#!/usr/bin/env python3

import os
import sys
import time
import signal
import hashlib
import hmac
import subprocess
import multiprocessing
from datetime import datetime
import calendar

# ================= CONFIG =================
WORDLIST_FILE = "./Wordlist/english.txt"
OUTPUT_PREFIX = "found_legacy_keys_"
BRAINFLAYER_BIN = "./brainflayer/brainflayer"
BLOOM_FILTER = "./040823BF.blf"
TABFILE = "./tablefile.tab"
ENTROPY_BYTES = 24

# ================= MT19937 =================
class MT19937:
    """Mersenne Twister 32-bit (sama dengan std::mt19937 C++)."""
    def __init__(self, seed):
        self.mt = [0] * 624
        self.index = 624
        self.mt[0] = seed & 0xffffffff
        for i in range(1, 624):
            self.mt[i] = (1812433253 * (self.mt[i-1] ^ (self.mt[i-1] >> 30)) + i) & 0xffffffff

    def twist(self):
        for i in range(624):
            y = (self.mt[i] & 0x80000000) | (self.mt[(i+1) % 624] & 0x7fffffff)
            self.mt[i] = self.mt[(i+397) % 624] ^ (y >> 1)
            if y & 1:
                self.mt[i] ^= 0x9908b0df
        self.index = 0

    def next(self):
        if self.index >= 624:
            self.twist()
        y = self.mt[self.index]
        y ^= (y >> 11)
        y ^= (y << 7) & 0x9d2c5680
        y ^= (y << 15) & 0xefc60000
        y ^= (y >> 18)
        self.index += 1
        return y & 0xffffffff

# ================= BIP39 & BIP32 =================
import coincurve  # untuk compressed public key

SECP256K1_ORDER = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

def load_wordlist(filename):
    with open(filename, 'r') as f:
        words = [line.strip() for line in f if line.strip()]
    if len(words) != 2048:
        raise ValueError("Wordlist harus berisi 2048 kata")
    return words

def generate_mnemonic_bip39(seed_val, wordlist):
    rng = MT19937(seed_val)
    entropy = bytearray(24)
    for i in range(0, 24, 4):
        r = rng.next()
        entropy[i] = r & 0xff
        entropy[i+1] = (r >> 8) & 0xff
        entropy[i+2] = (r >> 16) & 0xff
        entropy[i+3] = (r >> 24) & 0xff

    h = hashlib.sha256(entropy).digest()
    combined = entropy + h[:1]  # 25 byte

    total_bits = 24 * 8
    checksum_len = total_bits // 32   # = 6
    total_len_bits = total_bits + checksum_len  # = 198

    # Ambil bit dengan urutan MSB (sama seperti C++)
    bits = []
    for i in range(total_len_bits):
        byte_pos = i // 8
        bit_pos = 7 - (i % 8)
        bit = (combined[byte_pos] >> bit_pos) & 1
        bits.append(bit)

    # Kelompokkan 11 bit menjadi indeks kata
    mnemonic_words = []
    for i in range(0, total_len_bits, 11):
        idx = 0
        for j in range(11):
            idx = (idx << 1) | bits[i + j]
        mnemonic_words.append(wordlist[idx])
    return ' '.join(mnemonic_words)

def mnemonic_to_seed(mnemonic):
    return hashlib.pbkdf2_hmac('sha512', mnemonic.encode('utf-8'), b'mnemonic', 2048, dklen=64)

def hmac_sha512(key, data):
    return hmac.new(key, data, hashlib.sha512).digest()

def hd_master_key_from_seed(seed):
    I = hmac_sha512(b'Bitcoin seed', seed)
    return I[:32], I[32:]   # private key, chain code

def public_key_compress(private_key_bytes):
    pk = coincurve.PublicKey.from_secret(private_key_bytes)
    return pk.format(compressed=True)

def ckdpriv_fast(parent_key, parent_chain, index):
    hardened = index >= 0x80000000
    if hardened:
        data = b'\x00' + parent_key
    else:
        data = public_key_compress(parent_key)
    data += index.to_bytes(4, 'big')
    I = hmac_sha512(parent_chain, data)
    left = I[:32]
    right = I[32:]
    left_int = int.from_bytes(left, 'big')
    if left_int >= SECP256K1_ORDER:
        return None
    parent_int = int.from_bytes(parent_key, 'big')
    child_int = (left_int + parent_int) % SECP256K1_ORDER
    if child_int == 0:
        return None
    child_key = child_int.to_bytes(32, 'big')
    return child_key, right

# ================= WORKER =================
def worker_process(worker_id, start_ts, end_ts, step, wordlist, num_derivations, pipe_fd):
    """Proses worker: generate private keys dan kirim ke pipe."""
    stop_flag = False
    def handle_sigterm(signum, frame):
        nonlocal stop_flag
        stop_flag = True
    signal.signal(signal.SIGTERM, handle_sigterm)

    prog_file = f"/tmp/milksad_progress_{os.getpid()}.tmp"
    processed = 0

    # Jalur BIP44: m/44'/0'/0'/0/0..4
    H = 0x80000000
    path = [44 | H, 0 | H, 0 | H]  # hardened
    chain_external = 0

    ts = start_ts
    while ts <= end_ts and not stop_flag:
        # 1. Mnemonic dari timestamp
        mnemonic = generate_mnemonic_bip39(ts, wordlist)
        seed = mnemonic_to_seed(mnemonic)
        master_key, master_chain = hd_master_key_from_seed(seed)

        # Kirim master private key
        master_hex = master_key.hex()
        try:
            os.write(pipe_fd, (master_hex + '\n').encode())
        except BrokenPipeError:
            # brainflayer mati, hentikan worker
            break

        # 2. Turunkan ke m/44'/0'/0'
        key = master_key
        chain = master_chain
        valid = True
        for idx in path:
            res = ckdpriv_fast(key, chain, idx)
            if res is None:
                valid = False
                break
            key, chain = res
        if not valid:
            ts += step
            continue

        # 3. Chain eksternal (0)
        res = ckdpriv_fast(key, chain, chain_external)
        if res is None:
            ts += step
            continue
        key_change, chain_change = res

        # 4. Address index 0..num_derivations-1
        for i in range(num_derivations):
            res = ckdpriv_fast(key_change, chain_change, i)
            if res is None:
                continue
            child_key, _ = res
            child_hex = child_key.hex()
            try:
                os.write(pipe_fd, (child_hex + '\n').encode())
            except BrokenPipeError:
                stop_flag = True
                break
        if stop_flag:
            break

        processed += 1
        if processed % 100 == 0:
            with open(prog_file, 'w') as f:
                f.write(str(processed))
        ts += step

    # Tulis progress terakhir
    with open(prog_file, 'w') as f:
        f.write(str(processed))

# ================= MAIN =================
def date_range_to_timestamps(start_str, end_str):
    start_dt = datetime.strptime(start_str + " 00:00:00", "%Y-%m-%d %H:%M:%S")
    end_dt = datetime.strptime(end_str + " 23:59:59", "%Y-%m-%d %H:%M:%S")
    start_ts = int(calendar.timegm(start_dt.timetuple()))
    end_ts = int(calendar.timegm(end_dt.timetuple()))
    return start_ts, end_ts

def main():
    signal.signal(signal.SIGPIPE, signal.SIG_IGN)
    signal.signal(signal.SIGINT, lambda s, f: sys.exit(1))  # akan trigger KeyboardInterrupt

    # Periksa file yang dibutuhkan
    for f in [BRAINFLAYER_BIN, BLOOM_FILTER, TABFILE]:
        if not os.path.exists(f):
            print(f"File tidak ditemukan: {f}", file=sys.stderr)
            return 1

    try:
        wordlist = load_wordlist(WORDLIST_FILE)
    except Exception as e:
        print(f"Gagal load wordlist: {e}", file=sys.stderr)
        return 1

    start_str = input("Start Date YYYY-MM-DD: ").strip()
    end_str = input("End Date YYYY-MM-DD: ").strip()
    start_ts, end_ts = date_range_to_timestamps(start_str, end_str)
    total_timestamps = end_ts - start_ts + 1

    threads = int(input("Threads: ").strip())

    # Pipe untuk komunikasi worker -> brainflayer
    r_fd, w_fd = os.pipe()

    # Jalankan brainflayer
    logfile = OUTPUT_PREFIX + "brainflayer.log"
    brainflayer_proc = subprocess.Popen(
        [BRAINFLAYER_BIN, "-v", "-m", TABFILE, "-b", BLOOM_FILTER, "-t", "priv", "-x"],
        stdin=r_fd,
        stdout=open(logfile, 'w'),
        stderr=subprocess.STDOUT,
        pass_fds=(r_fd,)
    )
    os.close(r_fd)  # parent tidak perlu membaca

    # Fork worker
    workers = []
    for i in range(threads):
        p = multiprocessing.Process(
            target=worker_process,
            args=(i, start_ts + i, end_ts, threads, wordlist, 5, w_fd)
        )
        p.start()
        workers.append(p)

    # Parent tidak perlu menulis ke pipe
    os.close(w_fd)

    # Monitoring progress
    start_time = time.time()
    try:
        while True:
            time.sleep(2)
            alive = any(p.is_alive() for p in workers)
            if not alive:
                break

            total_processed = 0
            for p in workers:
                prog_file = f"/tmp/milksad_progress_{p.pid}.tmp"
                if os.path.exists(prog_file):
                    with open(prog_file, 'r') as f:
                        try:
                            val = int(f.read().strip())
                            total_processed += val
                        except:
                            pass
            elapsed = time.time() - start_time
            percent = total_processed / total_timestamps * 100
            rate = total_processed / elapsed if elapsed > 0 else 0
            eta = (total_timestamps - total_processed) / rate if rate > 0 else 0
            print(f"\rProgress: {total_processed}/{total_timestamps} ({percent:.2f}%) | "
                  f"Rate: {rate:.1f} ts/s | Elapsed: {elapsed:.0f}s | ETA: {eta:.0f}s   ",
                  end='', flush=True)
    except KeyboardInterrupt:
        print("\nInterrupt diterima, menghentikan proses...")
        for p in workers:
            p.terminate()
        brainflayer_proc.terminate()

    # Bersih-bersih
    for p in workers:
        p.join()
    brainflayer_proc.wait()

    # Hapus file progress
    for p in workers:
        prog_file = f"/tmp/milksad_progress_{p.pid}.tmp"
        try:
            os.unlink(prog_file)
        except:
            pass

    print(f"\nSelesai. Output brainflayer di {logfile}")

if __name__ == '__main__':
    main()