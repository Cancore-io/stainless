#!/usr/bin/env python3
"""
Cryptographic Test-Vector Generator and Reference Oracle.
Designed for Stainless formal verification cross-validation (Test-Driven Verification).
Standard suites:
- secp256k1 (Bitcoin/Ethereum)
- NIST P-256 / secp256r1
- RFC 6979 (Deterministic ECDSA Nonce generation)
- RFC 7748 (Curve25519 X25519)
- RFC 8032 (Ed25519 EdDSA)
- Extended Euclidean GCD & Bezout witnesses
- Modular arithmetic & Tonelli-Shanks modular sqrt
"""

import hashlib
import hmac
import json
import os
import sys

# -----------------------------------------------------------------------------
# 1. Number Theoretic Core
# -----------------------------------------------------------------------------

def extended_gcd(a: int, b: int):
    """
    Returns (gcd, ka, kb, x, y)
    where a = ka * gcd, b = kb * gcd
    and ka * x + kb * y == 1 (or a * x + b * y == gcd)
    Matches MoreExtendedEuclidGCD.scala structure from epfl-lara/bolts.
    """
    if b == 0:
        return (a, 1, 0, 1, 0)
    
    r_gcd, r_ka, r_kb, r_x, r_y = extended_gcd(b, a % b)
    ka = r_ka * (a // b) + r_kb
    kb = r_ka
    x = r_y
    y = r_x - (a // b) * r_y
    return (r_gcd, ka, kb, x, y)

def mod_inverse(a: int, m: int) -> int:
    """Computes modular inverse a^-1 mod m using Extended Euclidean Algorithm."""
    if m <= 1:
        raise ValueError("Modulus must be > 1")
    a = a % m
    gcd_val, _, _, x, _ = extended_gcd(a, m)
    if gcd_val != 1:
        raise ValueError(f"Inverse does not exist: gcd({a}, {m}) = {gcd_val}")
    return x % m

def tonelli_shanks(n: int, p: int):
    """Solves r^2 = n (mod p) for prime p. Returns None if no QR."""
    n = n % p
    if n == 0:
        return 0
    if p == 2:
        return n
    if pow(n, (p - 1) // 2, p) != 1:
        return None # Not a quadratic residue
    
    # Fast path for p = 3 mod 4
    if p % 4 == 3:
        return pow(n, (p + 1) // 4, p)
    
    # Factor p - 1 = Q * 2^S with Q odd
    q = p - 1
    s = 0
    while q % 2 == 0:
        q //= 2
        s += 1
    
    # Find non-residue z
    z = 2
    while pow(z, (p - 1) // 2, p) != p - 1:
        z += 1
    
    m = s
    c = pow(z, q, p)
    t = pow(n, q, p)
    r = pow(n, (q + 1) // 2, p)
    
    while t != 1:
        # Find lowest i such that t^(2^i) = 1
        t2i = t
        i = 0
        for i in range(1, m):
            t2i = pow(t2i, 2, p)
            if t2i == 1:
                break
        b = pow(c, 1 << (m - i - 1), p)
        m = i
        c = (b * b) % p
        t = (t * c) % p
        r = (r * b) % p
        
    return r

# -----------------------------------------------------------------------------
# 2. Weierstrass Elliptic Curve Core
# -----------------------------------------------------------------------------

class WeierstrassCurve:
    def __init__(self, name: str, p: int, a: int, b: int, gx: int, gy: int, n: int):
        self.name = name
        self.p = p
        self.a = a % p
        self.b = b % p
        self.gx = gx
        self.gy = gy
        self.n = n

    def is_on_curve(self, pt):
        if pt is None:
            return True
        x, y = pt
        if not (0 <= x < self.p and 0 <= y < self.p):
            return False
        return (y * y) % self.p == (x * x * x + self.a * x + self.b) % self.p

    def point_neg(self, pt):
        if pt is None:
            return None
        x, y = pt
        return (x, (-y) % self.p)

    def point_add(self, p1, p2):
        if p1 is None:
            return p2
        if p2 is None:
            return p1
        
        x1, y1 = p1
        x2, y2 = p2

        if x1 == x2:
            if (y1 + y2) % self.p == 0:
                return None # P + (-P) = O
            # Point doubling
            inv = mod_inverse(2 * y1, self.p)
            lam = ((3 * x1 * x1 + self.a) * inv) % self.p
        else:
            inv = mod_inverse((x2 - x1) % self.p, self.p)
            lam = ((y2 - y1) * inv) % self.p

        x3 = (lam * lam - x1 - x2) % self.p
        y3 = (lam * (x1 - x3) - y1) % self.p
        return (x3, y3)

    def scalar_mult(self, k: int, pt):
        """Double-and-add scalar multiplication."""
        k = k % self.n if self.n else k
        if k == 0 or pt is None:
            return None
        
        res = None
        addend = pt
        while k > 0:
            if k & 1:
                res = self.point_add(res, addend)
            addend = self.point_add(addend, addend)
            k >>= 1
        return res

SECP256K1 = WeierstrassCurve(
    name="secp256k1",
    p=0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F,
    a=0,
    b=7,
    gx=0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798,
    gy=0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8,
    n=0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141,
)

NIST_P256 = WeierstrassCurve(
    name="NIST_P256",
    p=0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF,
    a=0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFC, # p - 3
    b=0x5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B,
    gx=0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296,
    gy=0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5,
    n=0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551,
)

# -----------------------------------------------------------------------------
# 3. RFC 6979 Deterministic Nonce Generation
# -----------------------------------------------------------------------------

def rfc6979_nonce(priv_key: int, msg_hash: bytes, q: int) -> int:
    """RFC 6979 Section 3.2 HMAC_DRBG nonce generation."""
    q_len = (q.bit_length() + 7) // 8
    x_bytes = priv_key.to_bytes(q_len, 'big')
    h1 = msg_hash[:q_len] if len(msg_hash) >= q_len else msg_hash.rjust(q_len, b'\x00')
    
    v = b'\x01' * 32
    k = b'\x00' * 32
    
    k = hmac.new(k, v + b'\x00' + x_bytes + h1, hashlib.sha256).digest()
    v = hmac.new(k, v, hashlib.sha256).digest()
    k = hmac.new(k, v + b'\x01' + x_bytes + h1, hashlib.sha256).digest()
    v = hmac.new(k, v, hashlib.sha256).digest()
    
    while True:
        t = b''
        while len(t) < q_len:
            v = hmac.new(k, v, hashlib.sha256).digest()
            t += v
        k_candidate = int.from_bytes(t[:q_len], 'big')
        if 1 <= k_candidate < q:
            return k_candidate
        k = hmac.new(k, v + b'\x00', hashlib.sha256).digest()
        v = hmac.new(k, v, hashlib.sha256).digest()

# -----------------------------------------------------------------------------
# 4. RFC 7748 (Curve25519 / X25519)
# -----------------------------------------------------------------------------

P25519 = 2**255 - 19
A24 = (486662 - 2) // 4

def cswap(swap: int, x_2: int, x_3: int) -> tuple:
    dummy = swap * ((x_2 ^ x_3) % P25519)
    x_2 = (x_2 ^ dummy) % P25519
    x_3 = (x_3 ^ dummy) % P25519
    return x_2, x_3

def x25519(k_scalar: int, u_coord: int) -> int:
    """Montgomery ladder for X25519 per RFC 7748."""
    x_1 = u_coord
    x_2 = 1
    z_2 = 0
    x_3 = u_coord
    z_3 = 1
    swap = 0

    for t in range(254, -1, -1):
        k_t = (k_scalar >> t) & 1
        swap ^= k_t
        x_2, x_3 = cswap(swap, x_2, x_3)
        z_2, z_3 = cswap(swap, z_2, z_3)
        swap = k_t

        A = (x_2 + z_2) % P25519
        AA = (A * A) % P25519
        B = (x_2 - z_2) % P25519
        BB = (B * B) % P25519
        E = (AA - BB) % P25519
        C = (x_3 + z_3) % P25519
        D = (x_3 - z_3) % P25519
        DA = (D * A) % P25519
        CB = (C * B) % P25519
        x_3 = ((DA + CB) ** 2) % P25519
        z_3 = (x_1 * ((DA - CB) ** 2)) % P25519
        x_2 = (AA * BB) % P25519
        z_2 = (E * (AA + A24 * E)) % P25519

    x_2, x_3 = cswap(swap, x_2, x_3)
    z_2, z_3 = cswap(swap, z_2, z_3)
    return (x_2 * mod_inverse(z_2, P25519)) % P25519

# -----------------------------------------------------------------------------
# 5. Generator Orchestration
# -----------------------------------------------------------------------------

def generate_curve_vectors(curve: WeierstrassCurve, count: int = 50):
    g = (curve.gx, curve.gy)
    vectors = []
    
    # Standard scalar multiples
    scalars = [1, 2, 3, 4, 5, 7, 16, 31, 64, 127, 256, 1000, 65537,
               curve.n - 1, (curve.n // 2), 0xDEADBEEF]
    for s in scalars:
        pt = curve.scalar_mult(s, g)
        vectors.append({
            "curve": curve.name,
            "scalar_hex": hex(s),
            "scalar_dec": str(s),
            "result_point": {
                "is_infinity": pt is None,
                "x_hex": hex(pt[0]) if pt else None,
                "y_hex": hex(pt[1]) if pt else None,
                "x_dec": str(pt[0]) if pt else None,
                "y_dec": str(pt[1]) if pt else None,
            },
            "is_on_curve": curve.is_on_curve(pt)
        })
    
    # Point additions
    p1 = curve.scalar_mult(13, g)
    p2 = curve.scalar_mult(37, g)
    p_sum = curve.point_add(p1, p2)
    p_expected = curve.scalar_mult(50, g)
    assert p_sum == p_expected, "Addition mismatch"
    
    vectors.append({
        "curve": curve.name,
        "operation": "add",
        "p1_scalar": 13,
        "p2_scalar": 37,
        "expected_scalar": 50,
        "result_point": {
            "x_hex": hex(p_sum[0]),
            "y_hex": hex(p_sum[1]),
        },
        "is_on_curve": curve.is_on_curve(p_sum)
    })
    
    return vectors

def generate_edge_cases():
    results = []
    for curve in [SECP256K1, NIST_P256]:
        g = (curve.gx, curve.gy)
        # 1. Identity with Infinity: G + O = G
        p_inf = None
        add_inf = curve.point_add(g, p_inf)
        assert add_inf == g
        
        # 2. Inverses: G + (-G) = O
        neg_g = curve.point_neg(g)
        add_neg = curve.point_add(g, neg_g)
        assert add_neg is None
        
        # 3. Order cycle: [n]G = O
        pt_n = curve.scalar_mult(curve.n, g)
        assert pt_n is None
        
        # 4. [n+1]G = G
        pt_n_plus_1 = curve.scalar_mult(curve.n + 1, g)
        assert pt_n_plus_1 == g

        # 5. [0]G = O
        pt_zero = curve.scalar_mult(0, g)
        assert pt_zero is None

        # 6. [n-1]G = -G
        pt_n_minus_1 = curve.scalar_mult(curve.n - 1, g)
        assert pt_n_minus_1 == neg_g

        # 7. Doubling consistency: G + G == [2]G
        two_g = curve.scalar_mult(2, g)
        add_g_g = curve.point_add(g, g)
        assert add_g_g == two_g
        
        results.append({
            "curve": curve.name,
            "tests": [
                {"name": "identity_P_plus_O", "passed": add_inf == g},
                {"name": "inverse_P_plus_negP", "passed": add_neg is None},
                {"name": "order_mult_nG", "passed": pt_n is None},
                {"name": "order_mult_n_plus_1_G", "passed": pt_n_plus_1 == g},
                {"name": "order_mult_zero", "passed": pt_zero is None},
                {"name": "order_mult_n_minus_1_G_eq_negG", "passed": pt_n_minus_1 == neg_g},
                {"name": "doubling_consistency_G_plus_G", "passed": add_g_g == two_g},
            ]
        })
    return results

def generate_modular_vectors():
    vectors = []
    test_cases = [
        (17, 31), (256, 1009), (123456789, 987654321),
        (0xDEADBEEF, 0x100000007),
        (SECP256K1.p - 1, SECP256K1.p),
        (3, SECP256K1.p),
        (12345, SECP256K1.n),
        (0x1fffffffffffffffffffffffffffffff, 0x3fffffffffffffffffffffffffffffff),
        (0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798, SECP256K1.p)
    ]
    for a, b in test_cases:
        gcd_val, ka, kb, x, y = extended_gcd(a, b)
        bezout_holds = (a * x + b * y == gcd_val)
        inv_val = None
        if gcd_val == 1 and b > 1:
            inv_val = mod_inverse(a, b)
            inv_holds = ((a * inv_val) % b == 1)
        else:
            inv_holds = None
        
        # Test modpow: (a^65537) mod b
        exp = 65537
        modpow_res = pow(a, exp, b) if b > 1 else None

        # Test Tonelli-Shanks if b is prime (SECP256K1.p) and a is QR
        sqrt_val = None
        if b == SECP256K1.p:
            y2 = (a * a) % b
            sqrt_val = tonelli_shanks(y2, b)
        
        vectors.append({
            "a_dec": str(a),
            "b_dec": str(b),
            "gcd_dec": str(gcd_val),
            "ka_dec": str(ka),
            "kb_dec": str(kb),
            "x_dec": str(x),
            "y_dec": str(y),
            "bezout_holds": bezout_holds,
            "inv_dec": str(inv_val) if inv_val is not None else None,
            "inv_holds": inv_holds,
            "modpow_exp_65537_dec": str(modpow_res) if modpow_res is not None else None,
            "tonelli_shanks_sqrt_dec": str(sqrt_val) if sqrt_val is not None else None
        })
    return vectors

def generate_rfc6979_vectors():
    vectors = []
    # Test vector with secp256k1
    priv = 0xC9AFA9D845BA75166B5C215767B1D6934E50C3DB36E89B127B8A622B120F6721
    msg = b"sample"
    h = hashlib.sha256(msg).digest()
    k = rfc6979_nonce(priv, h, SECP256K1.n)
    vectors.append({
        "curve": "secp256k1",
        "private_key_hex": hex(priv),
        "message": msg.decode('ascii'),
        "message_hash_hex": h.hex(),
        "expected_nonce_k_hex": hex(k),
        "expected_nonce_k_dec": str(k),
    })
    return vectors

def generate_rfc7748_vectors():
    # Canonical RFC 7748 Section 6.1 Test Vector (Alice private x Bob public -> Shared Secret)
    alice_priv = bytes.fromhex('77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a')
    bob_pub = bytes.fromhex('de9edb7d7b7dc1b4d35b61c2ece435373f8343c85b78674dadfc7e146f882b4f')
    expected_shared = bytes.fromhex('4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742')

    s_int = int.from_bytes(alice_priv, 'little')
    s_int &= ~7
    s_int &= ~(128 << (8 * 31))
    s_int |= 64 << (8 * 31)

    bob_u = int.from_bytes(bob_pub, 'little') % P25519
    out_int = x25519(s_int, bob_u)
    out_bytes = out_int.to_bytes(32, 'little')
    assert out_bytes == expected_shared, "RFC 7748 shared secret mismatch"

    # Also compute Alice's public key from base point 9
    alice_pub_int = x25519(s_int, 9)
    alice_pub_bytes = alice_pub_int.to_bytes(32, 'little')
    assert alice_pub_bytes.hex() == '8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a'

    return [{
        "curve": "curve25519",
        "rfc": "RFC 7748 Section 6.1",
        "alice_private_hex_le": alice_priv.hex(),
        "alice_public_hex_le": alice_pub_bytes.hex(),
        "bob_public_hex_le": bob_pub.hex(),
        "shared_secret_hex_le": out_bytes.hex(),
        "bob_u_dec": str(bob_u),
        "shared_dec": str(out_int),
    }]

def generate_rfc8032_vectors():
    p = 2**255 - 19
    d = (-121665 * mod_inverse(121666, p)) % p
    bx = 0x216936d3cd6e53fec0a4e231fdd6dc5c692cc7609525a7b2c9562d608f25d51a
    by = 0x6666666666666666666666666666666666666666666666666666666666666658

    def ed_add(p1, p2):
        x1, y1 = p1
        x2, y2 = p2
        x3 = (x1 * y2 + y1 * x2) * mod_inverse(1 + d * x1 * x2 * y1 * y2, p) % p
        y3 = (y1 * y2 + x1 * x2) * mod_inverse(1 - d * x1 * x2 * y1 * y2, p) % p
        return (x3, y3)

    def ed_mult(k, pt):
        res = (0, 1)
        addend = pt
        while k > 0:
            if k & 1:
                res = ed_add(res, addend)
            addend = ed_add(addend, addend)
            k >>= 1
        return res

    # RFC 8032 Section 7.1 Test Vector 1
    sk = bytes.fromhex('9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60')
    h = hashlib.sha512(sk).digest()
    a = bytearray(h[:32])
    a[0] &= 248
    a[31] &= 127
    a[31] |= 64
    s = int.from_bytes(a, 'little')
    ax, ay = ed_mult(s, (bx, by))
    pk_bytes = bytearray(ay.to_bytes(32, 'little'))
    if ax % 2 == 1:
        pk_bytes[31] |= 0x80

    return [{
        "curve": "ed25519",
        "rfc": "RFC 8032 Section 7.1",
        "secret_key_hex": sk.hex(),
        "public_key_hex": pk_bytes.hex(),
        "public_key_x_dec": str(ax),
        "public_key_y_dec": str(ay),
        "scalar_dec": str(s),
    }]

def main():
    target_dir = os.path.join(os.path.dirname(__file__), "..", "vectors")
    os.makedirs(target_dir, exist_ok=True)
    
    secp = generate_curve_vectors(SECP256K1)
    with open(os.path.join(target_dir, "secp256k1_vectors.json"), "w") as f:
        json.dump(secp, f, indent=2)
        
    p256 = generate_curve_vectors(NIST_P256)
    with open(os.path.join(target_dir, "nist_p256_vectors.json"), "w") as f:
        json.dump(p256, f, indent=2)
        
    edges = generate_edge_cases()
    with open(os.path.join(target_dir, "edge_cases_vectors.json"), "w") as f:
        json.dump(edges, f, indent=2)
        
    mod_vecs = generate_modular_vectors()
    with open(os.path.join(target_dir, "modular_arithmetic_vectors.json"), "w") as f:
        json.dump(mod_vecs, f, indent=2)
        
    rfc6979 = generate_rfc6979_vectors()
    with open(os.path.join(target_dir, "rfc6979_vectors.json"), "w") as f:
        json.dump(rfc6979, f, indent=2)
        
    rfc7748 = generate_rfc7748_vectors()
    with open(os.path.join(target_dir, "rfc7748_vectors.json"), "w") as f:
        json.dump(rfc7748, f, indent=2)

    rfc8032 = generate_rfc8032_vectors()
    with open(os.path.join(target_dir, "rfc8032_vectors.json"), "w") as f:
        json.dump(rfc8032, f, indent=2)
        
    print(f"Successfully generated all test vectors into: {os.path.abspath(target_dir)}")

if __name__ == "__main__":
    main()
