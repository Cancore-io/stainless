#!/usr/bin/env python3
"""
Cryptographic Test-Vector Generator and Reference Oracle.
Designed for Stainless formal verification cross-validation (Test-Driven Verification).
Standard suites:
- secp256k1 (SECG SEC 2) and NIST P-256 / secp256r1 (FIPS 186-4)
- RFC 6979 (Deterministic ECDSA nonce generation, Appendix A.2.5)
- RFC 7748 (Curve25519 X25519, Section 6.1)
- RFC 8032 (Ed25519, Section 7.1)
- Extended Euclidean GCD with Bezout/divisibility witnesses
- Modular inverse, modpow and Tonelli-Shanks modular sqrt

Every generated value is either pinned to a published known-answer test (KAT)
or re-derived by the independent consumers (tests/test_oracle.py, the JVM suite).

Usage:
  oracle_gen.py          regenerate vectors/
  oracle_gen.py --check  fail if the committed vectors differ from a fresh run
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
    Returns (gcd, ka, kb, x, y) for a, b >= 0, not both zero,
    where a = ka * gcd, b = kb * gcd and ka * x + kb * y == 1
    (hence a * x + b * y == gcd).
    Matches the witness structure of MoreExtendedEuclidGCD.scala from epfl-lara/bolts.
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

def is_prime(n: int) -> bool:
    """Miller-Rabin with the first 12 prime bases (deterministic below 3.3e24)."""
    bases = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
    if n < 2:
        return False
    if n in bases:
        return True
    if any(n % b == 0 for b in bases):
        return False
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for b in bases:
        x = pow(b, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                break
        else:
            return False
    return True

def tonelli_shanks(n: int, p: int):
    """Solves r^2 = n (mod p) for prime p. Returns None if n is a non-residue."""
    n = n % p
    if n == 0:
        return 0
    if p == 2:
        return n
    if pow(n, (p - 1) // 2, p) != 1:
        return None

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
        # Find the least 0 < i < m such that t^(2^i) = 1
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
# 2. Weierstrass Elliptic Curve Core (affine, None = point at infinity)
# -----------------------------------------------------------------------------

class WeierstrassCurve:
    def __init__(self, name: str, p: int, a: int, b: int, gx: int, gy: int, n: int):
        self.name = name
        self.p = p
        self.a = a % p
        self.b = b % p
        self.g = (gx, gy)
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
                return None  # P + (-P) = O, includes doubling a point with y = 0
            inv = mod_inverse(2 * y1, self.p)
            lam = ((3 * x1 * x1 + self.a) * inv) % self.p
        else:
            inv = mod_inverse((x2 - x1) % self.p, self.p)
            lam = ((y2 - y1) * inv) % self.p

        x3 = (lam * lam - x1 - x2) % self.p
        y3 = (lam * (x1 - x3) - y1) % self.p
        return (x3, y3)

    def scalar_mult(self, k: int, pt):
        """Double-and-add scalar multiplication. k is NOT reduced: [n]G must come out as O."""
        if k < 0:
            raise ValueError("Negative scalar")
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
    a=-3,
    b=0x5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B,
    gx=0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296,
    gy=0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5,
    n=0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551,
)

# y^2 = x^3 - x over F_23: has the 2-torsion points (0,0), (1,0), (22,0), so the
# y = 0 doubling branch is reachable (it is not on the cofactor-1 curves above).
# n here is the order of G = (1, 0), which is 2.
TOY_P23 = WeierstrassCurve(name="toy_p23", p=23, a=-1, b=0, gx=1, gy=0, n=2)

# Published known answers, independent of this generator. scalar -> (x, y).
KAT_POINTS = {
    "secp256k1": {
        2: (0xC6047F9441ED7D6D3045406E95C07CD85C778E4B8CEF3CA7ABAC09B95C709EE5,
            0x1AE168FEA63DC339A3C58419466CEAEEF7F632653266D0E1236431A950CFE52A),
        3: (0xF9308A019258C31049344F85F89D5229B531C845836F99B08601F113BCE036F9,
            0x388F7B0F632DE8140FE337E62A37F3566500A99934C2231B6CB9FD7584B8E672),
    },
    "NIST_P256": {
        2: (0x7CF27B188D034F7E8A52380304B51AC3C08969E277F21B35A60B48FC47669978,
            0x07775510DB8ED040293D9AC69F7430DBBA7DADE63CE982299E04B79D227873D1),
        3: (0x5ECBE4D1A6330A44C8F7EF951D4BF165E6C6B721EFADA985FB41661BC6E7FD6C,
            0x8734640C4998FF7E374B06CE1A64A2ECD82AB036384FB83D9A79B127A27D5032),
    },
}

def pt_json(pt):
    """Point as JSON: null for infinity, otherwise lowercase hex without 0x."""
    if pt is None:
        return None
    return {"x": format(pt[0], "x"), "y": format(pt[1], "x")}

# -----------------------------------------------------------------------------
# 3. RFC 6979 Deterministic Nonce Generation (HMAC-SHA256)
# -----------------------------------------------------------------------------

def bits2int(b: bytes, qlen: int) -> int:
    """RFC 6979 Section 2.3.2: leftmost qlen bits of b as an integer."""
    x = int.from_bytes(b, "big")
    blen = len(b) * 8
    return x >> (blen - qlen) if blen > qlen else x

def rfc6979_nonce(priv_key: int, msg_hash: bytes, q: int) -> int:
    """RFC 6979 Section 3.2 HMAC_DRBG nonce generation."""
    qlen = q.bit_length()
    rlen = (qlen + 7) // 8
    x_bytes = priv_key.to_bytes(rlen, "big")
    h1 = (bits2int(msg_hash, qlen) % q).to_bytes(rlen, "big")  # bits2octets

    v = b"\x01" * 32
    k = b"\x00" * 32

    k = hmac.new(k, v + b"\x00" + x_bytes + h1, hashlib.sha256).digest()
    v = hmac.new(k, v, hashlib.sha256).digest()
    k = hmac.new(k, v + b"\x01" + x_bytes + h1, hashlib.sha256).digest()
    v = hmac.new(k, v, hashlib.sha256).digest()

    while True:
        t = b""
        while len(t) < rlen:
            v = hmac.new(k, v, hashlib.sha256).digest()
            t += v
        k_candidate = bits2int(t, qlen)
        if 1 <= k_candidate < q:
            return k_candidate
        k = hmac.new(k, v + b"\x00", hashlib.sha256).digest()
        v = hmac.new(k, v, hashlib.sha256).digest()

def ecdsa_sign(curve: WeierstrassCurve, priv: int, msg: bytes):
    """Deterministic ECDSA (no low-s normalisation, as in RFC 6979 Appendix A)."""
    h = hashlib.sha256(msg).digest()
    k = rfc6979_nonce(priv, h, curve.n)
    e = bits2int(h, curve.n.bit_length()) % curve.n
    r = curve.scalar_mult(k, curve.g)[0] % curve.n
    s = (mod_inverse(k, curve.n) * (e + priv * r)) % curve.n
    return h, k, r, s

# RFC 6979 A.2.5 (P-256, SHA-256) and the widely used secp256k1 vector
# (private key 1, "Satoshi Nakamoto"); only k is pinned for the latter.
RFC6979_KATS = [
    (NIST_P256, 0xC9AFA9D845BA75166B5C215767B1D6934E50C3DB36E89B127B8A622B120F6721, b"sample", {
        "k": 0xA6E3C57DD01ABE90086538398355DD4C3B17AA873382B0F24D6129493D8AAD60,
        "r": 0xEFD48B2AACB6A8FD1140DD9CD45E81D69D2C877B56AAF991C34D0EA84EAF3716,
        "s": 0xF7CB1C942D657C41D436C7A1B6E29F65F3E900DBB9AFF4064DC4AB2F843ACDA8,
    }),
    (NIST_P256, 0xC9AFA9D845BA75166B5C215767B1D6934E50C3DB36E89B127B8A622B120F6721, b"test", {
        "k": 0xD16B6AE827F17175E040871A1C7EC3500192C4C92677336EC2537ACAEE0008E0,
        "r": 0xF1ABB023518351CD71D881567B1EA663ED3EFCF6C5132B354F28D3B0B7D38367,
        "s": 0x019F4113742A2B14BD25926B49C649155F267E60D3814B4C0CC84250E46F0083,
    }),
    (SECP256K1, 1, b"Satoshi Nakamoto", {
        "k": 0x8F8A276C19F4149656B280621E358CCE24F5F52542772691EE69063B74F15D15,
    }),
]

# RFC 6979 A.2.5 public key U = xG for the P-256 test key.
RFC6979_P256_PUB = (0x60FED4BA255A9D31C961EB74C6356D68C049B8923B61FA6CE669622E60F29FB6,
                    0x7903FE1008B8BC99A41AE9E95628BC64F2F1B20C2D7E9F5177A3C294D4462299)

# -----------------------------------------------------------------------------
# 4. RFC 7748 (Curve25519 / X25519)
# -----------------------------------------------------------------------------

P25519 = 2**255 - 19
A24 = (486662 - 2) // 4

def cswap(swap: int, x_2: int, x_3: int) -> tuple:
    # No reduction here: x_2 ^ x_3 can exceed p, and reducing the mask breaks the swap.
    dummy = swap * (x_2 ^ x_3)
    x_2 ^= dummy
    x_3 ^= dummy
    return x_2, x_3

def decode_u(u_bytes: bytes) -> int:
    """RFC 7748 Section 5: mask bit 255, then reduce mod p."""
    return (int.from_bytes(u_bytes, "little") & ((1 << 255) - 1)) % P25519

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

def derived_scalar(seed: str, i: int, n: int) -> int:
    """Scalar in [1, n-1] from SHA-256: stable across Python versions, unlike random.randrange."""
    digest = hashlib.sha256(f"{seed}/{i}".encode()).digest()
    return int.from_bytes(digest, "big") % (n - 1) + 1

def generate_curve_vectors(curve: WeierstrassCurve, count: int, seed: str):
    g = curve.g
    for k, expected in KAT_POINTS[curve.name].items():
        assert curve.scalar_mult(k, g) == expected, f"{curve.name}: [{k}]G differs from the published KAT"

    scalars = [1, 2, 3, 4, 5, 7, 16, 31, 64, 127, 256, 1000, 65537,
               curve.n - 1, curve.n // 2, 0xDEADBEEF]
    scalars += [derived_scalar(seed, i, curve.n) for i in range(count)]

    vectors = []
    for k in scalars:
        pt = curve.scalar_mult(k, g)
        assert curve.is_on_curve(pt)
        vectors.append({"curve": curve.name, "op": "mul", "k": format(k, "x"), "result": pt_json(pt)})

    # Point additions P + Q, cross-checked against [k1 + k2]G
    pairs = [(13, 37)] + [(derived_scalar(seed + "/add-p", i, curve.n), derived_scalar(seed + "/add-q", i, curve.n))
                          for i in range(9)]
    for k1, k2 in pairs:
        p1, p2 = curve.scalar_mult(k1, g), curve.scalar_mult(k2, g)
        p_sum = curve.point_add(p1, p2)
        assert p_sum == curve.scalar_mult((k1 + k2) % curve.n, g), "Addition mismatch"
        vectors.append({"curve": curve.name, "op": "add",
                        "p": pt_json(p1), "q": pt_json(p2), "result": pt_json(p_sum)})
    return vectors

def generate_edge_cases():
    """Degenerate inputs as recomputable data: consumers re-derive every result."""
    results = []

    def mul(curve, name, k, expected):
        got = curve.scalar_mult(k, curve.g)
        assert got == expected, f"{curve.name}/{name}"
        results.append({"curve": curve.name, "name": name, "op": "mul",
                        "k": format(k, "x"), "result": pt_json(expected)})

    def add(curve, name, p, q, expected):
        got = curve.point_add(p, q)
        assert got == expected, f"{curve.name}/{name}"
        results.append({"curve": curve.name, "name": name, "op": "add",
                        "p": pt_json(p), "q": pt_json(q), "result": pt_json(expected)})

    for curve in [SECP256K1, NIST_P256]:
        g = curve.g
        neg_g = curve.point_neg(g)
        add(curve, "identity_P_plus_O", g, None, g)
        add(curve, "identity_O_plus_P", None, g, g)
        add(curve, "identity_O_plus_O", None, None, None)
        add(curve, "inverse_P_plus_negP", g, neg_g, None)
        add(curve, "doubling_G_plus_G", g, g, curve.scalar_mult(2, g))
        mul(curve, "order_mult_zero", 0, None)
        mul(curve, "order_mult_nG", curve.n, None)
        mul(curve, "order_mult_n_plus_1_G", curve.n + 1, g)
        mul(curve, "order_mult_n_minus_1_G_eq_negG", curve.n - 1, neg_g)

    # Vertical tangent: doubling a point with y = 0 must give O, not divide by zero.
    add(TOY_P23, "doubling_y_zero", TOY_P23.g, TOY_P23.g, None)
    mul(TOY_P23, "order_two_point", 2, None)
    return results

P224 = 2**224 - 2**96 + 1  # p - 1 = Q * 2^96: worst case for the Tonelli-Shanks loop

def generate_modular_vectors():
    """gcd/Bezout/inverse/modpow for every pair; Tonelli-Shanks when b is an odd prime.
    inv is present iff gcd == 1 and b > 1; modpow iff b > 0."""
    test_cases = [
        (17, 31), (256, 1009), (123456789, 987654321),
        (0xDEADBEEF, 0x100000007),
        (12, 18),  # non-coprime: no inverse
        (0, 5), (5, 0), (5, 1),  # extended_gcd base cases; inverse needs b > 1, modpow needs b > 0
        (SECP256K1.p - 1, SECP256K1.p),
        (3, SECP256K1.p),
        (12345, SECP256K1.n),
        (0x1fffffffffffffffffffffffffffffff, 0x3fffffffffffffffffffffffffffffff),
        (SECP256K1.g[0], SECP256K1.p),
        (pow(0xDEADBEEF, 2, P224), P224),      # residue, full loop with S = 96
        (11, P224),                             # non-residue
        (pow(0xCAFEBABE, 2, P25519), P25519),   # residue, p = 5 mod 8
        (2, P25519),                            # non-residue
        (pow(SECP256K1.g[1], 2, NIST_P256.p), NIST_P256.p),
    ]
    vectors = []
    for a, b in test_cases:
        gcd_val, ka, kb, x, y = extended_gcd(a, b)
        assert a * x + b * y == gcd_val and a == ka * gcd_val and b == kb * gcd_val
        inv_val = mod_inverse(a, b) if gcd_val == 1 and b > 1 else None
        b_is_prime = is_prime(b)
        sqrt_val = tonelli_shanks(a, b) if b_is_prime and b > 2 else None
        if sqrt_val is not None:
            assert (sqrt_val * sqrt_val - a) % b == 0
        vectors.append({
            "a": str(a),
            "b": str(b),
            "gcd": str(gcd_val),
            "ka": str(ka),
            "kb": str(kb),
            "x": str(x),
            "y": str(y),
            "inv": None if inv_val is None else str(inv_val),
            "modpow_65537": str(pow(a, 65537, b)) if b > 0 else None,
            "b_is_prime": b_is_prime,
            "sqrt": None if sqrt_val is None else str(sqrt_val),
        })
    # Both Tonelli-Shanks outcomes on the p = 1 mod 4 branch must be covered.
    ts = [(v["sqrt"] is None) for v in vectors if int(v["b"]) in (P224, P25519)]
    assert True in ts and False in ts
    return vectors

def generate_rfc6979_vectors():
    vectors = []
    for curve, priv, msg, kat in RFC6979_KATS:
        h, k, r, s = ecdsa_sign(curve, priv, msg)
        assert k == kat["k"], f"RFC 6979 nonce mismatch for {curve.name}/{msg!r}"
        assert "r" not in kat or (r, s) == (kat["r"], kat["s"]), f"RFC 6979 signature mismatch for {msg!r}"
        pub = curve.scalar_mult(priv, curve.g)
        if curve is NIST_P256:
            assert pub == RFC6979_P256_PUB
        vectors.append({
            "curve": curve.name,
            "private_key": format(priv, "x"),
            "public_key": pt_json(pub),
            "message": msg.decode("ascii"),
            "message_hash": h.hex(),
            "k": format(k, "x"),
            "r": format(r, "x"),
            "s": format(s, "x"),
        })
    return vectors

def generate_rfc7748_vectors():
    # Canonical RFC 7748 Section 6.1 Test Vector (Alice private x Bob public -> Shared Secret)
    alice_priv = bytes.fromhex("77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a")
    bob_pub = bytes.fromhex("de9edb7d7b7dc1b4d35b61c2ece435373f8343c85b78674dadfc7e146f882b4f")
    expected_shared = bytes.fromhex("4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742")

    s_int = int.from_bytes(alice_priv, "little")
    s_int &= ~7
    s_int &= ~(128 << (8 * 31))
    s_int |= 64 << (8 * 31)

    # The ladder never hits x_2 ^ x_3 >= p on this KAT, so pin the swap directly.
    assert cswap(1, P25519 - 1, 19) == (19, P25519 - 1) and cswap(0, 5, 7) == (5, 7)

    bob_u = decode_u(bob_pub)
    out_int = x25519(s_int, bob_u)
    out_bytes = out_int.to_bytes(32, "little")
    assert out_bytes == expected_shared, "RFC 7748 shared secret mismatch"

    # Also compute Alice's public key from base point 9
    alice_pub_bytes = x25519(s_int, 9).to_bytes(32, "little")
    assert alice_pub_bytes.hex() == "8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a"

    return [{
        "curve": "curve25519",
        "rfc": "RFC 7748 Section 6.1",
        "alice_private_hex_le": alice_priv.hex(),
        "alice_public_hex_le": alice_pub_bytes.hex(),
        "bob_public_hex_le": bob_pub.hex(),
        "shared_secret_hex_le": out_bytes.hex(),
    }]

def generate_rfc8032_vectors():
    p = P25519
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
    sk = bytes.fromhex("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60")
    h = hashlib.sha512(sk).digest()
    a = bytearray(h[:32])
    a[0] &= 248
    a[31] &= 127
    a[31] |= 64
    s = int.from_bytes(a, "little")
    ax, ay = ed_mult(s, (bx, by))
    pk_bytes = bytearray(ay.to_bytes(32, "little"))
    if ax % 2 == 1:
        pk_bytes[31] |= 0x80
    assert pk_bytes.hex() == "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"

    return [{
        "curve": "ed25519",
        "rfc": "RFC 8032 Section 7.1",
        "secret_key_hex": sk.hex(),
        "public_key_hex": pk_bytes.hex(),
        "public_key_x": format(ax, "x"),
        "public_key_y": format(ay, "x"),
        "scalar": format(s, "x"),
    }]

def generate_all():
    """File name -> JSON text, fully deterministic."""
    suites = {
        "secp256k1_vectors.json": generate_curve_vectors(SECP256K1, count=240, seed="secp256k1"),
        "nist_p256_vectors.json": generate_curve_vectors(NIST_P256, count=240, seed="NIST_P256"),
        "edge_cases_vectors.json": generate_edge_cases(),
        "modular_arithmetic_vectors.json": generate_modular_vectors(),
        "rfc6979_vectors.json": generate_rfc6979_vectors(),
        "rfc7748_vectors.json": generate_rfc7748_vectors(),
        "rfc8032_vectors.json": generate_rfc8032_vectors(),
    }
    return {name: json.dumps(data, indent=2) + "\n" for name, data in suites.items()}

def main():
    target_dir = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "vectors"))
    files = generate_all()

    if "--check" in sys.argv:
        stale = []
        for name, text in files.items():
            path = os.path.join(target_dir, name)
            if not os.path.exists(path) or open(path).read() != text:
                stale.append(name)
        if stale:
            sys.exit(f"Committed vectors are stale, rerun oracle_gen.py: {', '.join(stale)}")
        print(f"Committed vectors match the oracle ({len(files)} files).")
        return

    os.makedirs(target_dir, exist_ok=True)
    for name, text in files.items():
        with open(os.path.join(target_dir, name), "w") as f:
            f.write(text)
    print(f"Successfully generated all test vectors into: {target_dir}")

if __name__ == "__main__":
    main()
