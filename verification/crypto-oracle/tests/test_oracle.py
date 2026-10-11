#!/usr/bin/env python3
"""
Test Suite for Cryptographic Test Vectors and Reference Oracle.
Validates the committed vectors in verification/crypto-oracle/vectors against
mathematical invariants, without importing the generator.
Elliptic-curve results are recomputed independently by the JVM suite.
Can be executed standalone or via pytest/unittest.
"""

import hashlib
import json
import math
import os
import unittest

VECTORS_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "vectors"))

# Curve parameters transcribed from SEC 2 / FIPS 186-4: (p, a, b, Gx, Gy, n)
CURVES = {
    "secp256k1": (
        0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F, 0, 7,
        0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798,
        0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8,
        0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141),
    "NIST_P256": (
        0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF, -3,
        0x5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B,
        0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296,
        0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5,
        0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551),
    "toy_p23": (23, -1, 0, 1, 0, 2),
}

EDGE_CASE_NAMES = {
    "identity_P_plus_O", "identity_O_plus_P", "identity_O_plus_O", "inverse_P_plus_negP",
    "doubling_G_plus_G", "order_mult_zero", "order_mult_nG", "order_mult_n_plus_1_G",
    "order_mult_n_minus_1_G_eq_negG",
}

def load(name):
    path = os.path.join(VECTORS_DIR, name)
    with open(path) as f:
        return json.load(f)

def point(js):
    return None if js is None else (int(js["x"], 16), int(js["y"], 16))

def probably_prime(n):
    """Fermat test on small bases: independent of the generator's b_is_prime flag."""
    bases = (2, 3, 5, 7, 11)
    return n in bases or (n > 11 and all(pow(base, n - 1, n) == 1 for base in bases))

def on_curve(curve, pt):
    if pt is None:
        return True
    p, a, b = CURVES[curve][:3]
    x, y = pt
    return 0 <= x < p and 0 <= y < p and (y * y - (x * x * x + a * x + b)) % p == 0

class TestCryptoOracleVectors(unittest.TestCase):

    def check_curve_file(self, name, curve):
        data = load(name)
        g = CURVES[curve][3:5]
        for entry in data:
            self.assertEqual(entry["curve"], curve)
            for key in ("p", "q", "result"):
                if key in entry:
                    self.assertTrue(on_curve(curve, point(entry[key])), f"Point not on {curve}: {entry}")
        # [1]G must be the standard generator
        one = [e for e in data if e["op"] == "mul" and int(e["k"], 16) == 1]
        self.assertEqual(len(one), 1)
        self.assertEqual(point(one[0]["result"]), g)
        return data

    def test_secp256k1_vectors(self):
        self.check_curve_file("secp256k1_vectors.json", "secp256k1")

    def test_nist_p256_vectors(self):
        self.check_curve_file("nist_p256_vectors.json", "NIST_P256")

    def test_vector_count_dod(self):
        # PR 1 DoD: >= 500 standardised vectors across all files
        total = sum(len(load(f)) for f in os.listdir(VECTORS_DIR) if f.endswith(".json"))
        self.assertGreaterEqual(total, 500)

    def test_modular_arithmetic_vectors(self):
        data = load("modular_arithmetic_vectors.json")
        sqrt_outcomes = set()
        for entry in data:
            a, b = int(entry["a"]), int(entry["b"])
            gcd_val, ka, kb = int(entry["gcd"]), int(entry["ka"]), int(entry["kb"])
            x, y = int(entry["x"]), int(entry["y"])

            self.assertEqual(gcd_val, math.gcd(a, b))
            # Divisibility witnesses and Bezout identity
            self.assertEqual(a, ka * gcd_val)
            self.assertEqual(b, kb * gcd_val)
            self.assertEqual(ka * x + kb * y, 1)
            self.assertEqual(a * x + b * y, gcd_val)

            if gcd_val == 1 and b > 1:
                inv_val = int(entry["inv"])
                self.assertTrue(0 <= inv_val < b)
                self.assertEqual((a * inv_val) % b, 1)
            else:
                self.assertIsNone(entry["inv"])

            if b > 0:
                self.assertEqual(pow(a, 65537, b), int(entry["modpow_65537"]))
            else:
                self.assertIsNone(entry["modpow_65537"])

            self.assertEqual(entry["b_is_prime"], probably_prime(b), entry)
            if entry["b_is_prime"]:
                if entry["sqrt"] is None:
                    # Euler's criterion: a is a non-residue
                    self.assertEqual(pow(a, (b - 1) // 2, b), b - 1)
                else:
                    r = int(entry["sqrt"])
                    self.assertEqual((r * r - a) % b, 0)
                if b % 4 == 1:
                    sqrt_outcomes.add(entry["sqrt"] is None)
            else:
                self.assertIsNone(entry["sqrt"])
        # The general (p = 1 mod 4) Tonelli-Shanks branch must see both outcomes
        self.assertEqual(sqrt_outcomes, {True, False})

    def test_edge_cases_vectors(self):
        data = load("edge_cases_vectors.json")
        for curve in ("secp256k1", "NIST_P256"):
            names = {e["name"] for e in data if e["curve"] == curve}
            self.assertEqual(names, EDGE_CASE_NAMES)
        self.assertIn("doubling_y_zero", {e["name"] for e in data if e["curve"] == "toy_p23"})

        for e in data:
            curve = e["curve"]
            p, n = CURVES[curve][0], CURVES[curve][5]
            g = CURVES[curve][3:5]
            res = point(e["result"])
            for key in ("p", "q", "result"):
                if key in e:
                    self.assertTrue(on_curve(curve, point(e[key])), e)
            if e["op"] == "add":
                lhs, rhs = point(e["p"]), point(e["q"])
                if lhs is None or rhs is None:
                    self.assertEqual(res, rhs if lhs is None else lhs)
                elif lhs[0] == rhs[0] and (lhs[1] + rhs[1]) % p == 0:
                    self.assertIsNone(res)
            else:
                k = int(e["k"], 16)
                if k % n == 0:
                    self.assertIsNone(res)
                elif k % n == 1:
                    self.assertEqual(res, g)
                elif k % n == n - 1:
                    self.assertEqual(res, (g[0], (-g[1]) % p))

    def test_rfc6979_vectors(self):
        data = load("rfc6979_vectors.json")
        self.assertEqual({e["curve"] for e in data}, {"NIST_P256", "secp256k1"})
        for e in data:
            n = CURVES[e["curve"]][5]
            h = hashlib.sha256(e["message"].encode("ascii")).digest()
            self.assertEqual(h.hex(), e["message_hash"])
            d, k, r, s = (int(e[f], 16) for f in ("private_key", "k", "r", "s"))
            self.assertTrue(1 <= k < n and 1 <= r < n and 1 <= s < n)
            self.assertTrue(on_curve(e["curve"], point(e["public_key"])))
            # ECDSA signing equation: s * k == e + d * r (mod n)
            self.assertEqual((s * k - (int.from_bytes(h, "big") + d * r)) % n, 0)

        # RFC 6979 A.2.5, P-256 / SHA-256 / "sample"
        sample = next(e for e in data if e["curve"] == "NIST_P256" and e["message"] == "sample")
        self.assertEqual(sample["k"], "a6e3c57dd01abe90086538398355dd4c3b17aa873382b0f24d6129493d8aad60")

    def test_rfc7748_vectors(self):
        data = load("rfc7748_vectors.json")
        self.assertEqual(len(data), 1)
        self.assertEqual(data[0]["shared_secret_hex_le"], "4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742")
        self.assertEqual(data[0]["alice_public_hex_le"], "8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a")

    def test_rfc8032_vectors(self):
        data = load("rfc8032_vectors.json")
        self.assertEqual(len(data), 1)
        self.assertEqual(data[0]["public_key_hex"], "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a")
        # Decoded coordinates must match the encoding and lie on -x^2 + y^2 = 1 + d x^2 y^2
        p = 2**255 - 19
        d = (-121665 * pow(121666, -1, p)) % p
        x, y = int(data[0]["public_key_x"], 16), int(data[0]["public_key_y"], 16)
        enc = int.from_bytes(bytes.fromhex(data[0]["public_key_hex"]), "little")
        self.assertEqual(y, enc & ((1 << 255) - 1))
        self.assertEqual(x & 1, enc >> 255)
        self.assertEqual((-x * x + y * y - 1 - d * x * x * y * y) % p, 0)

if __name__ == "__main__":
    unittest.main()
