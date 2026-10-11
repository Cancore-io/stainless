#!/usr/bin/env python3
"""
Test Suite for Cryptographic Test Vectors and Reference Oracle.
Validates all vectors in verification/crypto-oracle/vectors against mathematical invariants.
Can be executed standalone or via pytest/unittest.
"""

import json
import os
import unittest

VECTORS_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "vectors"))

class TestCryptoOracleVectors(unittest.TestCase):

    def test_secp256k1_vectors(self):
        path = os.path.join(VECTORS_DIR, "secp256k1_vectors.json")
        self.assertTrue(os.path.exists(path), f"Missing {path}")
        with open(path) as f:
            data = json.load(f)
        
        p = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
        for entry in data:
            self.assertEqual(entry["curve"], "secp256k1")
            pt = entry["result_point"]
            if not pt.get("is_infinity", False):
                x = int(pt["x_hex"], 16)
                y = int(pt["y_hex"], 16)
                # Curve equation: y^2 == x^3 + 7 (mod p)
                lhs = (y * y) % p
                rhs = (x * x * x + 7) % p
                self.assertEqual(lhs, rhs, f"Point not on secp256k1 curve: {entry}")

    def test_nist_p256_vectors(self):
        path = os.path.join(VECTORS_DIR, "nist_p256_vectors.json")
        self.assertTrue(os.path.exists(path), f"Missing {path}")
        with open(path) as f:
            data = json.load(f)
        
        p = 0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF
        a = p - 3
        b = 0x5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B
        for entry in data:
            self.assertEqual(entry["curve"], "NIST_P256")
            pt = entry["result_point"]
            if not pt.get("is_infinity", False):
                x = int(pt["x_hex"], 16)
                y = int(pt["y_hex"], 16)
                lhs = (y * y) % p
                rhs = (x * x * x + a * x + b) % p
                self.assertEqual(lhs, rhs, f"Point not on NIST P-256 curve: {entry}")

    def test_modular_arithmetic_vectors(self):
        path = os.path.join(VECTORS_DIR, "modular_arithmetic_vectors.json")
        self.assertTrue(os.path.exists(path), f"Missing {path}")
        with open(path) as f:
            data = json.load(f)

        for entry in data:
            a = int(entry["a_dec"])
            b = int(entry["b_dec"])
            gcd_val = int(entry["gcd_dec"])
            ka = int(entry["ka_dec"])
            kb = int(entry["kb_dec"])
            x = int(entry["x_dec"])
            y = int(entry["y_dec"])

            # 1. Divisibility witnesses
            self.assertEqual(a, ka * gcd_val)
            self.assertEqual(b, kb * gcd_val)

            # 2. Bezout identity
            self.assertEqual(a * x + b * y, gcd_val)

            # 3. Modular inverse
            if entry.get("inv_dec") is not None:
                inv_val = int(entry["inv_dec"])
                self.assertEqual((a * inv_val) % b, 1)

            # 4. Modpow
            if entry.get("modpow_exp_65537_dec") is not None:
                exp_res = int(entry["modpow_exp_65537_dec"])
                self.assertEqual(pow(a, 65537, b), exp_res)

            # 5. Tonelli-Shanks
            if entry.get("tonelli_shanks_sqrt_dec") is not None:
                sqrt_res = int(entry["tonelli_shanks_sqrt_dec"])
                self.assertEqual((sqrt_res * sqrt_res) % b, (a * a) % b)

    def test_edge_cases_vectors(self):
        path = os.path.join(VECTORS_DIR, "edge_cases_vectors.json")
        self.assertTrue(os.path.exists(path), f"Missing {path}")
        with open(path) as f:
            data = json.load(f)

        for curve_suite in data:
            for test in curve_suite["tests"]:
                self.assertTrue(test["passed"], f"Edge test failed: {test['name']} for {curve_suite['curve']}")

    def test_rfc6979_vectors(self):
        path = os.path.join(VECTORS_DIR, "rfc6979_vectors.json")
        self.assertTrue(os.path.exists(path), f"Missing {path}")
        with open(path) as f:
            data = json.load(f)

        for entry in data:
            k = int(entry["expected_nonce_k_hex"], 16)
            self.assertGreaterEqual(k, 1)

    def test_rfc7748_vectors(self):
        path = os.path.join(VECTORS_DIR, "rfc7748_vectors.json")
        self.assertTrue(os.path.exists(path), f"Missing {path}")
        with open(path) as f:
            data = json.load(f)

        self.assertEqual(len(data), 1)
        self.assertEqual(data[0]["shared_secret_hex_le"], "4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742")
        self.assertEqual(data[0]["alice_public_hex_le"], "8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a")

    def test_rfc8032_vectors(self):
        path = os.path.join(VECTORS_DIR, "rfc8032_vectors.json")
        self.assertTrue(os.path.exists(path), f"Missing {path}")
        with open(path) as f:
            data = json.load(f)

        self.assertEqual(len(data), 1)
        self.assertEqual(data[0]["public_key_hex"], "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a")

if __name__ == "__main__":
    unittest.main()
