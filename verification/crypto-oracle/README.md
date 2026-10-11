# Cryptographic Reference Oracle & Test-Vector Architecture for Stainless

> **Test-Driven Verification: checking specifications against published references before they reach the SMT solver**

---

## 1. Motivation

Stainless proves that code conforms to the specification *as written*. If the specification itself
is wrong (a flipped sign in the point-addition formula, the wrong modulus), the verifier will happily
prove an incorrect algorithm. The oracle closes that gap: every formula and algorithm that later goes
into Stainless is first checked against published references (SEC 2, FIPS 186-4, RFCs).

Constraints this module is built around:

* **NIA is undecidable for SMT.** `((a % m) * (b % m)) % m == (a * b) % m` with a symbolic `m`
  times out (Stainless 0.10.2 / nativez3, `--timeout=30`). Nonlinear facts in the formal layer will
  therefore be discharged by `@opaque @inlineOnce` lemmas (the `ListSpecs.scala` convention, PR #1749)
  and witness structures (`bolts/MoreExtendedEuclidGCD.scala`).
* **`%` in Stainless is the remainder with the sign of the dividend** (Z3 counterexample:
  `a = -19, m = 9`). With `a = -3` (P-256) normalisation is mandatory; `BigInt.mod` gives the
  non-negative residue.
* **JVM only.** GenC is unsuitable for 256-bit arithmetic; the runtime is `java.math.BigInteger`.

## 2. Three independent layers

| Layer | What it does | What it catches |
| :--- | :--- | :--- |
| `scripts/oracle_gen.py` | Generates the vectors and checks the implementation against published KATs (`[2]G`, `[3]G` on both curves; RFC 6979 A.2.5 `k/r/s/U`; RFC 7748 §6.1; RFC 8032 §7.1). `--check` compares the committed vectors with a fresh run. | Errors in an oracle formula or algorithm; hand-edited JSON. |
| `tests/test_oracle.py` | Checks the committed data against invariants without importing the generator: every point (inputs and results) is on the curve, `[1]G = G`, independent primality of the modulus, Bezout and witnesses, `gcd`, inverse, `modpow`, square root or Euler's criterion, the ECDSA equation `s·k ≡ e + d·r (mod n)`. | Corrupted or off-curve points, wrong number-theoretic answers. |
| `tests/CryptoOracleJvmTest.scala` | Its own affine arithmetic on `BigInteger`: left-to-right double-and-add (the oracle is right-to-left), recomputes every `mul`/`add` vector and edge case, checks ECDSA (`r = ([k]G).x mod n` plus full verification). | A point that is on the curve but computed incorrectly, and any disagreement between the two implementations. |

Each layer is backed by mutants: a broken doubling formula, a skipped Tonelli–Shanks loop, a bug in
the JVM addition, corrupted JSON points, off-curve edge-case inputs, a hidden primality flag, and a
`cswap` mask reduced mod p are all killed. A substituted on-curve point `-[k]G` is caught only by the
JVM layer and `--check`; this is by design.

## 3. Test vectors (`vectors/`)

Points are stored as `{"x": hex, "y": hex}` (lowercase hex, no `0x`); `null` denotes the point at
infinity $\mathcal{O}$. Scalars are hex, number-theoretic values are decimal strings. Everything
parses losslessly with `BigInt(str, radix)`.

| File | Vectors | Source of truth | Contents |
| :--- | ---: | :--- | :--- |
| [`secp256k1_vectors.json`](vectors/secp256k1_vectors.json) | 266 | SEC 2 and KATs `[2]G`, `[3]G` | 16 fixed and 240 seeded pseudo-random `[k]G`; 10 additions `P + Q` cross-checked against `[k1+k2]G`. |
| [`nist_p256_vectors.json`](vectors/nist_p256_vectors.json) | 266 | FIPS 186-4 and KATs `[2]G`, `[3]G` | Same for P-256 ($a = -3$). |
| [`edge_cases_vectors.json`](vectors/edge_cases_vectors.json) | 20 | Group law | $P+\mathcal{O}$, $\mathcal{O}+P$, $\mathcal{O}+\mathcal{O}$, $P+(-P)$, $G+G$, $[0]G$, $[n]G$, $[n+1]G$, $[n-1]G=-G$; doubling at $y=0$ on the toy curve $y^2=x^3-x$ over $\mathbb{F}_{23}$ (such a point is unreachable on cofactor-1 curves). |
| [`modular_arithmetic_vectors.json`](vectors/modular_arithmetic_vectors.json) | 18 | Invariants | `gcd` with witnesses `ka, kb, x, y`, including the base cases `(0,5)`, `(5,0)`, `(5,1)`. `inv` is present iff `gcd = 1` and `b > 1`; `modpow(65537)` iff `b > 0`. `b_is_prime` is real primality: Miller–Rabin in the generator, Fermat in Python, `isProbablePrime` on the JVM. Tonelli–Shanks for every odd prime `b`, including P-224 ($S = 96$) and $2^{255}-19$, on residues and non-residues. |
| [`rfc6979_vectors.json`](vectors/rfc6979_vectors.json) | 3 | RFC 6979 A.2.5 | P-256 `sample`/`test` (`k, r, s`); secp256k1 (key 1, `Satoshi Nakamoto`, only `k` pinned). |
| [`rfc7748_vectors.json`](vectors/rfc7748_vectors.json) | 1 | RFC 7748 §6.1 | X25519 Montgomery ladder: Alice's public key and the shared secret. |
| [`rfc8032_vectors.json`](vectors/rfc8032_vectors.json) | 1 | RFC 8032 §7.1 | Ed25519 test 1: public key derivation. |

575 vectors in total. Pseudo-random scalars are derived from SHA-256 (`seed/i`) rather than
`random`, so `--check` does not depend on the Python version.

## 4. Running

```bash
./verification/crypto-oracle/run_all.sh                       # drift check, Python, JVM
python3 verification/crypto-oracle/scripts/oracle_gen.py      # regenerate after changing the oracle
python3 verification/crypto-oracle/tests/test_oracle.py
scala verification/crypto-oracle/tests/CryptoOracleJvmTest.scala -- verification/crypto-oracle/vectors
```

`run_all.sh` works from any directory and never overwrites the vectors: on a mismatch it fails and
asks for an explicit regeneration, so every change to the vectors shows up in the diff. The JVM
runner takes the vectors directory as an argument and never guesses it from the current directory.

## 5. Known limits

* RFC 6979: three branches are not covered by a KAT — `bits2octets` (`mod q`, since `H(m) < q`),
  the HMAC_DRBG retry when `k ∉ [1, q-1]`, and `bits2int` with `blen < qlen`. Mutants in them
  survive. They are closed by the P-192 and P-521 vectors from RFC 6979 A.2.x.
* The X25519 `cswap` never sees `x_2 ^ x_3 ≥ p` on the KAT, so it is pinned by a direct check in
  the generator (the "mask reduced mod p" regression is killed).
* Ed25519 and X25519 are covered by one KAT each, and the JVM layer does not recompute them. This
  is enough until these curves are brought into Stainless.
* Hashing (SHA-256/512, HMAC) comes from `hashlib` and is not verified; it is part of the trusted base.

## 6. Next steps

* **Modular arithmetic lemmas:** `ModArithLemmas` (`@opaque @inlineOnce`) — `modAdd`, `modMul`,
  `modAssoc` in witness form.
* **Number theory core:** `extendedGcd` with witnesses `ka, kb`, `modInverse`, `modPow`, CRT; the
  vectors in `modular_arithmetic_vectors.json` become their KATs.
* **Prime fields:** `FieldElem` over $GF(p)$ and Tonelli–Shanks (the root is checked before it is returned).
