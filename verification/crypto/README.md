# verification/crypto — verified crypto primitives (local)

Stainless-verified building blocks for ECDSA on secp256k1 / P-256, built on
`stainless.math.NonLinear` (witness-form BigInt lemmas). BigInt only, JVM only (no GenC).

| Module | Content |
| :--- | :--- |
| `NumberTheory.scala` | `extendedGcd` with divisibility witnesses, `gcdIsGreatest`, `modInverse` (+ completeness), `pow` spec, `modPow` (square-and-multiply), `crt` for two coprime moduli |

## Rules

* Contracts never use `/` or `%` on a symbolic modulus; divisibility is stated with witness
  cofactors. `/` and `%` in bodies only on a non-negative dividend (or by a literal).
* `BigInt.mod` in a contract only on a dividend proved non-negative. Any-sign residues use
  `NonLinear.floorMod` (proved); the bridge `mod == floorMod` is proved for a non-negative dividend.
* Lemmas are `@ghost @opaque @inlineOnce` (the `@lemma` expansion; 0.10.2 has no `@lemma`) and are
  called from executable code through `ghost(...)`. Every recursion has `decreases`.
* `stainless.lang.StaticChecks._` turns `require`/`ensuring`/`assert` into no-ops on the JVM, so the
  executable code never evaluates a specification such as `pow`.

## Running

```bash
DAMLAUDIT_LOCK=/tmp/heavy.lock verification/crypto/verify.sh   # Stainless 0.10.2, smt-z3, --timeout=10, no cache
verification/crypto/run_jvm.sh                                  # executes the verified code against PR 1 vectors
```

`verify.sh` fails on any non-valid VC of the modules and on any `invalid/*Mutants.scala` whose
invalid VCs differ from its `.check` (`line:col;function;kind;invalid`). `run_jvm.sh` compiles the
same sources with the Scala compiler shipped in the 0.10.2 release (the library TASTy is a 3.10
nightly that stock Scala 3.9 cannot read) and cross-checks every result with `java.math.BigInteger`.

## Trusted base (SPEC §8)

Everything accepted without proof. An entry without a justification blocks the PR.

| ID | Fact | Where | Justification | Status |
| :--- | :--- | :--- | :--- | :--- |
| T1 | Hash functions (SHA-256/512, HMAC) | input `e` of ECDSA verify (PR 6b), oracle | FIPS 180-4; not part of the verified code | accepted |
| T2 | `x.mod(m)` vs. the Euclidean quotient for a **negative** `x` | not used | NumberTheory keeps every `mod` dividend non-negative and uses `floorMod` otherwise; the non-negative bridge is proved (`NonLinear.modIsFloorMod`) | not needed |
| T3 | Associativity of the affine group law | PR 5 | polynomial identity in a CAS plus PR 1 vectors | planned |
| T4 | Primality of the concrete `p`, `n` until PR 6 | PR 4–5 | removed by the Pratt certificates of PR 6 | temporary |

No `assume`, `@extern` or unverified `@library` in this directory.
