# verification/crypto — verified crypto primitives (local)

Stainless-verified building blocks for ECDSA on secp256k1 / P-256, built on
`stainless.math.NonLinear` (witness-form BigInt lemmas). BigInt only, JVM only (no GenC).

| Module | Content |
| :--- | :--- |
| `NumberTheory.scala` | `extendedGcd` with divisibility witnesses, `gcdIsGreatest`, `modInverse` (+ completeness), `pow` spec, `modPow` (square-and-multiply), `crt` for two coprime moduli |
| `PrimeField.scala` | `FieldElem(v, p)` with the invariant `0 <= v < p`: `+ - * inverse /`, unary `-`, `of`; `Primes.isPrime` (definition, executable for small p) and coprimality; field laws (`FieldLaws`): neutral elements, commutativity, associativity, distributivity, additive and multiplicative inverses |
| `Curve.scala` | Short Weierstrass group law in affine coordinates: `CurveParams` (prime `p > 3`, non-singular), `ECPoint`, `isOnCurve` (residues of non-negative dividends: `a`, `b` enter as `a.mod(p)`, `b.mod(p)`), `neg`, `add`, `double`; closure of `add`/`double` proved (Groebner certificates as integer polynomial identities + quotient witnesses), `P + O = P`, `P + (-P) = O` (order-2 points included), `P + Q = Q + P` |
| `SqrtMod.scala` | `sqrtMod` — Tonelli–Shanks as a certifying algorithm: soundness proved, completeness on vectors |

## Rules

* Contracts never use `/` or `%` on a symbolic modulus; divisibility is stated with witness
  cofactors. `/` and `%` in bodies only on a non-negative dividend (or by a literal).
* `BigInt.mod` in a contract only on a dividend proved non-negative. Any-sign residues use
  `NonLinear.floorMod` (proved); the bridge `mod == floorMod` is proved for a non-negative dividend.
* Lemmas are `@ghost @opaque @inlineOnce` (the `@lemma` expansion; 0.10.2 has no `@lemma`) and are
  called from executable code through `ghost(...)`. Every recursion has `decreases`.
* Solver hygiene: anything Z3 should treat as an atom is `@opaque` (`isPrime`, `nonSingular`, `fcub`,
  `gap`, `red`, `slope`, `coefA`, `sameResidue`, ...) and unfolded only inside the lemma that needs it;
  polynomial identities take their composite quantities as parameters tied by `require`, so no caller
  ever substitutes a polynomial under a product (the source of every timeout met while writing PR 5).
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
| T3 | Associativity of the affine group law | PR 5 — **not used** by any proof; `CurveJvm` pins it on vector points | polynomial identity in a CAS plus PR 1 vectors | not used |
| T4 | Primality of the concrete `p`, `n` until PR 6 | PR 4–5: `isPrime(p)` is a precondition of `inverse`, `/` and of `CurveParams`; never assumed in code, the JVM runs do not check it | removed by the Pratt certificates of PR 6 | temporary (a precondition, not an axiom) |

No `assume`, `@extern` or unverified `@library` in this directory.
