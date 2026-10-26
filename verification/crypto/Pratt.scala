package crypto

import stainless.lang.{ghost => ghostExpr, _}
import stainless.lang.StaticChecks._
import stainless.annotation._
import stainless.collection._
import crypto.NumberTheory._

/** q^e is a factor of p - 1 with q * cofactor == p - 1 (a divisibility witness, no `/`). */
case class PrattFactor(q: BigInt, e: BigInt, cofactor: BigInt)

/** One Lucas step: a has order p - 1 modulo p, with p - 1 == prod q^e. */
case class PrattStep(p: BigInt, a: BigInt, factors: List[PrattFactor])

/**
 * Pratt primality certificates (SPEC.md §4 PR 6): a list of Lucas steps in
 * dependency order, each certifying its p from primes certified before it
 * (2 is given). The checker is verified (termination, safety); its soundness
 * rests on Lucas's theorem, TCB T5 (`lucas`). That the concrete curve
 * certificates check is TCB T6 (`curveCertsChecked`): an evaluation of this
 * very checker on the JVM, which Stainless cannot do symbolically at 256 bits.
 */
object Pratt {

  def product(fs: List[PrattFactor]): BigInt = {
    decreases(fs)
    fs match {
      case Nil()      => BigInt(1)
      case Cons(f, t) => if (f.e >= 0) pow(f.q, f.e) * product(t) else BigInt(0)
    }
  }

  /** Every factor: q certified before, e >= 1, q * cofactor == p - 1 and a^cofactor != 1 (mod p). */
  def factorsOk(p: BigInt, a: BigInt, fs: List[PrattFactor], known: List[BigInt]): Boolean = {
    require(p > 2 && 0 < a && a < p)
    decreases(fs)
    fs match {
      case Nil() => true
      case Cons(f, t) =>
        known.contains(f.q) && f.e >= 1 && f.cofactor >= 0 && f.q * f.cofactor == p - 1 &&
          modPow(a, f.cofactor, p) != BigInt(1) && factorsOk(p, a, t, known)
    }
  }

  def stepOk(s: PrattStep, known: List[BigInt]): Boolean =
    s.p > 2 && 0 < s.a && s.a < s.p && s.factors.nonEmpty && product(s.factors) == s.p - 1 &&
      modPow(s.a, s.p - 1, s.p) == BigInt(1) && factorsOk(s.p, s.a, s.factors, known)

  def checkSteps(steps: List[PrattStep], known: List[BigInt]): Boolean = {
    decreases(steps)
    steps match {
      case Nil()      => true
      case Cons(s, t) => stepOk(s, known) && checkSteps(t, s.p :: known)
    }
  }

  /** The certificate checks and its last step is n. */
  def certifies(steps: List[PrattStep], n: BigInt): Boolean =
    steps.nonEmpty && steps.last.p == n && checkSteps(steps, List(BigInt(2)))

  // ──────────────────────────────────────────────────────────────────────────
  // Soundness
  // ──────────────────────────────────────────────────────────────────────────

  /**
   * TCB T5 — Lucas's primality theorem (Lucas 1876; Pratt 1975): if a^(p-1) == 1 (mod p) and
   * a^((p-1)/q) != 1 (mod p) for every prime q dividing p - 1, then p is prime. stepOk lists
   * primes q whose powers multiply to p - 1, so every prime divisor of p - 1 is listed.
   * Formally proved in Lean 4 Mathlib (`lucas_primality`, Mathlib/NumberTheory/LucasPrimality.lean);
   * not proved in Stainless (needs the order of a unit and a counting argument over Z_p).
   */
  @extern @ghost
  def lucas(s: PrattStep, known: List[BigInt]): Unit = {
    require(known.forall(q => Primes.isPrime(q)) && stepOk(s, known))
  }.ensuring(_ => Primes.isPrime(s.p))

  @ghost @opaque @inlineOnce
  def twoIsPrime(): Unit = {
    unfold(Primes.isPrime(BigInt(2)))
  }.ensuring(_ => Primes.isPrime(BigInt(2)))

  @ghost @opaque @inlineOnce
  def checkStepsSound(steps: List[PrattStep], known: List[BigInt]): Unit = {
    require(known.forall(q => Primes.isPrime(q)) && checkSteps(steps, known))
    decreases(steps)
    steps match {
      case Nil() => ()
      case Cons(s, t) =>
        lucas(s, known)
        checkStepsSound(t, s.p :: known)
    }
  }.ensuring(_ => steps.forall(s => Primes.isPrime(s.p)))

  @ghost @opaque @inlineOnce
  def lastOfForall(steps: List[PrattStep]): Unit = {
    require(steps.nonEmpty && steps.forall(s => Primes.isPrime(s.p)))
    decreases(steps)
    steps match {
      case Cons(_, t) => if (t.nonEmpty) lastOfForall(t)
    }
  }.ensuring(_ => Primes.isPrime(steps.last.p))

  /** A checked certificate proves primality (modulo T5). */
  @ghost @opaque @inlineOnce
  def certifiesSound(steps: List[PrattStep], n: BigInt): Unit = {
    require(certifies(steps, n))
    twoIsPrime()
    checkStepsSound(steps, List(BigInt(2)))
    lastOfForall(steps)
  }.ensuring(_ => Primes.isPrime(n))

  /** A small certificate checked by Stainless itself: 7 with the primitive root 3 (7 - 1 = 2 * 3). */
  @ghost @opaque @inlineOnce
  def sevenIsPrime(): Unit = {
    val f2 = PrattFactor(BigInt(2), BigInt(1), BigInt(3))
    val f3 = PrattFactor(BigInt(3), BigInt(1), BigInt(2))
    val s3 = PrattStep(BigInt(3), BigInt(2), List(PrattFactor(BigInt(2), BigInt(1), BigInt(1))))
    val s7 = PrattStep(BigInt(7), BigInt(3), List(f2, f3))
    assert(modPow(BigInt(2), BigInt(1), BigInt(3)) == BigInt(2))
    assert(modPow(BigInt(2), BigInt(2), BigInt(3)) == BigInt(1))
    assert(product(s3.factors) == BigInt(2))
    assert(stepOk(s3, List(BigInt(2))))
    // modPow's contract reduces each power to the spec pow, which unrolls on small exponents.
    assert(pow(BigInt(3), BigInt(2)) == BigInt(9) && pow(BigInt(3), BigInt(3)) == BigInt(27))
    assert(pow(BigInt(3), BigInt(6)) == BigInt(729))
    assert(modPow(BigInt(3), BigInt(3), BigInt(7)) == BigInt(6))
    assert(modPow(BigInt(3), BigInt(2), BigInt(7)) == BigInt(2))
    assert(modPow(BigInt(3), BigInt(6), BigInt(7)) == BigInt(1))
    assert(product(s7.factors) == BigInt(6))
    assert(factorsOk(BigInt(7), BigInt(3), s7.factors, List(BigInt(3), BigInt(2))))
    assert(stepOk(s7, List(BigInt(3), BigInt(2))))
    assert(checkSteps(List(s3, s7), List(BigInt(2))))
    assert(certifies(List(s3, s7), BigInt(7)))
    certifiesSound(List(s3, s7), BigInt(7))
  }.ensuring(_ => Primes.isPrime(BigInt(7)))

  /** Kills a checker without known.contains(q): 9 - 1 == 8^1, 8^1 != 1 and 8^8 == 1 (mod 9), so only q = 8 being uncertified rejects 9. */
  @ghost @opaque @inlineOnce
  def uncertifiedFactorRejected(): Unit = {
    ()
  }.ensuring(_ => !certifies(List(PrattStep(BigInt(9), BigInt(8), List(PrattFactor(BigInt(8), BigInt(1), BigInt(1))))), BigInt(9)))

  // ──────────────────────────────────────────────────────────────────────────
  // The curve constants
  // ──────────────────────────────────────────────────────────────────────────

  /**
   * TCB T6 — the four generated certificates check. Established by executing this very
   * `certifies` on the JVM (run_jvm.sh, PrattJvm); a deterministic computation that
   * Stainless cannot unroll at 256 bits (modPow to depth 256 times hundreds of steps).
   */
  @extern @ghost
  def curveCertsChecked(): Unit = {
    ()
  }.ensuring(_ =>
    certifies(PrattCerts.secp256k1PCert, PrattCerts.secp256k1P) &&
    certifies(PrattCerts.secp256k1NCert, PrattCerts.secp256k1N) &&
    certifies(PrattCerts.p256PCert, PrattCerts.p256P) &&
    certifies(PrattCerts.p256NCert, PrattCerts.p256N))

  /** p and n of secp256k1 and P-256 are prime (T5 + T6; replaces T4). */
  @ghost @opaque @inlineOnce
  def curveConstantsPrime(): Unit = {
    curveCertsChecked()
    certifiesSound(PrattCerts.secp256k1PCert, PrattCerts.secp256k1P)
    certifiesSound(PrattCerts.secp256k1NCert, PrattCerts.secp256k1N)
    certifiesSound(PrattCerts.p256PCert, PrattCerts.p256P)
    certifiesSound(PrattCerts.p256NCert, PrattCerts.p256N)
  }.ensuring(_ =>
    Primes.isPrime(PrattCerts.secp256k1P) && Primes.isPrime(PrattCerts.secp256k1N) &&
    Primes.isPrime(PrattCerts.p256P) && Primes.isPrime(PrattCerts.p256N))
}

/** The curves of SEC 2 / FIPS 186-4, built with their primality proved (T5 + T6). */
object Curves {

  def secp256k1: CurveParams = {
    ghostExpr(Pratt.curveConstantsPrime())
    ghostExpr(unfold(CurveParams.nonSingular(BigInt(0), BigInt(7), PrattCerts.secp256k1P)))
    CurveParams(BigInt(0), BigInt(7), PrattCerts.secp256k1P)
  }

  def p256: CurveParams = {
    ghostExpr(Pratt.curveConstantsPrime())
    ghostExpr(unfold(CurveParams.nonSingular(BigInt(-3), p256B, PrattCerts.p256P)))
    CurveParams(BigInt(-3), p256B, PrattCerts.p256P)
  }

  val p256B: BigInt = BigInt("41058363725152142129326129780047268409114441015993725554835256314039467401291")
}
