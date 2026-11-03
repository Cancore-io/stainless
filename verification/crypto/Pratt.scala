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
 * rests on Lucas's theorem (`lucas`, proved in Lucas.scala); that the concrete
 * curve certificates check is proved by the generated traces in PrattTraces.scala.
 */
object Pratt {

  def product(fs: List[PrattFactor]): BigInt = {
    decreases(fs)
    fs match {
      case Nil()      => BigInt(1)
      case Cons(f, t) => if (f.e >= 0) pow(f.q, f.e) * product(t) else BigInt(0)
    }
  }

  /** Opaque: a ground certificate would unroll every modPow under it; lemmas unfold it. */
  /** Every factor: q certified before, e >= 1, q * cofactor == p - 1 and a^cofactor != 1 (mod p). */
  @opaque
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

  /** Lucas's primality theorem, proved in Lucas.scala (formerly TCB T5). */
  @ghost @opaque @inlineOnce
  def lucas(s: PrattStep, known: List[BigInt]): Unit = {
    require(known.forall(q => Primes.isPrime(q)) && stepOk(s, known))
    Lucas.forallAllPrime(known)
    Lucas.lucasTheorem(s, known)
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

  /** A checked certificate proves primality. */
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
    unfold(factorsOk(BigInt(3), BigInt(2), s3.factors, List(BigInt(2))))
    unfold(factorsOk(BigInt(3), BigInt(2), Nil[PrattFactor](), List(BigInt(2))))
    assert(stepOk(s3, List(BigInt(2))))
    // modPow's contract reduces each power to the spec pow, which unrolls on small exponents.
    assert(pow(BigInt(3), BigInt(2)) == BigInt(9) && pow(BigInt(3), BigInt(3)) == BigInt(27))
    assert(pow(BigInt(3), BigInt(6)) == BigInt(729))
    assert(modPow(BigInt(3), BigInt(3), BigInt(7)) == BigInt(6))
    assert(modPow(BigInt(3), BigInt(2), BigInt(7)) == BigInt(2))
    assert(modPow(BigInt(3), BigInt(6), BigInt(7)) == BigInt(1))
    assert(product(s7.factors) == BigInt(6))
    unfold(factorsOk(BigInt(7), BigInt(3), s7.factors, List(BigInt(3), BigInt(2))))
    unfold(factorsOk(BigInt(7), BigInt(3), s7.factors.tail, List(BigInt(3), BigInt(2))))
    unfold(factorsOk(BigInt(7), BigInt(3), Nil[PrattFactor](), List(BigInt(3), BigInt(2))))
    assert(factorsOk(BigInt(7), BigInt(3), s7.factors, List(BigInt(3), BigInt(2))))
    assert(stepOk(s7, List(BigInt(3), BigInt(2))))
    assert(checkSteps(List(s3, s7), List(BigInt(2))))
    assert(certifies(List(s3, s7), BigInt(7)))
    certifiesSound(List(s3, s7), BigInt(7))
  }.ensuring(_ => Primes.isPrime(BigInt(7)))

  /** Kills a checker without known.contains(q): 9 - 1 == 8^1, 8^1 != 1 and 8^8 == 1 (mod 9), so only q = 8 being uncertified rejects 9. */
  @ghost @opaque @inlineOnce
  def uncertifiedFactorRejected(): Unit = {
    unfold(factorsOk(BigInt(9), BigInt(8), List(PrattFactor(BigInt(8), BigInt(1), BigInt(1))), List(BigInt(2))))
  }.ensuring(_ => !certifies(List(PrattStep(BigInt(9), BigInt(8), List(PrattFactor(BigInt(8), BigInt(1), BigInt(1))))), BigInt(9)))

  /** factorsOk one factor at a time, so a generated proof never unfolds a whole factor list. */
  @ghost @opaque @inlineOnce
  def factorsOkCons(p: BigInt, a: BigInt, fs: List[PrattFactor], known: List[BigInt]): Unit = {
    require(p > 2 && 0 < a && a < p && fs.nonEmpty && known.contains(fs.head.q) && fs.head.e >= 1 &&
      fs.head.cofactor >= 0 && fs.head.q * fs.head.cofactor == p - 1 &&
      modPow(a, fs.head.cofactor, p) != BigInt(1) && factorsOk(p, a, fs.tail, known))
    unfold(factorsOk(p, a, fs, known))
  }.ensuring(_ => factorsOk(p, a, fs, known))

  @ghost @opaque @inlineOnce
  def factorsOkNil(p: BigInt, a: BigInt, known: List[BigInt]): Unit = {
    require(p > 2 && 0 < a && a < p)
    unfold(factorsOk(p, a, Nil[PrattFactor](), known))
  }.ensuring(_ => factorsOk(p, a, Nil[PrattFactor](), known))

  /** checkSteps one step at a time, so a generated proof never unfolds a whole certificate. */
  @ghost @opaque @inlineOnce
  def checkStepsCons(s: PrattStep, t: List[PrattStep], known: List[BigInt]): Unit = {
    require(stepOk(s, known) && checkSteps(t, s.p :: known))
  }.ensuring(_ => checkSteps(Cons(s, t), known))

  // ──────────────────────────────────────────────────────────────────────────
  // Square-and-multiply traces: one ground `mod` per step, chained through modPow's contract
  // ──────────────────────────────────────────────────────────────────────────

  @ghost @opaque @inlineOnce
  def traceBase(b: BigInt, m: BigInt, h: BigInt): Unit = {
    require(b >= 0 && m > 0 && h == b.mod(m))
    modPowOdd(b, BigInt(0), m, BigInt(1).mod(m))
    assert(modPow(b, BigInt(0), m) == BigInt(1).mod(m))
  }.ensuring(_ => modPow(b, BigInt(1), m) == h)

  @ghost @opaque @inlineOnce
  def traceSq(b: BigInt, e: BigInt, m: BigInt, h: BigInt, h2: BigInt): Unit = {
    require(b >= 0 && e >= 0 && m > 0 && modPow(b, e, m) == h && (h * h).mod(m) == h2)
    modPowEven(b, e, m, h)
  }.ensuring(_ => modPow(b, 2 * e, m) == h2)

  @ghost @opaque @inlineOnce
  def traceSqMul(b: BigInt, e: BigInt, m: BigInt, h: BigInt, h2: BigInt): Unit = {
    require(b >= 0 && e >= 0 && m > 0 && modPow(b, e, m) == h && ((h * h).mod(m) * b.mod(m)).mod(m) == h2)
    modPowOdd(b, e, m, h)
  }.ensuring(_ => modPow(b, 2 * e + 1, m) == h2)

  // ──────────────────────────────────────────────────────────────────────────
  // The curve constants
  // ──────────────────────────────────────────────────────────────────────────

  /** The four generated certificates check (formerly TCB T6): traces in PrattTraces.scala. */
  @ghost @opaque @inlineOnce
  def curveCertsChecked(): Unit = {
    PrattTraces.secp256k1PChecked()
    PrattTraces.secp256k1NChecked()
    PrattTraces.p256PChecked()
    PrattTraces.p256NChecked()
  }.ensuring(_ =>
    certifies(PrattCerts.secp256k1PCert, PrattCerts.secp256k1P) &&
    certifies(PrattCerts.secp256k1NCert, PrattCerts.secp256k1N) &&
    certifies(PrattCerts.p256PCert, PrattCerts.p256P) &&
    certifies(PrattCerts.p256NCert, PrattCerts.p256N))

  /** p and n of secp256k1 and P-256 are prime. */
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

/** The curves of SEC 2 / FIPS 186-4, built with their primality proved. */
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
