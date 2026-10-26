package crypto

import stainless.lang._
import stainless.lang.StaticChecks._
import stainless.collection._
import crypto.NumberTheory._
import crypto.Curve._
import crypto.Pratt._

// Each mutant breaks one certificate or weakens one contract of PR 6;
// every one must come out invalid (PrattMutants.check).
object PrattMutants {
  val s3 = PrattStep(BigInt(3), BigInt(2), List(PrattFactor(BigInt(2), BigInt(1), BigInt(1))))
  val f7 = List(PrattFactor(BigInt(2), BigInt(1), BigInt(3)), PrattFactor(BigInt(3), BigInt(1), BigInt(2)))

  // A wrong primitive root: 2 has order 3 modulo 7 (2^3 == 1), so the certificate is rejected.
  def wrongPrimitiveRoot(): Boolean = {
    assert(pow(BigInt(2), BigInt(3)) == BigInt(8))
    certifies(List(s3, PrattStep(BigInt(7), BigInt(2), f7)), BigInt(7))
  }.holds

  // A composite: 9 - 1 == 2^3, and 2^8 == 4 (mod 9) breaks Fermat.
  def compositeNine(): Boolean = {
    assert(pow(BigInt(2), BigInt(8)) == BigInt(256))
    certifies(List(PrattStep(BigInt(9), BigInt(2), List(PrattFactor(BigInt(2), BigInt(3), BigInt(4))))), BigInt(9))
  }.holds

  // A checker without the order test a^((p-1)/q) != 1 accepts the wrong root above.
  def noOrderTest(s: PrattStep, known: List[BigInt]): Boolean =
    s.p > 2 && 0 < s.a && s.a < s.p && s.factors.nonEmpty && product(s.factors) == s.p - 1 &&
      modPow(s.a, s.p - 1, s.p) == BigInt(1)

  def noOrderTestAgrees(): Boolean = {
    val s7 = PrattStep(BigInt(7), BigInt(2), f7)
    assert(pow(BigInt(2), BigInt(6)) == BigInt(64) && pow(BigInt(2), BigInt(3)) == BigInt(8))
    noOrderTest(s7, List(BigInt(3), BigInt(2))) == stepOk(s7, List(BigInt(3), BigInt(2)))
  }.holds

  // factorsOk without known.contains(f.q): the composite q = 8 passes the order test and 9 is accepted.
  def factorsOkNoKnown(p: BigInt, a: BigInt, fs: List[PrattFactor]): Boolean = {
    require(p > 2 && 0 < a && a < p)
    decreases(fs)
    fs match {
      case Nil() => true
      case Cons(f, t) =>
        f.e >= 1 && f.cofactor >= 0 && f.q * f.cofactor == p - 1 &&
          modPow(a, f.cofactor, p) != BigInt(1) && factorsOkNoKnown(p, a, t)
    }
  }

  def noKnownCheckAgrees(): Boolean = {
    val fs = List(PrattFactor(BigInt(8), BigInt(1), BigInt(1)))
    factorsOkNoKnown(BigInt(9), BigInt(8), fs) == factorsOk(BigInt(9), BigInt(8), fs, List(BigInt(2)))
  }.holds

  // scalarMul without isOnCurve(P): [1]P == P + O is off the curve.
  def scalarMulOffCurve(k: BigInt, pt: ECPoint, c: CurveParams): ECPoint = {
    require(k >= 0)
    decreases(k)
    if (k == 0) InfinityPoint
    else {
      val d = double(scalarMulOffCurve(k / 2, pt, c), c)
      if (k % 2 == 0) d else add(d, pt, c)
    }
  }.ensuring(res => isOnCurve(res, c))

  // scalarMul whose recursion does not shrink k (k - k/2 instead of k/2) fails at k == 1.
  def scalarMulNoProgress(k: BigInt, pt: ECPoint, c: CurveParams): ECPoint = {
    require(k >= 0 && isOnCurve(pt, c))
    decreases(k)
    if (k == 0) InfinityPoint
    else {
      val d = double(scalarMulNoProgress(k - k / 2, pt, c), c)
      if (k % 2 == 0) d else add(d, pt, c)
    }
  }.ensuring(res => isOnCurve(res, c))
}
