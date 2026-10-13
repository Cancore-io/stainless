package crypto

import stainless.lang._
import stainless.lang.StaticChecks._
import crypto.FieldElem._

// Each mutant weakens one precondition or corrupts one operation or law of
// PrimeField / SqrtMod; every one must come out invalid (PrimeFieldMutants.check).
object PrimeFieldMutants {

  // The field's division by zero: inverse of v = 0 violates the precondition.
  def inverseOfZero(p: BigInt): FieldElem = {
    require(Primes.isPrime(p) && p > 1)
    FieldElem(BigInt(0), p).inverse
  }

  // inverse without primality: v = 2 has no inverse mod 4.
  def inverseComposite(v: BigInt, p: BigInt): FieldElem = {
    require(p > 1 && 0 < v && v < p)
    FieldElem(v, p).inverse
  }

  // + without the reduction leaves the field.
  def addNoReduce(x: FieldElem, y: FieldElem): FieldElem = {
    require(x.p == y.p)
    FieldElem(x.v + y.v, x.p)
  }

  // Negation without the zero case: -0 == p is out of range.
  def negNoZeroCase(x: FieldElem): FieldElem = FieldElem(x.p - x.v, x.p)

  // of(n) with the signed % instead of mod: negative n leaves the field.
  def ofSignedRem(n: BigInt, p: BigInt): FieldElem = {
    require(p > 1)
    FieldElem(n % p, p)
  }

  // Additive inverse law corrupted.
  def addNegIsOne(x: FieldElem): Boolean = {
    x + (-x) == one(x.p)
  }.holds

  // Distributivity corrupted.
  def distribDropX(x: FieldElem, y: FieldElem, z: FieldElem): Boolean = {
    require(x.p == y.p && y.p == z.p)
    x * (y + z) == x * y + z
  }.holds

  // Multiplicative inverse law without primality.
  def mulInverseAnyModulus(x: FieldElem): Boolean = {
    require(x.v != 0)
    x * x.inverse == one(x.p)
  }.holds

  // sqrtMod without its certificate check: the candidate (here any r in [0, p),
  // since Tonelli-Shanks is not proved) is returned as a root.
  def sqrtUnchecked(n: BigInt, p: BigInt, r: BigInt): Option[BigInt] = {
    require(p > 2 && 0 <= r && r < p)
    Some(r)
  }.ensuring(res => res.forall(r => (r * r).mod(p) == n.mod(p)))
}
