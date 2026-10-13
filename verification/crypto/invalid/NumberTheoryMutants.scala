package crypto

import stainless.lang.{ghost => ghostExpr, _}
import stainless.lang.StaticChecks._
import stainless.annotation._
import stainless.math.NonLinear._
import crypto.NumberTheory._

// Each mutant weakens one precondition or corrupts one conclusion of NumberTheory;
// every one must come out invalid (NumberTheoryMutants.check), so the real
// contracts are not stronger than what is proved nor their requires looser.
object NumberTheoryMutants {

  // extendedGcd without (a > 0 || b > 0): (0, 0) yields gcd 0.
  def extendedGcdZero(a: BigInt, b: BigInt): GcdWitness = {
    require(a >= 0 && b >= 0)
    decreases(b)
    if (b == 0) GcdWitness(a, BigInt(1), BigInt(0), BigInt(1), BigInt(0))
    else extendedGcd(a, b)
  }.ensuring(res => res.gcd > 0 && a == res.ka * res.gcd && b == res.kb * res.gcd)

  // Bezout corrupted: on the operands the pair gives gcd, not 1.
  def bezoutOnOperandsIsOne(a: BigInt, b: BigInt): Boolean = {
    require(a >= 0 && b >= 0 && (a > 0 || b > 0))
    val w = extendedGcd(a, b)
    a * w.x + b * w.y == BigInt(1)
  }.holds

  // gcdIsGreatest without gcd > 0: a negative "gcd" is below a positive divisor.
  def greatestNegativeGcd(a: BigInt, b: BigInt, w: GcdWitness, d: BigInt, da: BigInt, db: BigInt): Boolean = {
    require(a == w.ka * w.gcd && b == w.kb * w.gcd && w.ka * w.x + w.kb * w.y == BigInt(1) &&
      a == da * d && b == db * d)
    d <= w.gcd
  }.holds

  // unitFactor without g > 0: g = k = -1.
  def unitFactorSigned(g: BigInt, k: BigInt): Boolean = {
    require(g * k == BigInt(1))
    g == BigInt(1)
  }.holds

  // modInverse with require(m > 1) weakened to m > 0: m = 1 has no inverse, yet gcd(0, 1) == 1.
  def modInverseM1(a: BigInt, m: BigInt): Option[BigInt] = {
    require(m > 0)
    val w = extendedGcd(a.mod(m), m)
    if (w.gcd != BigInt(1)) None[BigInt]()
    else Some(floorMod(w.x, m))
  }.ensuring(res => res.forall(r => (a.mod(m) * r).mod(m) == BigInt(1)))

  // modInverse corrupted conclusion: 3^-1 mod 7 is 5, not 3.
  def modInverseWrongValue(): Boolean = {
    modInverse(BigInt(3), BigInt(7)) == Some(BigInt(3))
  }.holds

  // Completeness corrupted: 3 is invertible mod 7, yet None is claimed.
  def modInverseNone(): Boolean = {
    modInverse(BigInt(3), BigInt(7)).isEmpty
  }.holds

  // powAdd corrupted: exponents add under +, not *.
  def powAddPlus(b: BigInt, i: BigInt, j: BigInt): Boolean = {
    require(i >= 0 && j >= 0)
    pow(b, i + j) == pow(b, i) + pow(b, j)
  }.holds

  // modPow with m > 0 weakened to m >= 0: modulo by zero.
  def modPowM0(b: BigInt, e: BigInt, m: BigInt): BigInt = {
    require(b >= 0 && e >= 0 && m >= 0)
    BigInt(1).mod(m)
  }

  // modPow's odd step dropped: squaring b^k alone does not give b^(2k+1).
  def modPowOddNoMultiply(b: BigInt, k: BigInt, m: BigInt, h: BigInt): Boolean = {
    require(b >= 0 && k >= 0 && m > 0 && h == pow(b, k).mod(m))
    (h * h).mod(m) == pow(b, 2 * k + 1).mod(m)
  }.holds

  // crt without r1 < m1: the residue r1 itself cannot be the remainder.
  def crtResidueOutOfRange(r1: BigInt, m1: BigInt, r2: BigInt, m2: BigInt): Boolean = {
    require(m1 > 0 && m2 > 0 && 0 <= r1 && 0 <= r2 && r2 < m2)
    val w = extendedGcd(m1, m2)
    w.gcd != BigInt(1) || (r1 + m1 * floorMod((r2 - r1) * w.x, m2)).mod(m1) == r1
  }.holds

  // crt corrupted conclusion: the residues swapped.
  def crtSwapped(r1: BigInt, m1: BigInt, r2: BigInt, m2: BigInt): Boolean = {
    require(m1 > 0 && m2 > 0 && 0 <= r1 && r1 < m1 && 0 <= r2 && r2 < m2)
    crt(r1, m1, r2, m2).forall(x => x.mod(m1) == r2)
  }.holds
}
