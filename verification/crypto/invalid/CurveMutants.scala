package crypto

import stainless.lang._
import stainless.lang.StaticChecks._
import crypto.Curve._

// Each mutant weakens one precondition or corrupts one formula of the group law;
// every one must come out invalid (CurveMutants.check).
object CurveMutants {

  // The v1 bug (E2): the signed % of x^3 + a*x + b goes negative for a = -3.
  def rhsSignedRem(x: BigInt, c: CurveParams): Boolean = {
    require(inField(x, c.p))
    (x * x * x + c.a * x + c.b) % c.p >= 0
  }.holds

  // add with a point that is not on the curve violates the precondition.
  def addOffCurve(x: BigInt, y: BigInt, c: CurveParams): ECPoint = {
    require(inField(x, c.p) && inField(y, c.p))
    add(AffinePoint(x, y), InfinityPoint, c)
  }

  // Division by zero in the slope.
  def slopeOverZero(n: BigInt, p: BigInt): BigInt = {
    require(Primes.isPrime(p) && n >= 0)
    slope(n, BigInt(0), p)
  }

  // The tangent at a point of order 2 (y == 0) divides by zero.
  def tangentAtOrderTwo(x: BigInt, c: CurveParams): ECPoint = {
    require(inField(x, c.p))
    tangent(x, BigInt(0), c)
  }

  // Chord certificate with the wrong cofactor (l^2 - x1 - x2 instead of l^2 - 2*x1 - x2).
  def chordCertWrongCofactor(x1: BigInt, y1: BigInt, x2: BigInt, l: BigInt, a: BigInt, b: BigInt): Boolean = {
    val x3 = l * l - x1 - x2
    val y3 = l * (x1 - x3) - y1
    y3 * y3 - (x3 * x3 * x3 + a * x3 + b) ==
      (y1 * y1 - (x1 * x1 * x1 + a * x1 + b)) +
      (l * l - x1 - x2) * (l * l * (x2 - x1) + 2 * l * y1 - (x2 * x2 + x1 * x2 + x1 * x1 + a))
  }.holds

  // Point addition with a flipped sign in y3 (SPEC R6: a wrong formula the prover would accept on its own).
  def chordFlippedY(x1: BigInt, y1: BigInt, x2: BigInt, l: BigInt, a: BigInt, b: BigInt): Boolean = {
    val x3 = l * l - x1 - x2
    val y3 = l * (x3 - x1) - y1
    y3 * y3 - (x3 * x3 * x3 + a * x3 + b) ==
      (y1 * y1 - (x1 * x1 * x1 + a * x1 + b)) +
      (l * l - 2 * x1 - x2) * (l * l * (x2 - x1) + 2 * l * y1 - (x2 * x2 + x1 * x2 + x1 * x1 + a))
  }.holds

  // Doubling with x3 = l^2 - x instead of l^2 - 2x.
  def tangentWrongX(x: BigInt, y: BigInt, l: BigInt, a: BigInt, b: BigInt): Boolean = {
    val x3 = l * l - x
    val y3 = l * (x - x3) - y
    y3 * y3 - (x3 * x3 * x3 + a * x3 + b) ==
      (y * y - (x * x * x + a * x + b)) + (l * l - 3 * x) * (2 * l * y - (3 * x * x + a))
  }.holds

  // Negation without the zero case leaves the field.
  def negNoZeroCase(x: BigInt, c: CurveParams): Boolean = {
    require(isOnCurve(AffinePoint(x, BigInt(0)), c))
    isOnCurve(AffinePoint(x, c.p - BigInt(0)), c)
  }.holds

  // P + P is not the point at infinity for y != 0.
  def doubleIsInfinity(x: BigInt, y: BigInt, c: CurveParams): Boolean = {
    require(isOnCurve(AffinePoint(x, y), c) && y != 0)
    add(AffinePoint(x, y), AffinePoint(x, y), c) == InfinityPoint
  }.holds
}
