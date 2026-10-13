import stainless.lang._
import stainless.math.NonLinear._

// One wrong conclusion per lemma form, with the right preconditions: each is a
// counterexample, so a lemma weakened the same way would be caught.
object NonLinearMutants {
  def strictFloor(y: BigInt, d: BigInt): Boolean = {
    require(y >= 0 && d > 0)
    y / d * d < y
  }.holds

  def strictNumeratorMono(y1: BigInt, y2: BigInt, d: BigInt): Boolean = {
    require(0 <= y1 && y1 < y2 && d > 0)
    y1 / d < y2 / d
  }.holds

  def denominatorWrongWay(y: BigInt, d1: BigInt, d2: BigInt): Boolean = {
    require(y >= 0 && 0 < d1 && d1 <= d2)
    y / d1 <= y / d2
  }.holds

  def crossMultiplyFlipped(n1: BigInt, d1: BigInt, n2: BigInt, d2: BigInt): Boolean = {
    require(n1 >= 0 && d1 > 0 && d2 > 0 && n1 * d2 <= n2 * d1)
    n2 / d2 <= n1 / d1
  }.holds

  def mulBoundedNoLowerBound(a: BigInt, aMax: BigInt, b: BigInt, bMax: BigInt): Boolean = {
    require(a <= aMax && 0 <= b && b <= bMax)
    0 <= a * b && a * b <= aMax * bMax
  }.holds

  def modSumNoOuterMod(a: BigInt, b: BigInt, m: BigInt): Boolean = {
    require(m > 0)
    (a + b).mod(m) == a.mod(m) + b.mod(m)
  }.holds

  def roundingStrictBound(n: BigInt, d: BigInt): Boolean = {
    require(d > 0)
    val q = roundHalfEven(n, d)
    2 * (q * d - n) < d && 2 * (n - q * d) < d
  }.holds
}
