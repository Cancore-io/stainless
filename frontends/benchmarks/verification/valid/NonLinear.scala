import stainless.lang._
import stainless.math.NonLinear._

// Every lemma of stainless.math.NonLinear, used from non-ghost code, plus the
// concrete roundHalfEven table of Daml Numeric banker's rounding.
object NonLinearUse {

  def floorDivision(x: BigInt, y: BigInt, d: BigInt): Boolean = {
    require(y >= 0 && d > 0)
    ghost(divBounds(y, d))
    ghost(divGalois(x, y, d))
    y / d * d <= y && y < y / d * d + d && ((x * d <= y) == (x <= y / d))
  }.holds

  def uniqueness(q: BigInt, r: BigInt, d: BigInt): Boolean = {
    require(q >= 0 && d > 0 && 0 <= r && r < d)
    ghost(divUnique(q * d + r, d, q, r))
    (q * d + r) / d == q && (q * d + r) % d == r
  }.holds

  def monotonicity(y1: BigInt, y2: BigInt, d1: BigInt, d2: BigInt): Boolean = {
    require(0 <= y1 && y1 <= y2 && 0 < d1 && d1 <= d2)
    ghost(divMonoNumerator(y1, y2, d1))
    ghost(divAntiMonoDenominator(y1, d1, d2))
    y1 / d1 <= y2 / d1 && y1 / d2 <= y1 / d1
  }.holds

  // The fee shape: a*r1/(S+r1) <= a*r2/(S+r2) for r1 <= r2, no fixed S.
  def crossMultiplyFee(a: BigInt, s: BigInt, r1: BigInt, r2: BigInt): Boolean = {
    require(a >= 0 && s > 0 && 0 <= r1 && r1 <= r2)
    ghost(mulNonNeg(a, s))
    ghost(mulMonoLeft(r1, r2, a * s))
    // a*r1*(s+r2) - a*r2*(s+r1) = a*s*(r1 - r2) <= 0
    ghost(mulNonNeg(a, r1))
    ghost(crossMultiply(a * r1, s + r1, a * r2, s + r2))
    (a * r1) / (s + r1) <= (a * r2) / (s + r2)
  }.holds

  def products(a: BigInt, aMax: BigInt, b: BigInt, bMax: BigInt): Boolean = {
    require(0 <= a && a <= aMax && 0 <= b && b <= bMax)
    ghost(mulBounded(a, aMax, b, bMax))
    0 <= a * b && a * b <= aMax * bMax
  }.holds

  def modular(a: BigInt, b: BigInt, m: BigInt): Boolean = {
    require(a >= 0 && b >= 0 && m > 0)
    ghost(modSum(a, b, m))
    ghost(modMul(a, b, m))
    (a + b).mod(m) == (a.mod(m) + b.mod(m)).mod(m) && (a * b).mod(m) == (a.mod(m) * b.mod(m)).mod(m)
  }.holds

  // Any sign: the Euclidean remainder floorMod.
  def signedModular(a: BigInt, b: BigInt, m: BigInt): Boolean = {
    require(m > 0)
    ghost(floorModSum(a, b, m))
    ghost(floorModMul(a, b, m))
    floorMod(a + b, m) == floorMod(floorMod(a, m) + floorMod(b, m), m) &&
    floorMod(a * b, m) == floorMod(floorMod(a, m) * floorMod(b, m), m) &&
    0 <= floorMod(a, m) && floorMod(a, m) < m
  }.holds

  def uniqueSigned(q: BigInt, r: BigInt, m: BigInt): Boolean = {
    require(m > 0 && 0 <= r && r < m)
    ghost(floorDivUnique(q * m + r, m, q, r))
    floorDiv(q * m + r, m) == q && floorMod(q * m + r, m) == r
  }.holds

  def modularEdges(): Boolean = {
    (BigInt(-1) + 0).mod(3) == 2 && (BigInt(-4) + 5).mod(3) == 1 && (BigInt(-4) * 5).mod(3) == 1 &&
    (BigInt(7) + 9).mod(1) == 0 && (BigInt(7) * 9).mod(1) == 0 &&
    floorMod(-1, 3) == 2 && floorMod(BigInt(-4) + 5, 3) == 1 && floorMod(BigInt(-4) * 5, 3) == 1
  }.holds

  // Truncation vs floor on a negative dividend.
  def signedFloor(): Boolean = {
    BigInt(-7) / 2 == -3 && floorDiv(-7, 2) == -4 &&
    BigInt(-1) / 10 == 0 && floorDiv(-1, 10) == -1 &&
    BigInt(-10) / 5 == -2 && floorDiv(-10, 5) == -2 &&
    floorDiv(7, 1) == 7 && floorDiv(-7, 1) == -7 && floorDiv(0, 1) == 0 && floorDiv(0, 5) == 0
  }.holds

  // Daml Numeric HALF_EVEN, incl. Numeric 10 operands in units of 1e-10.
  def bankersTable(): Boolean = {
    roundHalfEven(10, 3) == 3 && roundHalfEven(11, 3) == 4 &&
    roundHalfEven(5, 2) == 2 && roundHalfEven(7, 2) == 4 &&
    roundHalfEven(-5, 2) == -2 && roundHalfEven(-7, 2) == -4 &&
    roundHalfEven(BigInt(10000000000L), BigInt(20000000000L)) == 0 &&
    roundHalfEven(BigInt(30000000000L), BigInt(20000000000L)) == 2 &&
    roundHalfEven(7, 1) == 7 && roundHalfEven(-7, 1) == -7 && roundHalfEven(0, 1) == 0 && roundHalfEven(0, 5) == 0
  }.holds

  def roundingBounds(n: BigInt, d: BigInt, k: BigInt): Boolean = {
    require(d > 0)
    val q = roundHalfEven(n, d)
    ghost(roundHalfEvenTie(n, d))
    2 * (q * d - n) <= d && 2 * (n - q * d) <= d &&
    ((2 * (q * d - n) == d || 2 * (n - q * d) == d) ==> (q % 2 == 0))
  }.holds

  // An odd divisor has no tie: the bound is strict.
  def oddDivisorNoTie(n: BigInt, d: BigInt): Boolean = {
    require(d > 0 && d % 2 == 1)
    val q = roundHalfEven(n, d)
    2 * (q * d - n) < d && 2 * (n - q * d) < d
  }.holds

  def roundingLowerUpper(n: BigInt, d: BigInt, k: BigInt): Boolean = {
    require(d > 0 && 2 * n > (2 * k - 1) * d && 2 * n < (2 * k + 1) * d)
    ghost(roundHalfEvenLower(n, d, k))
    ghost(roundHalfEvenUpper(n, d, k))
    roundHalfEven(n, d) == k
  }.holds

  // The Daml fee a - a/(1+r) is monotone in the rate.
  def damlFeeMonotone(a: BigInt, s: BigInt, r1: BigInt, r2: BigInt): Boolean = {
    require(a >= 0 && s > 0 && 0 <= r1 && r1 <= r2)
    ghost(mulNonNeg(a, s))
    ghost(mulMonoLeft(s + r1, s + r2, a * s))
    ghost(roundHalfEvenMono(a * s, s + r2, a * s, s + r1))
    a - roundHalfEven(a * s, s + r1) <= a - roundHalfEven(a * s, s + r2)
  }.holds
}
