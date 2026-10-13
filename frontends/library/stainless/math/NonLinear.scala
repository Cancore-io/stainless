package stainless.math

import stainless.lang._
import stainless.annotation._

/**
 * Witness-form lemmas for non-linear BigInt arithmetic and integer division.
 *
 * Every lemma returns `Unit` and states its fact in `ensuring`; the caller
 * invokes it (inside `ghost(...)` from non-ghost code) to bring the fact into
 * scope. The annotations `@ghost @pure @opaque @inlineOnce` are the expansion
 * of `@lemma` (epfl-lara/stainless#1795), spelled out so the file also
 * compiles on the 0.10.2 release, which has no `@lemma`. `@opaque` hides the
 * proof body from callers: the solver sees the postcondition only, which is
 * what keeps the callers' queries small.
 *
 * Division semantics. `/` and `%` on BigInt truncate toward zero (Java/Scala),
 * so the floor-division lemmas below require a non-negative dividend. The
 * signed floor is `floorDiv`; `roundHalfEven` is built on it and matches the
 * banker's rounding of Daml `Numeric` (`RoundingMode.HALF_EVEN` for both `*`
 * and `/`, daml-lf `NumericModule.divide` / `multiply`). Divisors are always
 * positive here: a negative divisor is out of scope.
 */
object NonLinear {

  // ──────────────────────────────────────────────────────────────────────────
  // Products
  // ──────────────────────────────────────────────────────────────────────────

  @ghost @pure @opaque @inlineOnce
  def mulNonNeg(a: BigInt, b: BigInt): Unit = {
    require(a >= 0 && b >= 0)
  }.ensuring(_ => a * b >= 0)

  @ghost @pure @opaque @inlineOnce
  def mulPos(a: BigInt, b: BigInt): Unit = {
    require(a > 0 && b > 0)
  }.ensuring(_ => a * b > 0)

  /** a <= b, c >= 0  ==>  a*c <= b*c */
  @ghost @pure @opaque @inlineOnce
  def mulMonoLeft(a: BigInt, b: BigInt, c: BigInt): Unit = {
    require(a <= b && c >= 0)
    mulNonNeg(b - a, c)
  }.ensuring(_ => a * c <= b * c)

  /** a < b, c > 0  ==>  a*c < b*c */
  @ghost @pure @opaque @inlineOnce
  def mulStrictMonoLeft(a: BigInt, b: BigInt, c: BigInt): Unit = {
    require(a < b && c > 0)
    mulPos(b - a, c)
  }.ensuring(_ => a * c < b * c)

  /** c > 0, a*c <= b*c  ==>  a <= b */
  @ghost @pure @opaque @inlineOnce
  def mulCancelLe(a: BigInt, b: BigInt, c: BigInt): Unit = {
    require(c > 0 && a * c <= b * c)
    if (a > b) mulStrictMonoLeft(b, a, c)
  }.ensuring(_ => a <= b)

  /** c > 0, a*c < b*c  ==>  a < b */
  @ghost @pure @opaque @inlineOnce
  def mulCancelLt(a: BigInt, b: BigInt, c: BigInt): Unit = {
    require(c > 0 && a * c < b * c)
    if (a >= b) mulMonoLeft(b, a, c)
  }.ensuring(_ => a < b)

  /** 0 <= a <= A, 0 <= b <= B  ==>  0 <= a*b <= A*B */
  @ghost @pure @opaque @inlineOnce
  def mulBounded(a: BigInt, aMax: BigInt, b: BigInt, bMax: BigInt): Unit = {
    require(0 <= a && a <= aMax && 0 <= b && b <= bMax)
    mulNonNeg(a, b)
    mulMonoLeft(a, aMax, b)
    mulMonoLeft(b, bMax, aMax)
  }.ensuring(_ => 0 <= a * b && a * b <= aMax * bMax)

  // ──────────────────────────────────────────────────────────────────────────
  // Floor division of a non-negative dividend (truncation == floor there)
  // ──────────────────────────────────────────────────────────────────────────

  /** y >= 0, d > 0  ==>  y/d*d <= y < y/d*d + d, and y/d >= 0 */
  @ghost @pure @opaque @inlineOnce
  def divBounds(y: BigInt, d: BigInt): Unit = {
    require(y >= 0 && d > 0)
  }.ensuring(_ => y / d >= 0 && (y / d) * d <= y && y < (y / d) * d + d)

  /** Galois connection: y >= 0, d > 0  ==>  (x*d <= y  <==>  x <= y/d) */
  @ghost @pure @opaque @inlineOnce
  def divGalois(x: BigInt, y: BigInt, d: BigInt): Unit = {
    require(y >= 0 && d > 0)
    divBounds(y, d)
    val q = y / d
    if (x <= q) mulMonoLeft(x, q, d)
    else mulMonoLeft(q + 1, x, d)
  }.ensuring(_ => (x * d <= y) == (x <= y / d))

  /** y = q*d + r, 0 <= r < d, y >= 0  ==>  q == y/d and r == y % d */
  @ghost @pure @opaque @inlineOnce
  def divUnique(y: BigInt, d: BigInt, q: BigInt, r: BigInt): Unit = {
    require(y >= 0 && d > 0 && 0 <= r && r < d && y == q * d + r)
    divBounds(y, d)
    val p = y / d
    // (q - p)*d lies strictly between -d and d, so q == p.
    if (q > p) mulMonoLeft(p + 1, q, d)
    if (q < p) mulMonoLeft(q + 1, p, d)
  }.ensuring(_ => q == y / d && r == y % d)

  /** 0 <= y1 <= y2, d > 0  ==>  y1/d <= y2/d */
  @ghost @pure @opaque @inlineOnce
  def divMonoNumerator(y1: BigInt, y2: BigInt, d: BigInt): Unit = {
    require(0 <= y1 && y1 <= y2 && d > 0)
    divBounds(y1, d)
    divGalois(y1 / d, y2, d)
  }.ensuring(_ => y1 / d <= y2 / d)

  /** y >= 0, 0 < d1 <= d2  ==>  y/d2 <= y/d1 */
  @ghost @pure @opaque @inlineOnce
  def divAntiMonoDenominator(y: BigInt, d1: BigInt, d2: BigInt): Unit = {
    require(y >= 0 && 0 < d1 && d1 <= d2)
    divBounds(y, d2)
    val q = y / d2
    mulMonoLeft(d1, d2, q)
    divGalois(q, y, d1)
  }.ensuring(_ => y / d2 <= y / d1)

  /** n1 >= 0, d1 > 0, d2 > 0, n1*d2 <= n2*d1  ==>  n1/d1 <= n2/d2 */
  @ghost @pure @opaque @inlineOnce
  def crossMultiply(n1: BigInt, d1: BigInt, n2: BigInt, d2: BigInt): Unit = {
    require(n1 >= 0 && d1 > 0 && d2 > 0 && n1 * d2 <= n2 * d1)
    divBounds(n1, d1)
    val q = n1 / d1
    mulNonNeg(n1, d2)
    mulCancelLe(0, n2, d1)                // n2 >= 0
    mulMonoLeft(q * d1, n1, d2)           // q*d1*d2 <= n1*d2 <= n2*d1
    mulCancelLe(q * d2, n2, d1)           // q*d2 <= n2
    divGalois(q, n2, d2)
  }.ensuring(_ => n1 / d1 <= n2 / d2)

  // ──────────────────────────────────────────────────────────────────────────
  // Non-negative modulus (BigInt.mod is always in [0, m) for m > 0)
  // ──────────────────────────────────────────────────────────────────────────

  /** y = q*m + r, 0 <= r < m  ==>  y.mod(m) == r (any sign of y and q) */
  @ghost @pure @opaque @inlineOnce
  def modUnique(y: BigInt, m: BigInt, q: BigInt, r: BigInt): Unit = {
    require(m > 0 && 0 <= r && r < m && y == q * m + r)
    if (y >= 0) modUniqueNonNeg(y, m, q, r) else modUniqueNeg(y, m, q, r)
  }.ensuring(_ => y.mod(m) == r)

  @ghost @pure @opaque @inlineOnce
  private def modUniqueNonNeg(y: BigInt, m: BigInt, q: BigInt, r: BigInt): Unit = {
    require(y >= 0 && m > 0 && 0 <= r && r < m && y == q * m + r)
    // SMT `mod` pairs with the very `div` term y / m encodes to here.
    val k = y / m
    assert(y.mod(m) == y - k * m)
    // k*m <= y < k*m + m and q*m <= y < q*m + m force q == k.
    if (q > k) mulMonoLeft(k + 1, q, m)
    if (q < k) mulMonoLeft(q + 1, k, m)
  }.ensuring(_ => y.mod(m) == r)

  /** Decided directly by the solver's Euclidean mod axioms; kept apart so the query stays bare. */
  @ghost @pure @opaque @inlineOnce
  private def modUniqueNeg(y: BigInt, m: BigInt, q: BigInt, r: BigInt): Unit = {
    require(y < 0 && m > 0 && 0 <= r && r < m && y == q * m + r)
  }.ensuring(_ => y.mod(m) == r)

  /** m > 0  ==>  y.mod(m) == y - floorDiv(y, m)*m */
  @ghost @pure @opaque @inlineOnce
  def modFloorDiv(y: BigInt, m: BigInt): Unit = {
    require(m > 0)
    modUnique(y, m, floorDiv(y, m), y - floorDiv(y, m) * m)
  }.ensuring(_ => y.mod(m) == y - floorDiv(y, m) * m)

  /** m > 0  ==>  (a+b).mod(m) == (a.mod(m) + b.mod(m)).mod(m) */
  @ghost @pure @opaque @inlineOnce
  def modSum(a: BigInt, b: BigInt, m: BigInt): Unit = {
    require(m > 0)
    val qa = floorDiv(a, m); val ra = a - qa * m
    val qb = floorDiv(b, m); val rb = b - qb * m
    modUnique(a, m, qa, ra)
    modUnique(b, m, qb, rb)
    val s = ra + rb
    val qs = floorDiv(s, m); val rs = s - qs * m
    modUnique(s, m, qs, rs)
    modUnique(a + b, m, qa + qb + qs, rs)
  }.ensuring(_ => (a + b).mod(m) == (a.mod(m) + b.mod(m)).mod(m))

  /** m > 0  ==>  (a*b).mod(m) == (a.mod(m) * b.mod(m)).mod(m) */
  @ghost @pure @opaque @inlineOnce
  def modMul(a: BigInt, b: BigInt, m: BigInt): Unit = {
    require(m > 0)
    val qa = floorDiv(a, m); val ra = a - qa * m
    val qb = floorDiv(b, m); val rb = b - qb * m
    modUnique(a, m, qa, ra)
    modUnique(b, m, qb, rb)
    val p = ra * rb
    val qp = floorDiv(p, m); val rp = p - qp * m
    modUnique(p, m, qp, rp)
    // a*b = (qa*m + ra)(qb*m + rb) = (qa*qb*m + qa*rb + ra*qb)*m + ra*rb
    val k = qa * qb * m + qa * rb + ra * qb
    assert(a * b == k * m + p)
    modUnique(a * b, m, k + qp, rp)
  }.ensuring(_ => (a * b).mod(m) == (a.mod(m) * b.mod(m)).mod(m))

  // ──────────────────────────────────────────────────────────────────────────
  // Signed floor division and Daml banker's rounding
  // ──────────────────────────────────────────────────────────────────────────

  /** floor(n / d) for any sign of n, d > 0; defined without `/` on a negative. */
  def floorDiv(n: BigInt, d: BigInt): BigInt = {
    require(d > 0)
    if (n >= 0) n / d else -((-n - 1) / d) - 1
  }.ensuring(f => f * d <= n && n < f * d + d)

  /**
   * n / d rounded to the nearest integer, ties to even — Daml `Numeric`
   * division (`RoundingMode.HALF_EVEN`). For a Numeric 10 quotient x / y in
   * units of 10^-10: roundHalfEven(x * 10^10, y).
   */
  def roundHalfEven(n: BigInt, d: BigInt): BigInt = {
    require(d > 0)
    val f = floorDiv(n, d)
    val r = n - f * d
    if (2 * r < d) f
    else if (2 * r > d) f + 1
    else if (f % 2 == 0) f
    else f + 1
  }.ensuring(q => 2 * (q * d - n) <= d && 2 * (n - q * d) <= d)

  /** A tie (|q*d - n| == d/2) is resolved to the even neighbour. */
  @ghost @pure @opaque @inlineOnce
  def roundHalfEvenTie(n: BigInt, d: BigInt): Unit = {
    require(d > 0)
  }.ensuring(_ => {
    val q = roundHalfEven(n, d)
    (2 * (q * d - n) == d || 2 * (n - q * d) == d) ==> (q % 2 == 0)
  })

  /** 2n > (2k-1)*d  ==>  roundHalfEven(n, d) >= k */
  @ghost @pure @opaque @inlineOnce
  def roundHalfEvenLower(n: BigInt, d: BigInt, k: BigInt): Unit = {
    require(d > 0 && 2 * n > (2 * k - 1) * d)
    val q = roundHalfEven(n, d)
    // 2n <= (2q+1)*d by the rounding bound.
    mulCancelLt(2 * k - 1, 2 * q + 1, d)
  }.ensuring(_ => roundHalfEven(n, d) >= k)

  /** 2n < (2k+1)*d  ==>  roundHalfEven(n, d) <= k */
  @ghost @pure @opaque @inlineOnce
  def roundHalfEvenUpper(n: BigInt, d: BigInt, k: BigInt): Unit = {
    require(d > 0 && 2 * n < (2 * k + 1) * d)
    val q = roundHalfEven(n, d)
    // (2q-1)*d <= 2n by the rounding bound.
    mulCancelLt(2 * q - 1, 2 * k + 1, d)
  }.ensuring(_ => roundHalfEven(n, d) <= k)

  /**
   * Monotone in the rational value: n1/d1 <= n2/d2 (cross-multiplied)
   * ==>  roundHalfEven(n1, d1) <= roundHalfEven(n2, d2).
   * Ties go to the even neighbour on both sides, so equal values round equal.
   */
  @ghost @pure @opaque @inlineOnce
  def roundHalfEvenMono(n1: BigInt, d1: BigInt, n2: BigInt, d2: BigInt): Unit = {
    require(d1 > 0 && d2 > 0 && n1 * d2 <= n2 * d1)
    val q1 = roundHalfEven(n1, d1)
    val q2 = roundHalfEven(n2, d2)
    if (q2 < q1) {
      val t = 2 * q1 - 1
      // 2*n1 >= t*d1 and 2*n2 <= (2*q2+1)*d2 <= t*d2
      mulMonoLeft(2 * q2 + 1, t, d2)
      mulMonoLeft(t * d1, 2 * n1, d2)        // t*d1*d2 <= 2*n1*d2
      mulMonoLeft(2 * n2, t * d2, d1)        // 2*n2*d1 <= t*d2*d1
      mulMonoLeft(n1 * d2, n2 * d1, BigInt(2))
      // The chain t*d1*d2 <= 2*n1*d2 <= 2*n2*d1 <= t*d1*d2 collapses.
      mulCancelLe(t * d1, 2 * n1, d2)
      mulCancelLe(2 * n1, t * d1, d2)
      mulCancelLe(2 * n2, t * d2, d1)
      mulCancelLe(t * d2, 2 * n2, d1)
      assert(2 * n1 == t * d1 && 2 * n2 == t * d2)
      // q1 sits on a tie, so it is even.
      roundHalfEvenTie(n1, d1)
      // q2 >= q1 - 1: else 2*(n2 - q2*d2) = (t - 2*q2)*d2 > d2.
      if (q2 < q1 - 1) mulStrictMonoLeft(BigInt(1), t - 2 * q2, d2)
      assert(q2 == q1 - 1)
      // ... so q2 sits on a tie too, and q1 = q2 + 1 cannot both be even.
      roundHalfEvenTie(n2, d2)
      assert(false)
    }
  }.ensuring(_ => roundHalfEven(n1, d1) <= roundHalfEven(n2, d2))
}
