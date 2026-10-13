package crypto

import stainless.lang.{ghost => ghostExpr, _}
import stainless.lang.StaticChecks._
import stainless.annotation._
import stainless.math.NonLinear._
import crypto.NumberTheory._

/**
 * The group law of a short Weierstrass curve y^2 = x^3 + a*x + b over GF(p)
 * (SPEC.md §4 PR 5), affine coordinates in [0, p).
 *
 * Every `mod` dividend is non-negative: the coefficients enter reduced
 * (a.mod(p), so P-256's a = -3 is p - 3) and differences get + p or + 2p
 * first. Closure is proved by Groebner certificates checked as polynomial
 * identities over the integers (chordCert, tangentCert), turned into
 * congruences with explicit quotient witnesses; the one cancellation (by
 * x2 - x1) uses the primality of p.
 */
case class CurveParams(a: BigInt, b: BigInt, p: BigInt) {
  require(p > 3 && Primes.isPrime(p) && CurveParams.nonSingular(a, b, p))
}

object CurveParams {
  /** 4a^3 + 27b^2 != 0 (mod p). Opaque: the group law never needs it, and a cubic under `mod` in every context slows Z3 down. */
  @opaque
  def nonSingular(a: BigInt, b: BigInt, p: BigInt): Boolean = {
    require(p > 0)
    (4 * a * a * a + 27 * b * b).mod(p) != 0
  }
}

sealed abstract class ECPoint
case object InfinityPoint extends ECPoint
case class AffinePoint(x: BigInt, y: BigInt) extends ECPoint

object Curve {

  def inField(v: BigInt, p: BigInt): Boolean = 0 <= v && v < p

  /** u mod p as an atom: callers see the range only, redDecomp exposes the quotient. */
  @opaque
  def red(u: BigInt, p: BigInt): BigInt = {
    require(p > 0)
    u.mod(p)
  }.ensuring(r => 0 <= r && r < p)

  /** x^3 + A*x + B with A = a mod p, B = b mod p. */
  def rhs(x: BigInt, c: CurveParams): BigInt = fcub(x, coefA(c), coefB(c))

  /** The coefficients reduced into [0, p) (P-256's a = -3 becomes p - 3); opaque atoms for the solver. */
  @opaque
  def coefA(c: CurveParams): BigInt = c.a.mod(c.p).ensuring(r => 0 <= r && r < c.p)

  @opaque
  def coefB(c: CurveParams): BigInt = c.b.mod(c.p).ensuring(r => 0 <= r && r < c.p)

  /** f(x) = x^3 + a*x + b; opaque so that the closure proofs see it as an atom. */
  @opaque
  def fcub(x: BigInt, a: BigInt, b: BigInt): BigInt = x * x * x + a * x + b

  /** y^2 - f(x): zero modulo p exactly on the curve. */
  @opaque
  def gap(x: BigInt, y: BigInt, a: BigInt, b: BigInt): BigInt = y * y - fcub(x, a, b)

  /** H4 of the chord certificate: l^2*(x2 - x1) + 2*l*y1 - (x2^2 + x1*x2 + x1^2 + a). */
  @opaque
  def h4(x1: BigInt, y1: BigInt, x2: BigInt, l: BigInt, a: BigInt): BigInt =
    l * l * (x2 - x1) + 2 * l * y1 - (x2 * x2 + x1 * x2 + x1 * x1 + a)

  /** H5 of the tangent certificate: 2*l*y - (3*x^2 + a). */
  @opaque
  def h5(x: BigInt, y: BigInt, l: BigInt, a: BigInt): BigInt = 2 * l * y - (3 * x * x + a)

  def isOnCurve(pt: ECPoint, c: CurveParams): Boolean = pt match {
    case InfinityPoint     => true
    case AffinePoint(x, y) => inField(x, c.p) && inField(y, c.p) && sameResidue(x, y, c)
  }

  /** y^2 == x^3 + A*x + B (mod p). Opaque so that a point equality is plain congruence for the solver. */
  @opaque
  def sameResidue(x: BigInt, y: BigInt, c: CurveParams): Boolean = (y * y).mod(c.p) == rhs(x, c).mod(c.p)

  def neg(pt: ECPoint, c: CurveParams): ECPoint = pt match {
    case InfinityPoint     => InfinityPoint
    case AffinePoint(x, y) => AffinePoint(x, if (y == 0) BigInt(0) else c.p - y)
  }

  /** P + Q. P == -Q (vertical line, y == 0 included) gives the point at infinity. */
  def add(pt: ECPoint, qt: ECPoint, c: CurveParams): ECPoint = {
    require(isOnCurve(pt, c) && isOnCurve(qt, c))
    (pt, qt) match {
      case (InfinityPoint, _) => qt
      case (_, InfinityPoint) => pt
      case (AffinePoint(x1, y1), AffinePoint(x2, y2)) =>
        // The chord is always taken from the smaller x, so P + Q and Q + P compute the same thing.
        if (x1 < x2) {
          ghostExpr(chordOnCurve(x1, y1, x2, y2, c))
          chord(x1, y1, x2, y2, c)
        } else if (x2 < x1) {
          ghostExpr(chordOnCurve(x2, y2, x1, y1, c))
          chord(x2, y2, x1, y1, c)
        } else if (y1 == y2) double(pt, c)
        else InfinityPoint // x1 == x2, y1 == -y2 for points on the curve
    }
  }.ensuring(res => isOnCurve(res, c))

  /** [2]P; a point with y == 0 has order 2. */
  def double(pt: ECPoint, c: CurveParams): ECPoint = {
    require(isOnCurve(pt, c))
    pt match {
      case InfinityPoint => InfinityPoint
      case AffinePoint(x, y) =>
        if (y == 0) InfinityPoint
        else {
          ghostExpr(tangentOnCurve(x, y, c))
          tangent(x, y, c)
        }
    }
  }.ensuring(res => isOnCurve(res, c))

  /** n / d mod p for d in (0, p). */
  @opaque
  def slope(n: BigInt, d: BigInt, p: BigInt): BigInt = {
    require(Primes.isPrime(p) && n >= 0 && 0 < d && d < p)
    ghostExpr(Primes.inverseDefined(p, d))
    (n * modInverse(d, p).get).mod(p)
  }.ensuring(l => 0 <= l && l < p)

  def chord(x1: BigInt, y1: BigInt, x2: BigInt, y2: BigInt, c: CurveParams): ECPoint = {
    require(inField(x1, c.p) && inField(y1, c.p) && inField(x2, c.p) && inField(y2, c.p) && x1 < x2)
    val p = c.p
    val l = slope(y2 + p - y1, x2 - x1, p)
    val x3 = red(l * l - x1 - x2 + p * 2, p)
    AffinePoint(x3, red(l * (x1 + p - x3) + p - y1, p))
  }

  def tangent(x: BigInt, y: BigInt, c: CurveParams): ECPoint = {
    require(inField(x, c.p) && 0 < y && y < c.p)
    val p = c.p
    ghostExpr(Primes.primeOdd(p, y))
    val l = slope(3 * x * x + coefA(c), if (2 * y < p) 2 * y else 2 * y - p, p)
    val x3 = red(l * l - 2 * x + p * 2, p)
    AffinePoint(x3, red(l * (x + p - x3) + p - y, p))
  }

  // ──────────────────────────────────────────────────────────────────────────
  // Congruences with explicit quotient witnesses (non-negative dividends only)
  // ──────────────────────────────────────────────────────────────────────────

  /** u >= 0  ==>  u == q*p + u.mod(p) with q = floorDiv(u, p). */
  @ghost @opaque @inlineOnce
  def modDecomp(u: BigInt, p: BigInt): Unit = {
    require(u >= 0 && p > 0)
    modIsFloorMod(u, p)
  }.ensuring(_ => u == floorDiv(u, p) * p + u.mod(p))

  @ghost @opaque @inlineOnce
  def redDecomp(u: BigInt, p: BigInt): Unit = {
    require(u >= 0 && p > 0)
    unfold(red(u, p))
    modDecomp(u, p)
  }.ensuring(_ => u == floorDiv(u, p) * p + red(u, p))

  /** u, v >= 0 with equal residues differ by a multiple of p; returns the multiplier. */
  @ghost @opaque @inlineOnce
  def modEqWitness(u: BigInt, v: BigInt, p: BigInt): BigInt = {
    require(u >= 0 && v >= 0 && p > 0 && u.mod(p) == v.mod(p))
    modDecomp(u, p)
    modDecomp(v, p)
    floorDiv(u, p) - floorDiv(v, p)
  }.ensuring(k => u - v == p * k)

  /** u, v >= 0 and u - v == p*k  ==>  equal residues. */
  @ghost @opaque @inlineOnce
  def witnessModEq(u: BigInt, v: BigInt, p: BigInt, k: BigInt): Unit = {
    require(u >= 0 && v >= 0 && p > 0 && u - v == p * k)
    modDecomp(v, p)
    val q = floorDiv(v, p)
    assert(u == (q + k) * p + v.mod(p))
    modUnique(u, p, q + k, v.mod(p))
  }.ensuring(_ => u.mod(p) == v.mod(p))

  /** Euclid: p prime, 0 < d < p, d*h == p*K  ==>  h == p*k; returns k. */
  @ghost @opaque @inlineOnce
  def cancel(p: BigInt, d: BigInt, h: BigInt, bigK: BigInt): BigInt = {
    require(Primes.isPrime(p) && 0 < d && d < p && d * h == p * bigK)
    Primes.primeCoprime(p, d)
    val w = extendedGcd(d, p)
    assert(w.ka == d && w.kb == p && d * w.x + p * w.y == BigInt(1))
    assert(h == (d * w.x) * h + (p * w.y) * h)
    assert((d * w.x) * h == (d * h) * w.x)
    assert((d * h) * w.x == p * (bigK * w.x))
    assert(h == p * (bigK * w.x) + p * (w.y * h))
    bigK * w.x + h * w.y
  }.ensuring(k => h == p * k)

  /** n*u == n*v for u == v (the caller never rewrites under a product). */
  @ghost @opaque @inlineOnce
  def mulEq(n: BigInt, u: BigInt, v: BigInt): Unit = {
    require(u == v)
  }.ensuring(_ => n * u == n * v)

  /** (n/d) * d == n (mod p): with d*inv == q1*p + 1 and l == n*inv - q2*p, l*d - n == p*(n*q1 - q2*d). */
  @ghost @opaque @inlineOnce
  def slopeSpec(n: BigInt, d: BigInt, p: BigInt): Unit = {
    require(Primes.isPrime(p) && n >= 0 && 0 < d && d < p)
    Primes.inverseDefined(p, d)
    val inv = modInverse(d, p).get
    assert(isInverse(d, p, inv))
    mulNonNeg(d, inv)
    modDecomp(d * inv, p)
    val q1 = floorDiv(d * inv, p)
    mulNonNeg(n, inv)
    modDecomp(n * inv, p)
    val q2 = floorDiv(n * inv, p)
    val l = slope(n, d, p)
    unfold(slope(n, d, p))
    assert(l == n * inv - q2 * p)
    mulEq(n, d * inv, q1 * p + 1)
    assert(l * d - n == p * (n * q1 - q2 * d))
    mulNonNeg(l, d)
    witnessModEq(l * d, n, p, n * q1 - q2 * d)
  }.ensuring(_ => (slope(n, d, p) * d).mod(p) == n.mod(p))

  // ──────────────────────────────────────────────────────────────────────────
  // Polynomial identities. Every lemma takes the composite quantities as
  // parameters tied by `require`, so a caller's context only ever relates
  // atoms (gap(...), products of parameters) and never has to substitute a
  // polynomial inside a product, which is what makes Z3 time out.
  // ──────────────────────────────────────────────────────────────────────────

  @ghost @opaque @inlineOnce
  def fcubNonNeg(x: BigInt, a: BigInt, b: BigInt): Unit = {
    require(x >= 0 && a >= 0 && b >= 0)
    unfold(fcub(x, a, b))
    mulNonNeg(x, x); mulNonNeg(x * x, x); mulNonNeg(a, x)
  }.ensuring(_ => fcub(x, a, b) >= 0)

  @ghost @opaque @inlineOnce
  def gapIs(x: BigInt, y: BigInt, a: BigInt, b: BigInt): Unit = {
    unfold(gap(x, y, a, b))
    unfold(fcub(x, a, b))
  }.ensuring(_ => gap(x, y, a, b) == y * y - (x * x * x + a * x + b))

  /** c*u == c*v for u == p*k, without the caller rewriting under a product. */
  @ghost @opaque @inlineOnce
  def scale(c: BigInt, u: BigInt, p: BigInt, k: BigInt): Unit = {
    require(u == p * k)
  }.ensuring(_ => c * u == p * (c * k))

  /** g == h + t, h == p*k, t == p*e  ==>  g == p*(k + e). */
  @ghost @opaque @inlineOnce
  def sumWitness(g: BigInt, h: BigInt, t: BigInt, p: BigInt, k: BigInt, e: BigInt): Unit = {
    require(g == h + t && h == p * k && t == p * e)
  }.ensuring(_ => g == p * (k + e))

  /** l*(x0 + p - x3) == l*(x0 - xp) + p*(l - l*m3) for x3 == xp + p*m3. */
  @ghost @opaque @inlineOnce
  def lineShift(l: BigInt, x0: BigInt, xp: BigInt, x3: BigInt, m3: BigInt, p: BigInt): Unit = {
    require(x3 == xp + p * m3)
  }.ensuring(_ => l * (x0 + p - x3) == l * (x0 - xp) + p * (l - l * m3))

  @ghost @opaque @inlineOnce
  def h4Is(x1: BigInt, y1: BigInt, x2: BigInt, l: BigInt, a: BigInt): Unit = {
    unfold(h4(x1, y1, x2, l, a))
  }.ensuring(_ => h4(x1, y1, x2, l, a) == l * l * (x2 - x1) + 2 * l * y1 - (x2 * x2 + x1 * x2 + x1 * x1 + a))

  @ghost @opaque @inlineOnce
  def h5Is(x: BigInt, y: BigInt, l: BigInt, a: BigInt): Unit = {
    unfold(h5(x, y, l, a))
  }.ensuring(_ => h5(x, y, l, a) == 2 * l * y - (3 * x * x + a))

  /** l*u == l*v + p*(l*e) for u == v + p*e. */
  @ghost @opaque @inlineOnce
  def mulShift(l: BigInt, u: BigInt, v: BigInt, e: BigInt, p: BigInt): Unit = {
    require(u == v + p * e)
  }.ensuring(_ => l * u == l * v + p * (l * e))

  @ghost @opaque @inlineOnce
  def shiftPoly(x: BigInt, y: BigInt, xs: BigInt, ys: BigInt, m3: BigInt, m4: BigInt, a: BigInt, b: BigInt, p: BigInt): Unit = {
    require(xs == x + p * m3 && ys == y + p * m4)
    assert(xs * xs == x * x + p * (2 * x * m3 + p * m3 * m3))
    assert(xs * xs * xs == (x * x + p * (2 * x * m3 + p * m3 * m3)) * (x + p * m3))
  }.ensuring(_ =>
    ys * ys - (xs * xs * xs + a * xs + b) == (y * y - (x * x * x + a * x + b)) +
      p * (2 * y * m4 + p * m4 * m4 - (3 * x * x * m3 + 3 * x * p * m3 * m3 + p * p * m3 * m3 * m3 + a * m3)))

  /** Shifting a point by multiples of p shifts its gap by a multiple of p; returns the multiplier. */
  @ghost @opaque @inlineOnce
  def shiftGap(x: BigInt, y: BigInt, xs: BigInt, ys: BigInt, m3: BigInt, m4: BigInt, a: BigInt, b: BigInt, p: BigInt): BigInt = {
    require(xs == x + p * m3 && ys == y + p * m4)
    shiftPoly(x, y, xs, ys, m3, m4, a, b, p)
    gapIs(xs, ys, a, b)
    gapIs(x, y, a, b)
    2 * y * m4 + p * m4 * m4 - (3 * x * x * m3 + 3 * x * p * m3 * m3 + p * p * m3 * m3 * m3 + a * m3)
  }.ensuring(e => gap(xs, ys, a, b) == gap(x, y, a, b) + p * e)

  @ghost @opaque @inlineOnce
  def chordDiffPoly(x1: BigInt, y1: BigInt, x2: BigInt, l: BigInt, a: BigInt, b: BigInt, t: BigInt, h: BigInt): Unit = {
    require(t == l * (x2 - x1) + y1 && h == l * l * (x2 - x1) + 2 * l * y1 - (x2 * x2 + x1 * x2 + x1 * x1 + a))
  }.ensuring(_ =>
    (t * t - (x2 * x2 * x2 + a * x2 + b)) - (y1 * y1 - (x1 * x1 * x1 + a * x1 + b)) == (x2 - x1) * h)

  /** gap(x2, l*(x2 - x1) + y1) - gap(x1, y1) == (x2 - x1) * H4 */
  @ghost @opaque @inlineOnce
  def chordDiff(x1: BigInt, y1: BigInt, x2: BigInt, l: BigInt, a: BigInt, b: BigInt, t: BigInt, h: BigInt): Unit = {
    require(t == l * (x2 - x1) + y1 && h == l * l * (x2 - x1) + 2 * l * y1 - (x2 * x2 + x1 * x2 + x1 * x1 + a))
    chordDiffPoly(x1, y1, x2, l, a, b, t, h)
    gapIs(x2, t, a, b)
    gapIs(x1, y1, a, b)
  }.ensuring(_ => gap(x2, t, a, b) - gap(x1, y1, a, b) == (x2 - x1) * h)

  @ghost @opaque @inlineOnce
  def chordCertPoly(x1: BigInt, y1: BigInt, x2: BigInt, l: BigInt, a: BigInt, b: BigInt, x3: BigInt, y3: BigInt, h: BigInt): Unit = {
    require(x3 == l * l - x1 - x2 && y3 == l * (x1 - x3) - y1 &&
      h == l * l * (x2 - x1) + 2 * l * y1 - (x2 * x2 + x1 * x2 + x1 * x1 + a))
  }.ensuring(_ =>
    y3 * y3 - (x3 * x3 * x3 + a * x3 + b) == (y1 * y1 - (x1 * x1 * x1 + a * x1 + b)) + (l * l - 2 * x1 - x2) * h)

  /** Groebner certificate of the chord: G == H1 + (l^2 - 2*x1 - x2) * H4. */
  @ghost @opaque @inlineOnce
  def chordCert(x1: BigInt, y1: BigInt, x2: BigInt, l: BigInt, a: BigInt, b: BigInt, x3: BigInt, y3: BigInt, h: BigInt): Unit = {
    require(x3 == l * l - x1 - x2 && y3 == l * (x1 - x3) - y1 &&
      h == l * l * (x2 - x1) + 2 * l * y1 - (x2 * x2 + x1 * x2 + x1 * x1 + a))
    chordCertPoly(x1, y1, x2, l, a, b, x3, y3, h)
    gapIs(x3, y3, a, b)
    gapIs(x1, y1, a, b)
  }.ensuring(_ => gap(x3, y3, a, b) == gap(x1, y1, a, b) + (l * l - 2 * x1 - x2) * h)

  @ghost @opaque @inlineOnce
  def tangentCertPoly(x: BigInt, y: BigInt, l: BigInt, a: BigInt, b: BigInt, x3: BigInt, y3: BigInt, h: BigInt): Unit = {
    require(x3 == l * l - 2 * x && y3 == l * (x - x3) - y && h == 2 * l * y - (3 * x * x + a))
  }.ensuring(_ =>
    y3 * y3 - (x3 * x3 * x3 + a * x3 + b) == (y * y - (x * x * x + a * x + b)) + (l * l - 3 * x) * h)

  /** Groebner certificate of the tangent: G == H1 + (l^2 - 3*x) * H5. */
  @ghost @opaque @inlineOnce
  def tangentCert(x: BigInt, y: BigInt, l: BigInt, a: BigInt, b: BigInt, x3: BigInt, y3: BigInt, h: BigInt): Unit = {
    require(x3 == l * l - 2 * x && y3 == l * (x - x3) - y && h == 2 * l * y - (3 * x * x + a))
    tangentCertPoly(x, y, l, a, b, x3, y3, h)
    gapIs(x3, y3, a, b)
    gapIs(x, y, a, b)
  }.ensuring(_ => gap(x3, y3, a, b) == gap(x, y, a, b) + (l * l - 3 * x) * h)

  // ──────────────────────────────────────────────────────────────────────────
  // Closure
  // ──────────────────────────────────────────────────────────────────────────

  /** On the curve as a witness: gap(x, y) == p*k. */
  @ghost @opaque @inlineOnce
  def onCurveWitness(x: BigInt, y: BigInt, c: CurveParams): BigInt = {
    require(isOnCurve(AffinePoint(x, y), c))
    val (a, b) = (coefA(c), coefB(c))
    unfold(sameResidue(x, y, c))
    mulNonNeg(y, y)
    fcubNonNeg(x, a, b)
    val k = modEqWitness(y * y, fcub(x, a, b), c.p)
    unfold(gap(x, y, a, b))
    k
  }.ensuring(k => gap(x, y, coefA(c), coefB(c)) == c.p * k)

  /** gap == p*k  ==>  the residues of y^2 and f(x) agree, i.e. the reduced point is on the curve. */
  @ghost @opaque @inlineOnce
  def witnessOnCurve(x: BigInt, y: BigInt, k: BigInt, c: CurveParams): Unit = {
    require(inField(x, c.p) && inField(y, c.p) && gap(x, y, coefA(c), coefB(c)) == c.p * k)
    val (a, b) = (coefA(c), coefB(c))
    unfold(gap(x, y, a, b))
    mulNonNeg(y, y)
    fcubNonNeg(x, a, b)
    witnessModEq(y * y, fcub(x, a, b), c.p, k)
    unfold(sameResidue(x, y, c))
  }.ensuring(_ => isOnCurve(AffinePoint(x, y), c))

  /** The reduced coordinates differ from (x', y') by multiples of p: returns (m3, m4). */
  @ghost @opaque @inlineOnce
  def reduceShift(xp: BigInt, yp: BigInt, l: BigInt, x0: BigInt, y0: BigInt, s: BigInt, p: BigInt): (BigInt, BigInt) = {
    require(p > 0 && inField(x0, p) && inField(y0, p) && l >= 0 && xp + p * s >= 0 && yp == l * (x0 - xp) - y0)
    val u = xp + p * s
    val x3 = red(u, p)
    redDecomp(u, p)
    val m3 = s - floorDiv(u, p)
    assert(x3 == xp + p * m3)
    val t = x0 + p - x3
    mulNonNeg(l, t)
    val w = l * t + p - y0
    redDecomp(w, p)
    lineShift(l, x0, xp, x3, m3, p)
    (m3, l + 1 - l * m3 - floorDiv(w, p))
  }.ensuring(res => {
    val x3 = red(xp + p * s, p)
    x3 == xp + p * res._1 && red(l * (x0 + p - x3) + p - y0, p) == yp + p * res._2
  })

  /**
   * gap(x', y') == p*k with y' == l*(x0 - x'): for the point reduced into [0, p),
   * x3 = (x' + p*s).mod(p), y3 = (l*(x0 + p - x3) + p - y0).mod(p), returns K with gap(x3, y3) == p*K.
   */
  @ghost @opaque @inlineOnce
  def reduceWitness(xp: BigInt, yp: BigInt, l: BigInt, x0: BigInt, y0: BigInt, s: BigInt, k: BigInt, c: CurveParams): BigInt = {
    require(inField(x0, c.p) && inField(y0, c.p) && l >= 0 && xp + c.p * s >= 0 &&
      yp == l * (x0 - xp) - y0 && gap(xp, yp, coefA(c), coefB(c)) == c.p * k)
    val p = c.p
    val x3 = red(xp + p * s, p)
    val y3 = red(l * (x0 + p - x3) + p - y0, p)
    val (m3, m4) = reduceShift(xp, yp, l, x0, y0, s, p)
    val e = shiftGap(xp, yp, x3, y3, m3, m4, coefA(c), coefB(c), p)
    sumWitness(gap(x3, y3, coefA(c), coefB(c)), gap(xp, yp, coefA(c), coefB(c)), p * e, p, k, e)
    k + e
  }.ensuring(bigK => {
    val x3 = red(xp + c.p * s, c.p)
    gap(x3, red(l * (x0 + c.p - x3) + c.p - y0, c.p), coefA(c), coefB(c)) == c.p * bigK
  })

  @ghost @opaque @inlineOnce
  def reduceOnCurve(xp: BigInt, yp: BigInt, l: BigInt, x0: BigInt, y0: BigInt, s: BigInt, k: BigInt, c: CurveParams): Unit = {
    require(inField(x0, c.p) && inField(y0, c.p) && l >= 0 && xp + c.p * s >= 0 &&
      yp == l * (x0 - xp) - y0 && gap(xp, yp, coefA(c), coefB(c)) == c.p * k)
    val x3 = red(xp + c.p * s, c.p)
    val y3 = red(l * (x0 + c.p - x3) + c.p - y0, c.p)
    witnessOnCurve(x3, y3, reduceWitness(xp, yp, l, x0, y0, s, k, c), c)
  }.ensuring(_ => {
    val x3 = red(xp + c.p * s, c.p)
    isOnCurve(AffinePoint(x3, red(l * (x0 + c.p - x3) + c.p - y0, c.p)), c)
  })

  /** l*d == n (mod p) as a witness. */
  @ghost @opaque @inlineOnce
  def slopeWitness(n: BigInt, d: BigInt, p: BigInt): BigInt = {
    require(Primes.isPrime(p) && n >= 0 && 0 < d && d < p)
    slopeSpec(n, d, p)
    mulNonNeg(slope(n, d, p), d)
    modEqWitness(slope(n, d, p) * d, n, p)
  }.ensuring(k => slope(n, d, p) * d - n == p * k)

  /** H4 of the chord through two points on the curve is a multiple of p (the one cancellation). */
  @ghost @opaque @inlineOnce
  def chordH4(x1: BigInt, y1: BigInt, x2: BigInt, y2: BigInt, c: CurveParams): BigInt = {
    require(isOnCurve(AffinePoint(x1, y1), c) && isOnCurve(AffinePoint(x2, y2), c) && x1 < x2)
    val p = c.p
    val (a, b) = (coefA(c), coefB(c))
    val d = x2 - x1
    val l = slope(y2 + p - y1, d, p)
    // H3: t := l*d + y1 == y2 + p*k3
    val k3 = slopeWitness(y2 + p - y1, d, p) + 1
    val t = l * d + y1
    assert(t == y2 + p * k3)
    // gap(x2, t) == p*(k2 + e2)
    val k1 = onCurveWitness(x1, y1, c)
    val k2 = onCurveWitness(x2, y2, c)
    val e2 = shiftGap(x2, y2, x2, t, BigInt(0), k3, a, b, p)
    // d*H4 == gap(x2, t) - gap(x1, y1) == p*(k2 + e2 - k1)
    val h = h4(x1, y1, x2, l, a)
    h4Is(x1, y1, x2, l, a)
    chordDiff(x1, y1, x2, l, a, b, t, h)
    cancel(p, d, h, k2 + e2 - k1)
  }.ensuring(k4 => h4(x1, y1, x2, slope(y2 + c.p - y1, x2 - x1, c.p), coefA(c)) == c.p * k4)

  @ghost @opaque @inlineOnce
  def chordOnCurve(x1: BigInt, y1: BigInt, x2: BigInt, y2: BigInt, c: CurveParams): Unit = {
    require(isOnCurve(AffinePoint(x1, y1), c) && isOnCurve(AffinePoint(x2, y2), c) && x1 < x2)
    chordOnCurveCore(x1, y1, x2, y2, c)
  }.ensuring(_ => isOnCurve(chord(x1, y1, x2, y2, c), c))

  @ghost @opaque @inlineOnce
  def chordOnCurveCore(x1: BigInt, y1: BigInt, x2: BigInt, y2: BigInt, c: CurveParams): Unit = {
    require(isOnCurve(AffinePoint(x1, y1), c) && isOnCurve(AffinePoint(x2, y2), c) && x1 < x2)
    val p = c.p
    val (a, b) = (coefA(c), coefB(c))
    val l = slope(y2 + p - y1, x2 - x1, p)
    val h = h4(x1, y1, x2, l, a)
    val k4 = chordH4(x1, y1, x2, y2, c)
    val k1 = onCurveWitness(x1, y1, c)
    // G == H1 + cf*H4 == p*(k1 + cf*k4)
    val xp = l * l - x1 - x2
    val yp = l * (x1 - xp) - y1
    val cf = l * l - 2 * x1 - x2
    h4Is(x1, y1, x2, l, a)
    chordCert(x1, y1, x2, l, a, b, xp, yp, h)
    scale(cf, h, p, k4)
    sumWitness(gap(xp, yp, a, b), gap(x1, y1, a, b), cf * h, p, k1, cf * k4)
    mulNonNeg(l, l)
    reduceOnCurve(xp, yp, l, x1, y1, BigInt(2), k1 + cf * k4, c)
  }.ensuring(_ => {
    val l = slope(y2 + c.p - y1, x2 - x1, c.p)
    val x3 = red(l * l - x1 - x2 + c.p * 2, c.p)
    isOnCurve(AffinePoint(x3, red(l * (x1 + c.p - x3) + c.p - y1, c.p)), c)
  })

  /** H5 of the tangent at a point with y != 0 is a multiple of p. */
  @ghost @opaque @inlineOnce
  def tangentH5(x: BigInt, y: BigInt, c: CurveParams): BigInt = {
    require(inField(x, c.p) && 0 < y && y < c.p)
    val p = c.p
    val a = coefA(c)
    Primes.primeOdd(p, y)
    mulNonNeg(x, x)
    val n = 3 * x * x + a
    val d = if (2 * y < p) 2 * y else 2 * y - p
    val e = if (2 * y < p) BigInt(0) else BigInt(1)
    val l = slope(n, d, p)
    val k = slopeWitness(n, d, p)
    mulShift(l, 2 * y, d, e, p)
    h5Is(x, y, l, a)
    k + l * e
  }.ensuring(k5 => {
    val p = c.p
    val d = if (2 * y < p) 2 * y else 2 * y - p
    h5(x, y, slope(3 * x * x + coefA(c), d, p), coefA(c)) == p * k5
  })

  @ghost @opaque @inlineOnce
  def tangentOnCurve(x: BigInt, y: BigInt, c: CurveParams): Unit = {
    require(isOnCurve(AffinePoint(x, y), c) && y != 0)
    tangentOnCurveCore(x, y, c)
  }.ensuring(_ => isOnCurve(tangent(x, y, c), c))

  @ghost @opaque @inlineOnce
  def tangentOnCurveCore(x: BigInt, y: BigInt, c: CurveParams): Unit = {
    require(isOnCurve(AffinePoint(x, y), c) && y != 0)
    val p = c.p
    val (a, b) = (coefA(c), coefB(c))
    Primes.primeOdd(p, y)
    mulNonNeg(x, x)
    val d = if (2 * y < p) 2 * y else 2 * y - p
    val l = slope(3 * x * x + a, d, p)
    val h = h5(x, y, l, a)
    val k5 = tangentH5(x, y, c)
    val k1 = onCurveWitness(x, y, c)
    val xp = l * l - 2 * x
    val yp = l * (x - xp) - y
    val cf = l * l - 3 * x
    h5Is(x, y, l, a)
    tangentCert(x, y, l, a, b, xp, yp, h)
    scale(cf, h, p, k5)
    sumWitness(gap(xp, yp, a, b), gap(x, y, a, b), cf * h, p, k1, cf * k5)
    mulNonNeg(l, l)
    reduceOnCurve(xp, yp, l, x, y, BigInt(2), k1 + cf * k5, c)
  }.ensuring(_ => {
    val p = c.p
    val l = slope(3 * x * x + coefA(c), if (2 * y < p) 2 * y else 2 * y - p, p)
    val x3 = red(l * l - 2 * x + p * 2, p)
    isOnCurve(AffinePoint(x3, red(l * (x + p - x3) + p - y, p)), c)
  })

  // ──────────────────────────────────────────────────────────────────────────
  // Group laws (associativity is TCB T3, not proved here)
  // ──────────────────────────────────────────────────────────────────────────

  @ghost @opaque @inlineOnce
  def negOnCurve(pt: ECPoint, c: CurveParams): Unit = {
    require(isOnCurve(pt, c))
    pt match {
      case InfinityPoint => ()
      case AffinePoint(x, y) =>
        if (y != 0) {
          val p = c.p
          assert((p - y) * (p - y) - y * y == p * (p - 2 * y))
          mulNonNeg(p - y, p - y); mulNonNeg(y, y)
          witnessModEq((p - y) * (p - y), y * y, p, p - 2 * y)
          unfold(sameResidue(x, y, c))
          unfold(sameResidue(x, p - y, c))
        }
    }
  }.ensuring(_ => isOnCurve(neg(pt, c), c))

  @ghost @opaque @inlineOnce
  def addIdentity(pt: ECPoint, c: CurveParams): Unit = {
    require(isOnCurve(pt, c))
  }.ensuring(_ => add(pt, InfinityPoint, c) == pt && add(InfinityPoint, pt, c) == pt)

  @ghost @opaque @inlineOnce
  def addComm(pt: ECPoint, qt: ECPoint, c: CurveParams): Unit = {
    require(isOnCurve(pt, c) && isOnCurve(qt, c))
  }.ensuring(_ => add(pt, qt, c) == add(qt, pt, c))

  /** P + (-P) == O, including the points of order 2 (y == 0). */
  @ghost @opaque @inlineOnce
  def addNeg(pt: ECPoint, c: CurveParams): Unit = {
    require(isOnCurve(pt, c))
    negOnCurve(pt, c)
    pt match {
      case InfinityPoint => ()
      case AffinePoint(x, y) => if (y != 0) Primes.primeOdd(c.p, y)
    }
  }.ensuring(_ => isOnCurve(neg(pt, c), c) && add(pt, neg(pt, c), c) == InfinityPoint)

  /** A point of order 2: [2]P == O. */
  @ghost @opaque @inlineOnce
  def doubleOrderTwo(x: BigInt, c: CurveParams): Unit = {
    require(isOnCurve(AffinePoint(x, BigInt(0)), c))
  }.ensuring(_ => double(AffinePoint(x, BigInt(0)), c) == InfinityPoint &&
    add(AffinePoint(x, BigInt(0)), AffinePoint(x, BigInt(0)), c) == InfinityPoint)
}
