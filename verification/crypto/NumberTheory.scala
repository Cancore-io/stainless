package crypto

import stainless.lang.{ghost => ghostExpr, _}
import stainless.lang.StaticChecks._
import stainless.annotation._
import stainless.math.NonLinear._

/**
 * Elementary number theory on BigInt (SPEC.md §4 PR 3): extended gcd with
 * divisibility witnesses, modular inverse, modular exponentiation, CRT.
 *
 * Rules (SPEC §3.4): contracts never use `/` or `%` on a symbolic modulus;
 * divisibility is stated with witness cofactors. `BigInt.mod` appears in a
 * contract only on a dividend proved non-negative: relating `mod` of a
 * negative dividend to its Euclidean quotient is not decided by the solvers
 * within the budget (SPEC §8 T2), so intermediate any-sign residues use
 * `floorMod` (stainless.math.NonLinear), which is proved.
 *
 * StaticChecks makes `require`/`ensuring`/`assert` no-ops on the JVM, so the
 * executable code never evaluates the `pow` specification.
 */
object NumberTheory {

  /** gcd > 0 with a == ka*gcd, b == kb*gcd and the Bezout pair ka*x + kb*y == 1 on the cofactors. */
  case class GcdWitness(gcd: BigInt, ka: BigInt, kb: BigInt, x: BigInt, y: BigInt)

  // ──────────────────────────────────────────────────────────────────────────
  // Extended Euclid (proof steps after bolts algorithms/extended-gcd/MoreExtendedEuclidGCD.scala)
  // ──────────────────────────────────────────────────────────────────────────

  def extendedGcd(a: BigInt, b: BigInt): GcdWitness = {
    require(a >= 0 && b >= 0 && (a > 0 || b > 0))
    decreases(b)
    if (b == 0) GcdWitness(a, BigInt(1), BigInt(0), BigInt(1), BigInt(0))
    else {
      // a >= 0, b > 0: truncating / and % are the Euclidean quotient and remainder here.
      val q = a / b
      val r = a % b
      assert(a == b * q + r && 0 <= r && r < b)
      val w = extendedGcd(b, r)
      val g = w.gcd
      // b == w.ka*g and r == w.kb*g, so a == (w.ka*q + w.kb)*g.
      val ka = w.ka * q + w.kb
      assert(a == w.ka * g * q + w.kb * g)
      assert(a == ka * g)
      // w.ka*w.x + w.kb*w.y == 1 with w.kb == ka - w.ka*q.
      assert(w.ka * w.x + (ka - w.ka * q) * w.y == BigInt(1))
      assert(ka * w.y + w.ka * (w.x - q * w.y) == BigInt(1))
      GcdWitness(g, ka, w.ka, w.y, w.x - q * w.y)
    }
  }.ensuring(res =>
    res.gcd > 0 &&
    a == res.ka * res.gcd && b == res.kb * res.gcd &&
    res.ka * res.x + res.kb * res.y == BigInt(1))

  /** Bezout on the operands: a*x + b*y == gcd. */
  @ghost @opaque @inlineOnce
  def bezout(a: BigInt, b: BigInt, w: GcdWitness): Unit = {
    require(a == w.ka * w.gcd && b == w.kb * w.gcd && w.ka * w.x + w.kb * w.y == BigInt(1))
    assert(w.gcd * (w.ka * w.x) + w.gcd * (w.kb * w.y) == w.gcd)
  }.ensuring(_ => a * w.x + b * w.y == w.gcd)

  /** The gcd is the greatest common divisor: any d dividing a and b (witnesses da, db) divides it, so d <= gcd. */
  @ghost @opaque @inlineOnce
  def gcdIsGreatest(a: BigInt, b: BigInt, w: GcdWitness, d: BigInt, da: BigInt, db: BigInt): Unit = {
    require(w.gcd > 0 && a == w.ka * w.gcd && b == w.kb * w.gcd && w.ka * w.x + w.kb * w.y == BigInt(1) &&
      a == da * d && b == db * d)
    bezout(a, b, w)
    val k = da * w.x + db * w.y
    assert(a * w.x + b * w.y == k * d)
    assert(w.gcd == k * d)
    if (d > 0) {
      // k*d == gcd > 0 with d > 0 forces k >= 1, hence gcd >= d.
      if (k <= 0) mulMonoLeft(k, BigInt(0), d)
      mulMonoLeft(BigInt(1), k, d)
    }
  }.ensuring(_ => d <= w.gcd && w.gcd == (da * w.x + db * w.y) * d)

  /** g > 0 and g*k == 1 force g == 1. */
  @ghost @opaque @inlineOnce
  def unitFactor(g: BigInt, k: BigInt): Unit = {
    require(g > 0 && g * k == BigInt(1))
    if (k <= 0) mulMonoLeft(k, BigInt(0), g)
    else mulMonoLeft(BigInt(1), k, g)
  }.ensuring(_ => g == BigInt(1))

  // ──────────────────────────────────────────────────────────────────────────
  // Modular inverse
  // ──────────────────────────────────────────────────────────────────────────

  /** r in [0, m) inverts a modulo m; for a >= 0 also stated on a itself. */
  def isInverse(a: BigInt, m: BigInt, r: BigInt): Boolean = {
    require(m > 1)
    0 <= r && r < m && (a.mod(m) * r).mod(m) == BigInt(1) && (a >= 0 ==> ((a * r).mod(m) == BigInt(1)))
  }

  /** Some(r) with r in [0, m) and a*r == 1 (mod m) iff gcd(a mod m, m) == 1. */
  def modInverse(a: BigInt, m: BigInt): Option[BigInt] = {
    require(m > 1)
    val a0 = a.mod(m)
    val w = extendedGcd(a0, m)
    if (w.gcd != BigInt(1)) None[BigInt]()
    else {
      val r = floorMod(w.x, m)
      ghostExpr(inverseCorrect(a, m, w, r))
      Some(r)
    }
  }.ensuring(res => res.forall(r => isInverse(a, m, r)))

  @ghost @opaque @inlineOnce
  def inverseCorrect(a: BigInt, m: BigInt, w: GcdWitness, r: BigInt): Unit = {
    require(m > 1 && w.gcd == BigInt(1) && a.mod(m) == w.ka && m == w.kb &&
      w.ka * w.x + w.kb * w.y == BigInt(1) && r == floorMod(w.x, m))
    val a0 = a.mod(m)
    val qx = floorDiv(w.x, m)
    assert(r == w.x - qx * m)
    // a0*r == a0*x - a0*qx*m == 1 + (-y - a0*qx)*m
    val k = -w.y - a0 * qx
    assert(a0 * r == a0 * w.x - a0 * qx * m)
    assert(a0 * r == k * m + 1)
    mulNonNeg(a0, r)
    modUnique(a0 * r, m, k, BigInt(1))
    if (a >= 0) {
      // a == qa*m + a0, so a*r == (k + qa*r)*m + 1.
      modIsFloorMod(a, m)
      val qa = floorDiv(a, m)
      assert(a == qa * m + a0)
      assert(a * r == qa * r * m + a0 * r)
      assert(a * r == (k + qa * r) * m + 1)
      mulNonNeg(a, r)
      modUnique(a * r, m, k + qa * r, BigInt(1))
    }
  }.ensuring(_ => isInverse(a, m, r))

  /** Completeness: if some r in [0, m) inverts a mod m, modInverse finds one. */
  @ghost @opaque @inlineOnce
  def modInverseComplete(a: BigInt, m: BigInt, r: BigInt): Unit = {
    require(m > 1 && 0 <= r && (a.mod(m) * r).mod(m) == BigInt(1))
    val a0 = a.mod(m)
    val w = extendedGcd(a0, m)
    val p = a0 * r
    mulNonNeg(a0, r)
    modIsFloorMod(p, m)
    val d = floorDiv(p, m)
    assert(p == d * m + 1)
    // ka*g*r == d*kb*g + 1, i.e. g*(ka*r - d*kb) == 1.
    assert(w.ka * w.gcd * r == d * w.kb * w.gcd + 1)
    assert(w.gcd * (w.ka * r - d * w.kb) == BigInt(1))
    unitFactor(w.gcd, w.ka * r - d * w.kb)
  }.ensuring(_ => extendedGcd(a.mod(m), m).gcd == BigInt(1))

  /** ... so modInverse returns Some. */
  @ghost @opaque @inlineOnce
  def modInverseDefined(a: BigInt, m: BigInt, r: BigInt): Unit = {
    require(m > 1 && 0 <= r && (a.mod(m) * r).mod(m) == BigInt(1))
    modInverseComplete(a, m, r)
  }.ensuring(_ => modInverse(a, m).isDefined)

  // ──────────────────────────────────────────────────────────────────────────
  // Modular exponentiation
  // ──────────────────────────────────────────────────────────────────────────

  /** Specification: b^e for e >= 0. */
  def pow(b: BigInt, e: BigInt): BigInt = {
    require(e >= 0)
    decreases(e)
    if (e == 0) BigInt(1) else b * pow(b, e - 1)
  }

  @ghost @opaque @inlineOnce
  def powNonNeg(b: BigInt, e: BigInt): Unit = {
    require(b >= 0 && e >= 0)
    decreases(e)
    if (e > 0) {
      powNonNeg(b, e - 1)
      mulNonNeg(b, pow(b, e - 1))
    }
  }.ensuring(_ => pow(b, e) >= 0)

  /** b^(i+j) == b^i * b^j */
  @ghost @opaque @inlineOnce
  def powAdd(b: BigInt, i: BigInt, j: BigInt): Unit = {
    require(i >= 0 && j >= 0)
    decreases(j)
    if (j > 0) {
      powAdd(b, i, j - 1)
      assert(pow(b, i + j) == b * pow(b, i + j - 1))
      assert(pow(b, i + j) == b * (pow(b, i) * pow(b, j - 1)))
      assert(pow(b, i + j) == pow(b, i) * (b * pow(b, j - 1)))
    }
  }.ensuring(_ => pow(b, i + j) == pow(b, i) * pow(b, j))

  /** Square-and-multiply: b^e mod m with O(log e) multiplications. Opaque: callers use the contract. */
  @opaque
  def modPow(b: BigInt, e: BigInt, m: BigInt): BigInt = {
    require(b >= 0 && e >= 0 && m > 0)
    decreases(e)
    if (e == 0) BigInt(1).mod(m)
    else {
      val k = e / 2
      val h = modPow(b, k, m)
      val sq = (h * h).mod(m)
      if (e == 2 * k) {
        ghostExpr(modPowEven(b, k, m, h))
        sq
      } else {
        assert(e == 2 * k + 1)
        ghostExpr(modPowOdd(b, k, m, h))
        (sq * b.mod(m)).mod(m)
      }
    }
  }.ensuring(res => res == pow(b, e).mod(m))

  /** h == b^k mod m  ==>  h^2 mod m == b^(2k) mod m */
  @ghost @opaque @inlineOnce
  def modPowEven(b: BigInt, k: BigInt, m: BigInt, h: BigInt): Unit = {
    require(b >= 0 && k >= 0 && m > 0 && h == pow(b, k).mod(m))
    val p = pow(b, k)
    powNonNeg(b, k)
    powAdd(b, k, k)
    modMul(p, p, m)
  }.ensuring(_ => (h * h).mod(m) == pow(b, 2 * k).mod(m))

  /** h == b^k mod m  ==>  (h^2 mod m) * (b mod m) mod m == b^(2k+1) mod m */
  @ghost @opaque @inlineOnce
  def modPowOdd(b: BigInt, k: BigInt, m: BigInt, h: BigInt): Unit = {
    require(b >= 0 && k >= 0 && m > 0 && h == pow(b, k).mod(m))
    val p = pow(b, k)
    powNonNeg(b, k)
    powAdd(b, k, k)
    modMul(p, p, m)
    val pp = p * p
    mulNonNeg(p, p)
    assert(pow(b, 2 * k + 1) == b * pp)
    modMul(pp, b, m)
    assert((pp * b).mod(m) == ((h * h).mod(m) * b.mod(m)).mod(m))
  }.ensuring(_ => ((h * h).mod(m) * b.mod(m)).mod(m) == pow(b, 2 * k + 1).mod(m))

  // ──────────────────────────────────────────────────────────────────────────
  // Chinese remainder theorem, two coprime moduli
  // ──────────────────────────────────────────────────────────────────────────

  /** Some(x) with x in [0, m1*m2), x == r1 (mod m1), x == r2 (mod m2) iff gcd(m1, m2) == 1 (Garner's form). */
  def crt(r1: BigInt, m1: BigInt, r2: BigInt, m2: BigInt): Option[BigInt] = {
    require(m1 > 0 && m2 > 0 && 0 <= r1 && r1 < m1 && 0 <= r2 && r2 < m2)
    val w = extendedGcd(m1, m2)
    if (w.gcd != BigInt(1)) None[BigInt]()
    else {
      val t = floorMod((r2 - r1) * w.x, m2)
      val x = r1 + m1 * t
      ghostExpr(crtCorrect(r1, m1, r2, m2, w, t))
      Some(x)
    }
  }.ensuring(res => res.forall(x =>
    0 <= x && x < m1 * m2 && x.mod(m1) == r1 && x.mod(m2) == r2))

  @ghost @opaque @inlineOnce
  def crtCorrect(r1: BigInt, m1: BigInt, r2: BigInt, m2: BigInt, w: GcdWitness, t: BigInt): Unit = {
    require(m1 > 0 && m2 > 0 && 0 <= r1 && r1 < m1 && 0 <= r2 && r2 < m2 &&
      w.gcd == BigInt(1) && m1 == w.ka && m2 == w.kb && w.ka * w.x + w.kb * w.y == BigInt(1) &&
      t == floorMod((r2 - r1) * w.x, m2))
    val x = r1 + m1 * t
    // Range: 0 <= m1*t <= m1*(m2 - 1).
    mulBounded(m1, m1, t, m2 - 1)
    assert(m1 * (m2 - 1) == m1 * m2 - m1)
    // x mod m1 == r1.
    assert(x == t * m1 + r1)
    modUnique(x, m1, t, r1)
    // x mod m2 == r2: with q = floorDiv((r2 - r1)*u, m2) and m1*u == 1 - m2*v,
    // x == r1 + (r2 - r1)*(1 - m2*v) - m1*q*m2 == (-(r2 - r1)*v - m1*q)*m2 + r2.
    val s = (r2 - r1) * w.x
    val q = floorDiv(s, m2)
    assert(t == s - q * m2)
    assert(m1 * t == m1 * s - m1 * q * m2)
    assert(m1 * s == (r2 - r1) * (m1 * w.x))
    assert(m1 * w.x == 1 - m2 * w.y)
    assert(m1 * s == (r2 - r1) - (r2 - r1) * w.y * m2)
    val k = -(r2 - r1) * w.y - m1 * q
    assert(x == k * m2 + r2)
    modUnique(x, m2, k, r2)
  }.ensuring(_ => {
    val x = r1 + m1 * t
    0 <= x && x < m1 * m2 && x.mod(m1) == r1 && x.mod(m2) == r2
  })
}
