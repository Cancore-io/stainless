package crypto

import stainless.lang.{ghost => ghostExpr, _}
import stainless.lang.StaticChecks._
import stainless.annotation._
import stainless.math.NonLinear._
import crypto.NumberTheory._

/**
 * The prime field GF(p) (SPEC.md §4 PR 4): a field element carries its
 * invariant 0 <= v < p, every operation is closed, and the field laws are
 * lemmas. Primality of p is a precondition (Primes.isPrime) only where it is
 * needed, i.e. for the multiplicative inverse; for the concrete curve
 * constants it is supplied by the Pratt certificates of PR 6 (TCB T4 until then).
 */
case class FieldElem(v: BigInt, p: BigInt) {
  require(p > 1 && 0 <= v && v < p)

  def +(that: FieldElem): FieldElem = {
    require(p == that.p)
    val s = v + that.v
    FieldElem(if (s >= p) s - p else s, p)
  }

  def unary_- : FieldElem = FieldElem(if (v == 0) BigInt(0) else p - v, p)

  def -(that: FieldElem): FieldElem = {
    require(p == that.p)
    this + (-that)
  }

  def *(that: FieldElem): FieldElem = {
    require(p == that.p)
    FieldElem((v * that.v).mod(p), p)
  }

  def inverse: FieldElem = {
    require(v != 0 && Primes.isPrime(p))
    ghostExpr(Primes.inverseDefined(p, v))
    FieldElem(modInverse(v, p).get, p)
  }.ensuring(res => (v * res.v).mod(p) == BigInt(1))

  def /(that: FieldElem): FieldElem = {
    require(p == that.p && that.v != 0 && Primes.isPrime(p))
    this * that.inverse
  }
}

object FieldElem {
  def zero(p: BigInt): FieldElem = { require(p > 1); FieldElem(BigInt(0), p) }
  def one(p: BigInt): FieldElem = { require(p > 1); FieldElem(BigInt(1), p) }

  /** The residue of any integer, negative ones included. */
  def of(n: BigInt, p: BigInt): FieldElem = { require(p > 1); FieldElem(n.mod(p), p) }
}

object Primes {

  /** No divisor in [2, d] (spec; executable only for small p). */
  def noDivisorUpTo(p: BigInt, d: BigInt): Boolean = {
    require(d >= 1)
    decreases(d)
    d == 1 || (p.mod(d) != 0 && noDivisorUpTo(p, d - 1))
  }

  /** p is prime: p > 1 with no divisor in [2, p - 1]. */
  def isPrime(p: BigInt): Boolean = p > 1 && noDivisorUpTo(p, p - 1)

  /** A factorisation p == g*k with 2 <= g <= d contradicts noDivisorUpTo(p, d). */
  @ghost @opaque @inlineOnce
  def noFactorBelow(p: BigInt, d: BigInt, g: BigInt, k: BigInt): Unit = {
    require(p >= 0 && d >= 1 && noDivisorUpTo(p, d) && 2 <= g && g <= d && p == g * k)
    decreases(d)
    if (g == d) modUnique(p, g, k, BigInt(0))
    else noFactorBelow(p, d - 1, g, k)
  }.ensuring(_ => false)

  /** A prime p is coprime to every v in (0, p). */
  @ghost @opaque @inlineOnce
  def primeCoprime(p: BigInt, v: BigInt): Unit = {
    require(isPrime(p) && 0 < v && v < p)
    val w = extendedGcd(v, p)
    val g = w.gcd
    // p == kb*g and v == ka*g with g > 0, so kb >= 1 and g <= p.
    if (w.kb <= 0) mulMonoLeft(w.kb, BigInt(0), g)
    mulMonoLeft(BigInt(1), w.kb, g)
    if (g == p) {
      // v == ka*p in (0, p) is impossible.
      if (w.ka <= 0) mulMonoLeft(w.ka, BigInt(0), p)
      else mulMonoLeft(BigInt(1), w.ka, p)
    } else if (g > 1) noFactorBelow(p, p - 1, g, w.kb)
  }.ensuring(_ => extendedGcd(v, p).gcd == BigInt(1))

  /** ... hence modInverse(v, p) is defined. */
  @ghost @opaque @inlineOnce
  def inverseDefined(p: BigInt, v: BigInt): Unit = {
    require(isPrime(p) && 0 < v && v < p)
    primeCoprime(p, v)
    modUnique(v, p, BigInt(0), v)
  }.ensuring(_ => modInverse(v, p).isDefined)
}

/** Field laws of GF(p). */
object FieldLaws {
  import FieldElem._

  @ghost @opaque @inlineOnce
  def addZero(x: FieldElem): Unit = {
    ()
  }.ensuring(_ => x + zero(x.p) == x)

  @ghost @opaque @inlineOnce
  def addComm(x: FieldElem, y: FieldElem): Unit = {
    require(x.p == y.p)
  }.ensuring(_ => x + y == y + x)

  @ghost @opaque @inlineOnce
  def addAssoc(x: FieldElem, y: FieldElem, z: FieldElem): Unit = {
    require(x.p == y.p && y.p == z.p)
  }.ensuring(_ => (x + y) + z == x + (y + z))

  @ghost @opaque @inlineOnce
  def addNeg(x: FieldElem): Unit = {
    ()
  }.ensuring(_ => x + (-x) == zero(x.p))

  @ghost @opaque @inlineOnce
  def mulOne(x: FieldElem): Unit = {
    modUnique(x.v, x.p, BigInt(0), x.v)
  }.ensuring(_ => x * one(x.p) == x)

  @ghost @opaque @inlineOnce
  def mulComm(x: FieldElem, y: FieldElem): Unit = {
    require(x.p == y.p)
  }.ensuring(_ => x * y == y * x)

  @ghost @opaque @inlineOnce
  def mulAssoc(x: FieldElem, y: FieldElem, z: FieldElem): Unit = {
    require(x.p == y.p && y.p == z.p)
    val (a, b, c, p) = (x.v, y.v, z.v, x.p)
    val ab = a * b
    val bc = b * c
    mulNonNeg(a, b); mulNonNeg(b, c)
    // ((a*b) mod p * c) mod p == (ab*c) mod p, witnessed by ab == q*p + u.
    val u = (x * y).v
    val q = floorDiv(ab, p)
    modUnique(ab, p, q, ab - q * p)
    mulNonNeg(u, c)
    val q2 = floorDiv(u * c, p)
    modUnique(u * c, p, q2, u * c - q2 * p)
    assert(ab * c == (q * c + q2) * p + (u * c - q2 * p))
    mulNonNeg(ab, c)
    modUnique(ab * c, p, q * c + q2, u * c - q2 * p)
    assert(((x * y) * z).v == (ab * c).mod(p))
    modUnique(a, p, BigInt(0), a)
    modMul(a, bc, p)
    assert((x * (y * z)).v == (a * bc).mod(p))
    assert(ab * c == a * bc)
  }.ensuring(_ => (x * y) * z == x * (y * z))

  @ghost @opaque @inlineOnce
  def distrib(x: FieldElem, y: FieldElem, z: FieldElem): Unit = {
    require(x.p == y.p && y.p == z.p)
    val (a, b, c, p) = (x.v, y.v, z.v, x.p)
    val s = (y + z).v
    // s == (b + c) mod p, by uniqueness of the remainder.
    if (b + c >= p) modUnique(b + c, p, BigInt(1), b + c - p) else modUnique(b + c, p, BigInt(0), b + c)
    assert(s == (b + c).mod(p))
    modUnique(a, p, BigInt(0), a)
    // lhs: (a*s) mod p == (a*(b + c)) mod p
    modMul(a, b + c, p)
    assert((x * (y + z)).v == (a * (b + c)).mod(p))
    // rhs: ((a*b) mod p + (a*c) mod p) reduced == (a*b + a*c) mod p
    mulNonNeg(a, b); mulNonNeg(a, c)
    val u = (x * y).v
    val t = (x * z).v
    if (u + t >= p) modUnique(u + t, p, BigInt(1), u + t - p) else modUnique(u + t, p, BigInt(0), u + t)
    assert((x * y + x * z).v == (u + t).mod(p))
    modSum(a * b, a * c, p)
    assert((x * y + x * z).v == (a * b + a * c).mod(p))
    assert(a * (b + c) == a * b + a * c)
  }.ensuring(_ => x * (y + z) == x * y + x * z)

  @ghost @opaque @inlineOnce
  def mulInverse(x: FieldElem): Unit = {
    require(x.v != 0 && Primes.isPrime(x.p))
  }.ensuring(_ => x * x.inverse == one(x.p))

  @ghost @opaque @inlineOnce
  def subIsAddNeg(x: FieldElem, y: FieldElem): Unit = {
    require(x.p == y.p)
  }.ensuring(_ => x - y == x + (-y))

  @ghost @opaque @inlineOnce
  def divIsMulInverse(x: FieldElem, y: FieldElem): Unit = {
    require(x.p == y.p && y.v != 0 && Primes.isPrime(x.p))
  }.ensuring(_ => x / y == x * y.inverse)
}
