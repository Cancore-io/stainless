package crypto

import stainless.lang._
import stainless.lang.StaticChecks._
import stainless.annotation._
import stainless.collection._
import stainless.math.NonLinear._
import crypto.NumberTheory._
import crypto.Primes._

/**
 * Lucas's primality theorem (closes TCB T5): with a^(p-1) == 1 (mod p) and a^((p-1)/q) != 1 (mod p)
 * for every prime q dividing p - 1, p is prime. Proof: the order o of a divides p - 1, and a prime
 * factor r of (p-1)/o would be some listed q with o | (p-1)/q, so o == p - 1; then a^1..a^(p-1) are
 * p - 1 distinct residues in [1, p-1] that are units, so a divisor g of p in [2, p-1] would leave
 * p - 1 distinct values in a range of p - 2 (pigeonhole).
 */
object Lucas {

  /** a^i mod p, the residue every lemma below talks about. */
  def res(a: BigInt, i: BigInt, p: BigInt): BigInt = {
    require(i >= 0 && p > 0)
    pow(a, i).mod(p)
  }

  @ghost @opaque @inlineOnce
  def modMod(x: BigInt, p: BigInt): Unit = {
    require(x >= 0 && p > 0)
    modUnique(x.mod(p), p, BigInt(0), x.mod(p))
  }.ensuring(_ => x.mod(p).mod(p) == x.mod(p))

  /** res(i + j) == res(i) * res(j) mod p */
  @ghost @opaque @inlineOnce
  def resAdd(a: BigInt, i: BigInt, j: BigInt, p: BigInt): Unit = {
    require(a >= 0 && i >= 0 && j >= 0 && p > 0)
    powAdd(a, i, j)
    powNonNeg(a, i)
    powNonNeg(a, j)
    modMul(pow(a, i), pow(a, j), p)
  }.ensuring(_ => res(a, i + j, p) == (res(a, i, p) * res(a, j, p)).mod(p))

  /** res(c) == 1  ==>  res(c * k) == 1 */
  @ghost @opaque @inlineOnce
  def resOnePow(a: BigInt, c: BigInt, k: BigInt, p: BigInt): Unit = {
    require(a >= 0 && c >= 0 && k >= 0 && p > 1 && res(a, c, p) == BigInt(1))
    decreases(k)
    if (k > 0) {
      resOnePow(a, c, k - 1, p)
      assert(c * k == c * (k - 1) + c)
      mulNonNeg(c, k - 1)
      resAdd(a, c * (k - 1), c, p)
      modUnique(BigInt(1), p, BigInt(0), BigInt(1))
    } else {
      modUnique(BigInt(1), p, BigInt(0), BigInt(1))
    }
  }.ensuring(_ => res(a, c * k, p) == BigInt(1))

  // ──────────────────────────────────────────────────────────────────────────
  // The order of a modulo p
  // ──────────────────────────────────────────────────────────────────────────

  /** The least e in [k, p-1] with res(e) == 1. */
  @ghost
  def ordFrom(a: BigInt, p: BigInt, k: BigInt): BigInt = {
    require(p > 2 && 1 <= k && k <= p - 1 && res(a, p - 1, p) == BigInt(1))
    decreases(p - 1 - k)
    if (res(a, k, p) == BigInt(1)) k else ordFrom(a, p, k + 1)
  }.ensuring(o => k <= o && o <= p - 1 && res(a, o, p) == BigInt(1))

  @ghost @opaque @inlineOnce
  def ordMin(a: BigInt, p: BigInt, k: BigInt, j: BigInt): Unit = {
    require(p > 2 && 1 <= k && k <= p - 1 && res(a, p - 1, p) == BigInt(1) && k <= j && j < ordFrom(a, p, k))
    decreases(p - 1 - k)
    if (res(a, k, p) != BigInt(1) && j > k) ordMin(a, p, k + 1, j)
  }.ensuring(_ => res(a, j, p) != BigInt(1))

  /** res(e) == 1  ==>  e == o * c for the order o. */
  @ghost @opaque
  def ordDivides(a: BigInt, p: BigInt, e: BigInt): BigInt = {
    require(a >= 0 && p > 2 && res(a, p - 1, p) == BigInt(1) && e >= 0 && res(a, e, p) == BigInt(1))
    val o = ordFrom(a, p, BigInt(1))
    val c = e / o
    val r = e % o
    assert(e == o * c + r && 0 <= r && r < o)
    mulNonNeg(o, c)
    resOnePow(a, o, c, p)
    resAdd(a, o * c, r, p)
    powNonNeg(a, r)
    modMod(pow(a, r), p)
    if (r > 0) ordMin(a, p, BigInt(1), r)
    c
  }.ensuring(c => c >= 0 && e == ordFrom(a, p, BigInt(1)) * c)

  // ──────────────────────────────────────────────────────────────────────────
  // Primes and divisibility
  // ──────────────────────────────────────────────────────────────────────────

  /** Euclid: a prime r dividing x*y divides x or y (witness form). */
  @ghost @opaque
  def euclid(r: BigInt, x: BigInt, y: BigInt, k: BigInt): Unit = {
    require(isPrime(r) && x >= 0 && y >= 0 && x * y == r * k)
    unfold(isPrime(r))
    val xm = x.mod(r)
    if (xm != 0) {
      val qx = x / r
      modUnique(x, r, qx, x % r)
      assert(x == qx * r + xm)
      primeCoprime(r, xm)
      val w = extendedGcd(xm, r)
      bezout(xm, r, w)
      // y == y*(xm*u + r*v) == u*(xm*y) + r*v*y and xm*y == r*(k - qx*y).
      assert(xm * y == r * (k - qx * y))
      assert(y == w.x * (xm * y) + r * (w.y * y))
      val t = w.x * (k - qx * y) + w.y * y
      assert(y == t * r)
      modUnique(y, r, t, BigInt(0))
    }
  }.ensuring(_ => x.mod(r) == 0 || y.mod(r) == 0)

  /** d.mod(r) == 0 with d >= 0, r > 0 gives the witness d == r * (d / r). */
  @ghost @opaque @inlineOnce
  def modZero(d: BigInt, r: BigInt): Unit = {
    require(d >= 0 && r > 0 && d.mod(r) == 0)
    modUnique(d, r, d / r, d % r)
  }.ensuring(_ => d == r * (d / r))

  /** A prime r dividing q^e divides q. */
  @ghost @opaque
  def euclidPow(r: BigInt, q: BigInt, e: BigInt): Unit = {
    require(r > 1 && isPrime(r) && q >= 0 && e >= 0 && pow(q, e).mod(r) == 0)
    decreases(e)
    unfold(isPrime(r))
    if (e == 0) modUnique(BigInt(1), r, BigInt(0), BigInt(1))
    else {
      powNonNeg(q, e - 1)
      mulNonNeg(q, pow(q, e - 1))
      modZero(pow(q, e), r)
      euclid(r, q, pow(q, e - 1), pow(q, e) / r)
      if (q.mod(r) != 0) euclidPow(r, q, e - 1)
    }
  }.ensuring(_ => q.mod(r) == 0)

  /** A prime r dividing a prime q is q. */
  @ghost @opaque @inlineOnce
  def primeDividesPrime(r: BigInt, q: BigInt): Unit = {
    require(r > 1 && isPrime(r) && isPrime(q) && q.mod(r) == 0)
    unfold(isPrime(r))
    unfold(isPrime(q))
    modZero(q, r)
    val k = q / r
    if (k <= 0) mulMonoLeft(k, BigInt(0), r)
    if (k == 1) () else {
      mulMonoLeft(BigInt(2), k, r)
      if (r < q) noFactorBelow(q, q - 1, r, k)
    }
  }.ensuring(_ => r == q)

  def allPrime(known: List[BigInt]): Boolean = known match {
    case Nil()      => true
    case Cons(h, t) => isPrime(h) && allPrime(t)
  }

  @ghost @opaque
  def forallAllPrime(known: List[BigInt]): Unit = {
    require(known.forall(q => isPrime(q)))
    decreases(known)
    known match {
      case Nil()      => ()
      case Cons(_, t) => forallAllPrime(t)
    }
  }.ensuring(_ => allPrime(known))

  @ghost @opaque
  def allPrimeContains(known: List[BigInt], q: BigInt): Unit = {
    require(allPrime(known) && known.contains(q))
    decreases(known)
    known match {
      case Cons(h, t) => if (h != q) allPrimeContains(t, q)
    }
  }.ensuring(_ => isPrime(q))

  /** A prime r dividing product(fs) is one of the listed q (Pratt.factorsOk lists only certified primes). */
  @ghost @opaque
  def primeFactorListed(r: BigInt, p: BigInt, a: BigInt, fs: List[PrattFactor], known: List[BigInt]): PrattFactor = {
    require(p > 2 && 0 < a && a < p && r > 1 && isPrime(r) && allPrime(known) && Pratt.factorsOk(p, a, fs, known) &&
      Pratt.product(fs).mod(r) == 0)
    decreases(fs)
    unfold(isPrime(r))
    unfold(Pratt.factorsOk(p, a, fs, known))
    fs match {
      case Nil() =>
        modUnique(BigInt(1), r, BigInt(0), BigInt(1))
        PrattFactor(BigInt(0), BigInt(0), BigInt(0))
      case Cons(f, t) =>
        allPrimeContains(known, f.q)
        unfold(isPrime(f.q))
        powNonNeg(f.q, f.e)
        productNonNeg(p, a, t, known)
        productNonNeg(p, a, fs, known)
        val pr = Pratt.product(Cons(f, t))
        modZero(pr, r)
        euclid(r, pow(f.q, f.e), Pratt.product(t), pr / r)
        if (pow(f.q, f.e).mod(r) == 0) {
          euclidPow(r, f.q, f.e)
          primeDividesPrime(r, f.q)
          f
        } else primeFactorListed(r, p, a, t, known)
    }
  }.ensuring(f => fs.contains(f) && f.q == r)

  @ghost @opaque
  def productNonNeg(p: BigInt, a: BigInt, fs: List[PrattFactor], known: List[BigInt]): Unit = {
    require(p > 2 && 0 < a && a < p && allPrime(known) && Pratt.factorsOk(p, a, fs, known))
    decreases(fs)
    unfold(Pratt.factorsOk(p, a, fs, known))
    fs match {
      case Nil() => ()
      case Cons(f, t) =>
        allPrimeContains(known, f.q)
        unfold(isPrime(f.q))
        productNonNeg(p, a, t, known)
        powNonNeg(f.q, f.e)
        mulNonNeg(pow(f.q, f.e), Pratt.product(t))
    }
  }.ensuring(_ => Pratt.product(fs) >= 0)


  /** The conditions factorsOk states for a listed factor. */
  @ghost @opaque
  def factorsOkContains(p: BigInt, a: BigInt, fs: List[PrattFactor], known: List[BigInt], f: PrattFactor): Unit = {
    require(p > 2 && 0 < a && a < p && Pratt.factorsOk(p, a, fs, known) && fs.contains(f))
    decreases(fs)
    unfold(Pratt.factorsOk(p, a, fs, known))
    fs match {
      case Cons(h, t) => if (h != f) factorsOkContains(p, a, t, known, f)
    }
  }.ensuring(_ => f.q * f.cofactor == p - 1 && f.cofactor >= 0 && modPow(a, f.cofactor, p) != BigInt(1))

  /** The least divisor >= d of c, given none in [2, d-1]; it is prime. */
  @ghost
  def leastDivisor(c: BigInt, d: BigInt): BigInt = {
    require(c >= 2 && 2 <= d && d <= c && noDivisorUpTo(c, d - 1))
    decreases(c - d)
    if (c.mod(d) == 0) d
    else {
      if (d == c) modUnique(c, c, BigInt(1), BigInt(0))
      leastDivisor(c, d + 1)
    }
  }.ensuring(r => 2 <= r && r <= c && c.mod(r) == 0 && noDivisorUpTo(c, r - 1))

  /** No divisor of c below r ==> no divisor of r below r (r | c). */
  @ghost @opaque
  def noDivisorTransfer(c: BigInt, r: BigInt, k: BigInt, d: BigInt): Unit = {
    require(c >= 2 && 2 <= r && c == r * k && noDivisorUpTo(c, r - 1) && 1 <= d && d <= r - 1)
    decreases(d)
    if (d > 1) {
      noDivisorTransfer(c, r, k, d - 1)
      if (r.mod(d) == 0) {
        modZero(r, d)
        val j = r / d
        assert(c == d * (j * k))
        noFactorBelow(c, r - 1, d, j * k)
      }
    }
  }.ensuring(_ => noDivisorUpTo(r, d))

  @ghost @opaque
  def primeDivisor(c: BigInt): BigInt = {
    require(c >= 2)
    val r = leastDivisor(c, BigInt(2))
    modZero(c, r)
    noDivisorTransfer(c, r, c / r, r - 1)
    unfold(isPrime(r))
    r
  }.ensuring(r => isPrime(r) && c.mod(r) == 0)

  /** !noDivisorUpTo(p, d) yields a divisor g in [2, d]. */
  @ghost
  def divisorWitness(p: BigInt, d: BigInt): BigInt = {
    require(d >= 1 && !noDivisorUpTo(p, d))
    decreases(d)
    if (p.mod(d) == 0) d else divisorWitness(p, d - 1)
  }.ensuring(g => 2 <= g && g <= d && p.mod(g) == 0)

  // ──────────────────────────────────────────────────────────────────────────
  // Pigeonhole
  // ──────────────────────────────────────────────────────────────────────────

  def distinct(l: List[BigInt]): Boolean = l match {
    case Nil()      => true
    case Cons(h, t) => !t.contains(h) && distinct(t)
  }

  /** Every x in l: lo <= x <= hi and x != g. */
  def allIn(l: List[BigInt], lo: BigInt, hi: BigInt, g: BigInt): Boolean = l match {
    case Nil()      => true
    case Cons(h, t) => lo <= h && h <= hi && h != g && allIn(t, lo, hi, g)
  }

  def without(l: List[BigInt], x: BigInt): List[BigInt] = {
    decreases(l)
    l match {
      case Nil()      => Nil[BigInt]()
      case Cons(h, t) => if (h == x) t else Cons(h, without(t, x))
    }
  }

  @ghost @opaque
  def withoutSubset(l: List[BigInt], x: BigInt, y: BigInt): Unit = {
    require(without(l, x).contains(y))
    decreases(l)
    l match {
      case Cons(h, t) => if (h != x && h != y) withoutSubset(t, x, y)
    }
  }.ensuring(_ => l.contains(y))

  @ghost @opaque
  def withoutProps(l: List[BigInt], lo: BigInt, hi: BigInt, g: BigInt): Unit = {
    require(distinct(l) && allIn(l, lo, hi, g))
    decreases(l)
    l match {
      case Nil() => ()
      case Cons(h, t) =>
        withoutProps(t, lo, hi, g)
        if (h != hi) {
          if (without(t, hi).contains(h)) withoutSubset(t, hi, h)
        } else {
          allInNot(t, lo, hi, g)
        }
    }
  }.ensuring(_ => {
    val w = without(l, hi)
    distinct(w) && allIn(w, lo, hi - 1, g) && l.size <= w.size + 1 && (!l.contains(hi) ==> (l.size == w.size))
  })

  /** distinct and allIn(lo, hi): with hi not in t, t lies in [lo, hi - 1]. */
  @ghost @opaque
  def allInNot(t: List[BigInt], lo: BigInt, hi: BigInt, g: BigInt): Unit = {
    require(allIn(t, lo, hi, g) && !t.contains(hi))
    decreases(t)
    t match {
      case Nil()       => ()
      case Cons(_, tt) => allInNot(tt, lo, hi, g)
    }
  }.ensuring(_ => allIn(t, lo, hi - 1, g))

  @ghost @opaque
  def allInEmpty(l: List[BigInt], lo: BigInt, hi: BigInt, g: BigInt): Unit = {
    require(allIn(l, lo, hi, g) && hi < lo)
  }.ensuring(_ => l.size == BigInt(0))

  /** Distinct values in [lo, hi] minus {g}: at most hi - lo + 1, one fewer when g is in range. */
  @ghost @opaque
  def pigeonhole(l: List[BigInt], lo: BigInt, hi: BigInt, g: BigInt): Unit = {
    require(distinct(l) && allIn(l, lo, hi, g) && hi >= lo - 1)
    decreases(if (hi < lo) BigInt(0) else hi - lo + 1)
    if (hi < lo) allInEmpty(l, lo, hi, g)
    else {
      withoutProps(l, lo, hi, g)
      pigeonhole(without(l, hi), lo, hi - 1, g)
      if (hi == g) allInNoG(l, lo, hi, g)
    }
  }.ensuring(_ => l.size <= hi - lo + 1 - (if (lo <= g && g <= hi) BigInt(1) else BigInt(0)))

  @ghost @opaque
  def allInNoG(l: List[BigInt], lo: BigInt, hi: BigInt, g: BigInt): Unit = {
    require(allIn(l, lo, hi, g))
    decreases(l)
    l match {
      case Nil()      => ()
      case Cons(_, t) => allInNoG(t, lo, hi, g)
    }
  }.ensuring(_ => !l.contains(g))

  // ──────────────────────────────────────────────────────────────────────────
  // The residues a^1..a^k
  // ──────────────────────────────────────────────────────────────────────────

  def residues(a: BigInt, p: BigInt, k: BigInt): List[BigInt] = {
    require(k >= 0 && p > 0)
    decreases(k)
    if (k == 0) Nil[BigInt]() else Cons(res(a, k, p), residues(a, p, k - 1))
  }.ensuring(l => l.size == k)

  /** With order p - 1, res(j) != res(k) for 1 <= j < k <= p - 1. */
  @ghost @opaque
  def resDistinct(a: BigInt, p: BigInt, j: BigInt, k: BigInt): Unit = {
    require(a >= 0 && p > 2 && res(a, p - 1, p) == BigInt(1) && ordFrom(a, p, BigInt(1)) == p - 1 &&
      1 <= j && j < k && k <= p - 1)
    if (res(a, k, p) == res(a, j, p)) {
      val u = p - 1 - j
      resAdd(a, k, u, p)
      resAdd(a, j, u, p)
      assert(k + u == (p - 1) + (k - j))
      resAdd(a, p - 1, k - j, p)
      powNonNeg(a, k - j)
      modMod(pow(a, k - j), p)
      assert(j + u == p - 1)
      ordMin(a, p, BigInt(1), k - j)
    }
  }.ensuring(_ => res(a, k, p) != res(a, j, p))

  @ghost @opaque
  def notInResidues(a: BigInt, p: BigInt, k: BigInt, m: BigInt): Unit = {
    require(a >= 0 && p > 2 && res(a, p - 1, p) == BigInt(1) && ordFrom(a, p, BigInt(1)) == p - 1 &&
      0 <= m && m < k && k <= p - 1)
    decreases(m)
    if (m > 0) {
      resDistinct(a, p, m, k)
      notInResidues(a, p, k, m - 1)
    }
  }.ensuring(_ => !residues(a, p, m).contains(res(a, k, p)))

  @ghost @opaque
  def residuesDistinct(a: BigInt, p: BigInt, k: BigInt): Unit = {
    require(a >= 0 && p > 2 && res(a, p - 1, p) == BigInt(1) && ordFrom(a, p, BigInt(1)) == p - 1 &&
      0 <= k && k <= p - 1)
    decreases(k)
    if (k > 0) {
      notInResidues(a, p, k, k - 1)
      residuesDistinct(a, p, k - 1)
    }
  }.ensuring(_ => distinct(residues(a, p, k)))

  /** res(i), 1 <= i <= p - 1, is a unit: not 0 and not a divisor g in [2, p-1] of p. */
  @ghost @opaque
  def resUnit(a: BigInt, p: BigInt, i: BigInt, g: BigInt): Unit = {
    require(a >= 0 && p > 2 && res(a, p - 1, p) == BigInt(1) && 1 <= i && i <= p - 1 &&
      2 <= g && g <= p - 1 && p.mod(g) == 0)
    val u = p - 1 - i
    resAdd(a, i, u, p)
    val x = res(a, i, p)
    val y = res(a, u, p)
    assert((x * y).mod(p) == BigInt(1))
    if (x == 0) ()
    else if (x == g) {
      mulNonNeg(x, y)
      modZero(p, g)
      val h = p / g
      val q = (x * y) / p
      modUnique(x * y, p, q, (x * y) % p)
      // g*y == q*g*h + 1, so g*(y - q*h) == 1.
      assert(g * (y - q * h) == BigInt(1))
      unitFactor(g, y - q * h)
    }
  }.ensuring(_ => 1 <= res(a, i, p) && res(a, i, p) <= p - 1 && res(a, i, p) != g)

  @ghost @opaque
  def residuesIn(a: BigInt, p: BigInt, k: BigInt, g: BigInt): Unit = {
    require(a >= 0 && p > 2 && res(a, p - 1, p) == BigInt(1) && 0 <= k && k <= p - 1 &&
      2 <= g && g <= p - 1 && p.mod(g) == 0)
    decreases(k)
    if (k > 0) {
      resUnit(a, p, k, g)
      residuesIn(a, p, k - 1, g)
    }
  }.ensuring(_ => allIn(residues(a, p, k), BigInt(1), p - 1, g))

  // ──────────────────────────────────────────────────────────────────────────
  // The theorem
  // ──────────────────────────────────────────────────────────────────────────

  @ghost @opaque
  def orderIsFull(s: PrattStep, known: List[BigInt]): Unit = {
    require(allPrime(known) && Pratt.stepOk(s, known))
    val p = s.p
    val a = s.a
    assert(res(a, p - 1, p) == BigInt(1))
    val o = ordFrom(a, p, BigInt(1))
    val c = ordDivides(a, p, p - 1)
    if (c >= 2) {
      val r = primeDivisor(c)
      unfold(isPrime(r))
      modZero(c, r)
      val c2 = c / r
      if (c2 <= 0) mulMonoLeft(c2, BigInt(0), r)
      productNonNeg(p, a, s.factors, known)
      assert(Pratt.product(s.factors) == r * (o * c2))
      mulNonNeg(o, c2)
      modUnique(Pratt.product(s.factors), r, o * c2, BigInt(0))
      val f = primeFactorListed(r, p, a, s.factors, known)
      factorsOkContains(p, a, s.factors, known, f)
      // r*f.cofactor == r*(o*c2) with r > 0.
      mulCancel(r, f.cofactor, o * c2)
      resOnePow(a, o, c2, p)
    }
  }.ensuring(_ => ordFrom(s.a, s.p, BigInt(1)) == s.p - BigInt(1))

  @ghost @opaque @inlineOnce
  def mulCancel(r: BigInt, x: BigInt, y: BigInt): Unit = {
    require(r > 0 && r * x == r * y)
    if (x < y) mulStrictMonoLeft(x, y, r)
    else if (x > y) mulStrictMonoLeft(y, x, r)
  }.ensuring(_ => x == y)

  @ghost @opaque
  def lucasTheorem(s: PrattStep, known: List[BigInt]): Unit = {
    require(allPrime(known) && Pratt.stepOk(s, known))
    val p = s.p
    val a = s.a
    orderIsFull(s, known)
    unfold(isPrime(p))
    if (!noDivisorUpTo(p, p - 1)) {
      val g = divisorWitness(p, p - 1)
      residuesDistinct(a, p, p - 1)
      residuesIn(a, p, p - 1, g)
      pigeonhole(residues(a, p, p - 1), BigInt(1), p - 1, g)
    }
  }.ensuring(_ => isPrime(s.p))
}
