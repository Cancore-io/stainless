package crypto

import stainless.lang._
import stainless.lang.StaticChecks._
import crypto.NumberTheory._

/**
 * Square roots modulo p by Tonelli–Shanks as a certifying algorithm (SPEC §3.3):
 * the search is only proved safe and terminating, and sqrtMod returns its
 * result only after checking r*r == n (mod p). Soundness (Some => a root) is
 * proved; completeness (a residue yields Some) is covered by the PR 1 vectors
 * and an exhaustive JVM check over small primes. Every loop is bounded, so a
 * composite p or a non-residue n ends in None rather than divergence.
 */
object SqrtMod {

  def sqrtMod(n: BigInt, p: BigInt): Option[BigInt] = {
    require(p > 2)
    val a = n.mod(p)
    val r = tonelliShanks(a, p)
    if ((r * r).mod(p) == a) Some(r) else None[BigInt]()
  }.ensuring(res => res.forall(r => 0 <= r && r < p && (r * r).mod(p) == n.mod(p)))

  /** A candidate root of n in [0, p); not proved to be one. */
  def tonelliShanks(n: BigInt, p: BigInt): BigInt = {
    require(0 <= n && n < p && p > 2)
    if (n == 0) BigInt(0)
    else {
      val (q, s) = splitTwos(p - 1, BigInt(0))
      if (s == 0) BigInt(0) // p even: not a prime, give up
      else {
        val z = nonResidue(BigInt(2), p)
        tsLoop(s, modPow(z, q, p), modPow(n, q, p), modPow(n, (q + 1) / 2, p), p)
      }
    }
  }.ensuring(res => 0 <= res && res < p)

  /** (q, s) with q odd and q * 2^(s - s0) == q0. */
  def splitTwos(q: BigInt, s: BigInt): (BigInt, BigInt) = {
    require(q > 0 && s >= 0)
    decreases(q)
    if (q % 2 == 0) splitTwos(q / 2, s + 1) else (q, s)
  }.ensuring(res => res._1 > 0 && res._2 >= s)

  /** The least z' >= z with z'^((p-1)/2) == -1 (mod p), or 0 if there is none below p. */
  def nonResidue(z: BigInt, p: BigInt): BigInt = {
    require(2 <= z && z <= p && p > 2)
    decreases(p - z)
    if (z == p) BigInt(0)
    else if (modPow(z, (p - 1) / 2, p) == p - 1) z
    else nonResidue(z + 1, p)
  }.ensuring(res => 0 <= res && res < p)

  /** x^(2^k) mod p. */
  def squareTimes(x: BigInt, k: BigInt, p: BigInt): BigInt = {
    require(0 <= x && x < p && k >= 0 && p > 1)
    decreases(k)
    if (k == 0) x else squareTimes((x * x).mod(p), k - 1, p)
  }.ensuring(res => 0 <= res && res < p)

  /** The least i in [i0, m) with t^(2^i) == 1 (mod p), or m if there is none. */
  def leastOrderExp(t: BigInt, i: BigInt, m: BigInt, p: BigInt): BigInt = {
    require(0 <= t && t < p && 1 <= i && i <= m && p > 1)
    decreases(m - i)
    if (i == m) m
    else if (squareTimes(t, i, p) == 1) i
    else leastOrderExp(t, i + 1, m, p)
  }.ensuring(res => i <= res && res <= m)

  def tsLoop(m: BigInt, c: BigInt, t: BigInt, r: BigInt, p: BigInt): BigInt = {
    require(m >= 1 && 0 <= c && c < p && 0 <= t && t < p && 0 <= r && r < p && p > 2)
    decreases(m)
    if (t == 1) r
    else {
      val i = leastOrderExp(t, BigInt(1), m, p)
      if (i == m) r // n is not a residue: the certificate check in sqrtMod rejects r
      else {
        val b = squareTimes(c, m - i - 1, p)
        val b2 = (b * b).mod(p)
        tsLoop(i, b2, (t * b2).mod(p), (r * b).mod(p), p)
      }
    }
  }.ensuring(res => 0 <= res && res < p)
}
