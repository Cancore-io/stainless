package crypto

import crypto.SqrtMod._
import java.math.BigInteger
import java.nio.file.{Files, Path}

/**
 * Executes PrimeField and SqrtMod on the JVM: Tonelli–Shanks against the PR 1
 * vectors (both p mod 4 branches, residues and non-residues), exhaustive
 * completeness over small primes, and field operations against BigInteger.
 */
object PrimeFieldJvm {
  private var checks = 0
  private def check(cond: Boolean, msg: => String): Unit = {
    checks += 1
    if (!cond) { System.err.println(s"FAIL: $msg"); sys.exit(1) }
  }
  private def some(o: stainless.lang.Option[BigInt]): Option[BigInt] = o match {
    case stainless.lang.Some(x) => scala.Some(x)
    case _                      => scala.None
  }
  private def prime(n: BigInt): Boolean = n.bigInteger.isProbablePrime(64)

  def main(args: Array[String]): Unit = {
    val dir = Path.of(args.headOption.getOrElse("verification/crypto-oracle/vectors"))
    val vs = ujson.read(Files.readString(dir.resolve("modular_arithmetic_vectors.json"))).arr

    // sqrtMod on every odd prime modulus of the oracle.
    var branches = Set.empty[(Int, Boolean)]
    for (v <- vs if v("b_is_prime").bool && BigInt(v("b").str) > 2) {
      val (a, p) = (BigInt(v("a").str), BigInt(v("b").str))
      val got = some(sqrtMod(a, p))
      val want = if (v("sqrt").isNull) scala.None else scala.Some(BigInt(v("sqrt").str))
      check(got.isDefined == want.isDefined, s"sqrtMod($a, $p) = $got, oracle $want")
      got.foreach(r => check((r * r - a).mod(p) == 0 && (want.contains(r) || want.contains(p - r)), s"root $r of $a mod $p"))
      branches += (((p.mod(4)).toInt, got.isDefined))
    }
    check(Set((3, true), (1, true), (1, false)).subsetOf(branches), s"Tonelli-Shanks branches seen: $branches")

    // Completeness: for every odd prime below 200, Some exactly on the squares.
    for (p <- (BigInt(3) until 200).filter(prime)) {
      val squares = (BigInt(0) until p).map(x => (x * x).mod(p)).toSet
      for (n <- BigInt(-p.toInt) until p * 2)
        check(some(sqrtMod(n, p)).isDefined == squares.contains(n.mod(p)), s"sqrtMod($n, $p) completeness")
    }

    // isPrime (spec, executable for small p) against BigInteger.
    for (n <- BigInt(2) until 500) check(Primes.isPrime(n) == prime(n), s"isPrime($n)")

    // Field operations on the oracle's prime moduli, against BigInteger.
    for (v <- vs if v("b_is_prime").bool) {
      val p = BigInt(v("b").str)
      val elems = Seq(BigInt(0), BigInt(1), p - 1, BigInt(v("a").str).mod(p), BigInt(v("x").str).mod(p), BigInt(v("y").str).mod(p))
      for (x <- elems; y <- elems) {
        val (fx, fy) = (FieldElem(x, p), FieldElem(y, p))
        check((fx + fy).v == (x + y).mod(p), s"$x + $y mod $p")
        check((fx - fy).v == (x - y).mod(p), s"$x - $y mod $p")
        check((fx * fy).v == (x * y).mod(p), s"$x * $y mod $p")
        check((-fx).v == (-x).mod(p), s"-$x mod $p")
        if (y != 0) {
          val inv = BigInt(y.bigInteger.modInverse(p.bigInteger))
          check(fy.inverse.v == inv, s"$y^-1 mod $p")
          check((fx / fy).v == (x * inv).mod(p), s"$x / $y mod $p")
        }
      }
      check(FieldElem.of(-BigInt(v("a").str), p).v == (-BigInt(v("a").str)).mod(p), s"of(-a) mod $p")
    }

    println(s"PrimeField/SqrtMod JVM: $checks checks passed")
  }
}
