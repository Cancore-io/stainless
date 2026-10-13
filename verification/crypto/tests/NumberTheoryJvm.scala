package crypto

import crypto.NumberTheory._
import java.math.BigInteger
import java.nio.file.{Files, Path}

/**
 * Executes the verified NumberTheory code on the JVM against the PR 1 oracle
 * vectors (verification/crypto-oracle/vectors/modular_arithmetic_vectors.json)
 * and cross-checks every result with java.math.BigInteger.
 */
object NumberTheoryJvm {
  private var checks = 0
  private def check(cond: Boolean, msg: => String): Unit = {
    checks += 1
    if (!cond) { System.err.println(s"FAIL: $msg"); sys.exit(1) }
  }
  private def big(s: String): BigInt = BigInt(s)
  private def opt(v: ujson.Value, f: String): Option[BigInt] =
    if (v(f).isNull) scala.None else scala.Some(big(v(f).str))
  private def toScala(o: stainless.lang.Option[BigInt]): Option[BigInt] = o match {
    case stainless.lang.Some(x) => scala.Some(x)
    case _                      => scala.None
  }

  def main(args: Array[String]): Unit = {
    val dir = Path.of(args.headOption.getOrElse("verification/crypto-oracle/vectors"))
    val vs = ujson.read(Files.readString(dir.resolve("modular_arithmetic_vectors.json"))).arr
    check(vs.size == 18, s"expected 18 vectors, got ${vs.size}")

    for (v <- vs) {
      val (a, b) = (big(v("a").str), big(v("b").str))
      // extendedGcd: witnesses equal the oracle's, and they satisfy the contract.
      val w = extendedGcd(a, b)
      val want = GcdWitness(big(v("gcd").str), big(v("ka").str), big(v("kb").str), big(v("x").str), big(v("y").str))
      check(w == want, s"extendedGcd($a, $b) = $w, oracle $want")
      check(w.gcd.bigInteger == a.bigInteger.gcd(b.bigInteger), s"gcd($a, $b) vs BigInteger")
      // modInverse: defined for m > 1 only; the oracle has inv iff gcd == 1 and b > 1.
      if (b > 1) {
        val inv = toScala(modInverse(a, b))
        check(inv == opt(v, "inv"), s"modInverse($a, $b) = $inv, oracle ${opt(v, "inv")}")
        inv.foreach(r => check((a * r).mod(b) == 1 && r.bigInteger == a.bigInteger.modInverse(b.bigInteger), s"inverse $r of $a mod $b"))
      } else check(opt(v, "inv").isEmpty, s"oracle has an inverse for m = $b")
      // modPow: the oracle has modpow_65537 iff b > 0.
      if (b > 0) {
        val r = modPow(a, BigInt(65537), b)
        check(scala.Some(r) == opt(v, "modpow_65537"), s"modPow($a, 65537, $b) = $r, oracle ${opt(v, "modpow_65537")}")
        check(r.bigInteger == a.bigInteger.modPow(BigInteger.valueOf(65537), b.bigInteger), s"modPow vs BigInteger")
        // Fermat on prime moduli, a cross-check independent of the oracle's modpow field.
        if (v("b_is_prime").bool && w.gcd == 1) check(modPow(a, b - 1, b) == 1, s"Fermat $a^($b-1) mod $b")
      } else check(opt(v, "modpow_65537").isEmpty, s"oracle has modpow for m = $b")
      // CRT on the vector's moduli (a, b) with residues derived from x, y.
      if (a > 0 && b > 0) {
        val (r1, r2) = (w.x.mod(a), w.y.mod(b))
        toScala(crt(r1, a, r2, b)) match {
          case scala.Some(x) =>
            check(w.gcd == 1 && 0 <= x && x < a * b && x.mod(a) == r1 && x.mod(b) == r2, s"crt($r1, $a, $r2, $b) = $x")
            val ref = r1.bigInteger.add(a.bigInteger.multiply(r2.bigInteger.subtract(r1.bigInteger)
              .multiply(a.bigInteger.modInverse(b.bigInteger)).mod(b.bigInteger)))
            check(x.bigInteger == ref, s"crt vs BigInteger Garner")
          case scala.None => check(w.gcd != 1, s"crt($r1, $a, $r2, $b) = None for coprime moduli")
        }
      }
    }

    // CRT KAT: Sunzi Suanjing (3rd-5th c.), x = 2 mod 3, 3 mod 5, 2 mod 7  ==>  x = 23.
    val x15 = toScala(crt(2, 3, 3, 5))
    check(x15 == scala.Some(BigInt(8)), s"Sunzi step 1: $x15")
    check(toScala(crt(8, 15, 2, 7)) == scala.Some(BigInt(23)), "Sunzi: 23")
    check(toScala(crt(1, 4, 3, 6)).isEmpty, "crt with gcd 2 is None")
    // Base cases of modPow and modInverse.
    check(modPow(5, 0, 7) == 1 && modPow(5, 0, 1) == 0 && modPow(0, 3, 7) == 0, "modPow base cases")
    check(toScala(modInverse(-3, 7)) == scala.Some(BigInt(2)), "modInverse of a negative a")

    println(s"NumberTheory JVM: ${vs.size} vectors, $checks checks passed")
  }
}
