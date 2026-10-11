//> using scala 3.9.0
//> using dep com.lihaoyi::ujson:4.4.3

package verification.oracle

import java.math.BigInteger
import java.nio.file.{Files, Paths}

/**
 * JVM Cross-Validation Runner for Cryptographic Test Vectors.
 * Re-derives every curve vector with an independent affine implementation on
 * java.math.BigInteger instead of trusting the Python oracle's results.
 */
object CryptoOracleJvmTest:

  type Point = Option[(BigInteger, BigInteger)] // None = point at infinity

  final case class Curve(p: BigInteger, a: BigInteger, b: BigInteger, g: Point, n: BigInteger):
    def onCurve(pt: Point): Boolean = pt match
      case None => true
      case Some((x, y)) =>
        x.signum >= 0 && x.compareTo(p) < 0 && y.signum >= 0 && y.compareTo(p) < 0 &&
          y.multiply(y).subtract(x.pow(3).add(a.multiply(x)).add(b)).mod(p).signum == 0

    def neg(pt: Point): Point = pt.map((x, y) => (x, y.negate.mod(p)))

    def add(p1: Point, p2: Point): Point = (p1, p2) match
      case (None, q) => q
      case (q, None) => q
      case (Some((x1, y1)), Some((x2, y2))) =>
        if x1 == x2 && y1.add(y2).mod(p).signum == 0 then None
        else
          val lam =
            if x1 == x2 then x1.pow(2).multiply(Three).add(a).multiply(y1.shiftLeft(1).modInverse(p)).mod(p)
            else y2.subtract(y1).multiply(x2.subtract(x1).modInverse(p)).mod(p)
          val x3 = lam.pow(2).subtract(x1).subtract(x2).mod(p)
          Some((x3, lam.multiply(x1.subtract(x3)).subtract(y1).mod(p)))

    // Left-to-right double-and-add (the oracle is right-to-left), k not reduced mod n.
    def mul(k: BigInteger, pt: Point): Point =
      (k.bitLength - 1 to 0 by -1).foldLeft(None: Point) { (acc, i) =>
        val d = add(acc, acc)
        if k.testBit(i) then add(d, pt) else d
      }

  val Three = BigInteger.valueOf(3)
  def hex(s: String) = new BigInteger(s, 16)
  def dec(s: String) = new BigInteger(s)

  // Independent transcription of SEC 2 / FIPS 186-4 parameters.
  val Curves: Map[String, Curve] = Map(
    "secp256k1" -> Curve(
      hex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F"), BigInteger.ZERO, BigInteger.valueOf(7),
      Some((hex("79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798"),
        hex("483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8"))),
      hex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141")),
    "NIST_P256" -> Curve(
      hex("FFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF"), BigInteger.valueOf(-3),
      hex("5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B"),
      Some((hex("6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296"),
        hex("4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5"))),
      hex("FFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551")),
    "toy_p23" -> Curve(BigInteger.valueOf(23), BigInteger.valueOf(-1), BigInteger.ZERO,
      Some((BigInteger.ONE, BigInteger.ZERO)), BigInteger.TWO),
  )

  def point(v: ujson.Value): Point =
    if v.isNull then None else Some((hex(v("x").str), hex(v("y").str)))

  def main(args: Array[String]): Unit =
    println("=== Starting Crypto Oracle JVM Test Suite ===")
    // The vectors directory is passed explicitly (run_all.sh does); never guessed from the cwd.
    val dir = Paths.get(args.headOption.getOrElse(throw new IllegalArgumentException("usage: <vectors-dir>")))
    assert(Files.isDirectory(dir), s"Vectors directory not found: $dir")
    def load(name: String) = ujson.read(Files.readString(dir.resolve(name))).arr.toSeq

    val curveVectors = load("secp256k1_vectors.json") ++ load("nist_p256_vectors.json")
    println(s"[JVM] Recomputed ${checkCurveVectors(curveVectors)} secp256k1 / P-256 vectors.")
    println(s"[JVM] Recomputed ${checkCurveVectors(load("edge_cases_vectors.json"))} edge cases.")
    println(s"[JVM] Verified ${checkModular(load("modular_arithmetic_vectors.json"))} modular arithmetic cases.")
    println(s"[JVM] Verified ${checkRfc6979(load("rfc6979_vectors.json"))} RFC 6979 signatures.")
    println("=== ALL JVM VERIFICATION CHECKS PASSED SUCCESSFULLY ===")

  def checkCurveVectors(vs: Seq[ujson.Value]): Int =
    assert(vs.nonEmpty, "No curve vectors")
    for v <- vs do
      val c = Curves(v("curve").str)
      val expected = point(v("result"))
      for key <- Seq("p", "q") if v.obj.contains(key) do assert(c.onCurve(point(v(key))), s"Input not on curve: $v")
      val got = v("op").str match
        case "mul" => c.mul(hex(v("k").str), c.g)
        case "add" => c.add(point(v("p")), point(v("q")))
      assert(got == expected, s"JVM result differs from oracle: $v")
      assert(c.onCurve(got), s"Result not on curve: $v")
      // Edge-case invariants checked directly, not via the stored result.
      v.obj.get("name").map(_.str).foreach {
        case "inverse_P_plus_negP" => assert(point(v("q")) == c.neg(point(v("p"))) && got.isEmpty, v)
        case "order_mult_n_minus_1_G_eq_negG" => assert(got == c.neg(c.g), v)
        case "order_mult_nG" => assert(got.isEmpty, v)
        case _ =>
      }
    vs.size

  def checkModular(vs: Seq[ujson.Value]): Int =
    for v <- vs do
      val Seq(a, b, g, ka, kb, x, y) = Seq("a", "b", "gcd", "ka", "kb", "x", "y").map(f => dec(v(f).str))
      assert(a.gcd(b) == g, s"GCD mismatch: $v")
      assert(ka.multiply(g) == a && kb.multiply(g) == b, s"Divisibility witness failed: $v")
      assert(a.multiply(x).add(b.multiply(y)) == g, s"Bezout identity failed: $v")
      if g == BigInteger.ONE && b.compareTo(BigInteger.ONE) > 0 then
        assert(a.modInverse(b) == dec(v("inv").str), s"Inverse mismatch: $v")
      else assert(v("inv").isNull, v)
      if b.signum > 0 then
        assert(a.modPow(BigInteger.valueOf(65537), b) == dec(v("modpow_65537").str), s"modPow mismatch: $v")
      else assert(v("modpow_65537").isNull, v)
      assert(v("b_is_prime").bool == b.isProbablePrime(64), s"Primality flag wrong: $v")
      if !v("sqrt").isNull then
        val r = dec(v("sqrt").str)
        assert(r.multiply(r).subtract(a).mod(b).signum == 0, s"Tonelli-Shanks root wrong: $v")
      else if v("b_is_prime").bool then
        assert(a.modPow(b.shiftRight(1), b) == b.subtract(BigInteger.ONE), s"Residue reported as non-residue: $v")
    vs.size

  def checkRfc6979(vs: Seq[ujson.Value]): Int =
    for v <- vs do
      val c = Curves(v("curve").str)
      val Seq(d, k, r, s) = Seq("private_key", "k", "r", "s").map(f => hex(v(f).str))
      val e = hex(v("message_hash").str)
      assert(c.mul(d, c.g) == point(v("public_key")), s"Public key mismatch: $v")
      assert(c.mul(k, c.g).get._1.mod(c.n) == r, s"r != ([k]G).x mod n: $v")
      assert(s.multiply(k).subtract(e.add(d.multiply(r))).mod(c.n).signum == 0, s"ECDSA equation failed: $v")
      // Verification path: [u1]G + [u2]Q has x == r (mod n)
      val w = s.modInverse(c.n)
      val rv = c.add(c.mul(e.multiply(w).mod(c.n), c.g), c.mul(r.multiply(w).mod(c.n), point(v("public_key"))))
      assert(rv.get._1.mod(c.n) == r, s"ECDSA verification failed: $v")
    vs.size
