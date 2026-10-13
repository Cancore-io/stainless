package stainless.cryptooracle

import io.circe.Json
import io.circe.parser.parse
import org.scalatest.funsuite.AnyFunSuite

import java.math.BigInteger
import java.security.MessageDigest
import scala.io.Source

/**
 * Cross-validation of the committed crypto test vectors (verification/crypto-oracle/vectors).
 * Every curve vector is re-derived with an affine implementation independent of the Python
 * oracle; number-theoretic and RFC vectors are checked against invariants and published KATs.
 */
class CryptoOracleSuite extends AnyFunSuite {
  import CryptoOracleSuite._

  test("secp256k1 and P-256 vectors match an independent recomputation") {
    assert(checkCurveVectors(load("secp256k1_vectors.json") ++ load("nist_p256_vectors.json")) == 532)
  }

  test("edge cases are complete and recompute") {
    val vs = load("edge_cases_vectors.json")
    for (curve <- Seq("secp256k1", "NIST_P256"))
      assert(vs.filter(str(_, "curve") == curve).map(str(_, "name")).toSet == EdgeCaseNames, curve)
    assert(vs.exists(v => str(v, "curve") == "toy_p23" && str(v, "name") == "doubling_y_zero"))
    checkCurveVectors(vs)
  }

  test("gcd witnesses, inverses, modpow and square roots hold") {
    val vs = load("modular_arithmetic_vectors.json")
    for (v <- vs) {
      val Seq(a, b, g, ka, kb, x, y) = Seq("a", "b", "gcd", "ka", "kb", "x", "y").map(f => dec(str(v, f)))
      assert(a.gcd(b) == g, v)
      assert(ka.multiply(g) == a && kb.multiply(g) == b, s"divisibility witness: $v")
      assert(ka.multiply(x).add(kb.multiply(y)) == BigInteger.ONE, s"Bezout on cofactors: $v")
      assert(a.multiply(x).add(b.multiply(y)) == g, s"Bezout: $v")
      if (g == BigInteger.ONE && b.compareTo(BigInteger.ONE) > 0) assert(a.modInverse(b) == dec(str(v, "inv")), v)
      else assert(isNull(v, "inv"), v)
      if (b.signum > 0) assert(a.modPow(BigInteger.valueOf(65537), b) == dec(str(v, "modpow_65537")), v)
      else assert(isNull(v, "modpow_65537"), v)
      val prime = bool(v, "b_is_prime")
      assert(prime == b.isProbablePrime(64), s"primality flag: $v")
      if (!isNull(v, "sqrt")) {
        assert(prime, s"square root for a composite modulus: $v")
        val r = dec(str(v, "sqrt"))
        assert(r.multiply(r).subtract(a).mod(b).signum == 0, s"wrong root: $v")
      } else if (prime)
        assert(a.modPow(b.shiftRight(1), b) == b.subtract(BigInteger.ONE), s"residue reported as non-residue: $v")
    }
    // The general (p = 1 mod 4) Tonelli-Shanks branch must see both a residue and a non-residue.
    val generalBranch = vs.filter(v => bool(v, "b_is_prime") && dec(str(v, "b")).testBit(1) == false)
    assert(generalBranch.map(isNull(_, "sqrt")).toSet == Set(true, false))
  }

  test("RFC 6979 signatures verify and match A.2.5") {
    val vs = load("rfc6979_vectors.json")
    assert(vs.map(str(_, "curve")).toSet == Set("NIST_P256", "secp256k1"))
    for (v <- vs) {
      val c = Curves(str(v, "curve"))
      val Seq(d, k, r, s) = Seq("private_key", "k", "r", "s").map(f => hex(str(v, f)))
      val digest = MessageDigest.getInstance("SHA-256").digest(str(v, "message").getBytes("US-ASCII"))
      assert(toHex(digest) == str(v, "message_hash"), v)
      val e = new BigInteger(1, digest)
      for (z <- Seq(k, r, s)) assert(z.signum > 0 && z.compareTo(c.n) < 0, v)
      val q = point(v.hcursor.downField("public_key").focus.get)
      assert(c.mul(d, c.g) == q, s"public key: $v")
      assert(c.mul(k, c.g).get._1.mod(c.n) == r, s"r != ([k]G).x mod n: $v")
      assert(s.multiply(k).subtract(e.add(d.multiply(r))).mod(c.n).signum == 0, s"ECDSA equation: $v")
      val w = s.modInverse(c.n)
      val rv = c.add(c.mul(e.multiply(w).mod(c.n), c.g), c.mul(r.multiply(w).mod(c.n), q))
      assert(rv.get._1.mod(c.n) == r, s"ECDSA verification: $v")
    }
    val sample = vs.find(v => str(v, "curve") == "NIST_P256" && str(v, "message") == "sample").get
    assert(str(sample, "k") == "a6e3c57dd01abe90086538398355dd4c3b17aa873382b0f24d6129493d8aad60")
  }

  test("RFC 7748 and RFC 8032 known answers") {
    val x25519 = load("rfc7748_vectors.json")
    assert(x25519.size == 1)
    assert(str(x25519.head, "shared_secret_hex_le") == "4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742")
    assert(str(x25519.head, "alice_public_hex_le") == "8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a")

    val ed = load("rfc8032_vectors.json")
    assert(ed.size == 1)
    val pk = str(ed.head, "public_key_hex")
    assert(pk == "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a")
    // Decoded coordinates must match the encoding and lie on -x^2 + y^2 = 1 + d x^2 y^2.
    val p = BigInteger.TWO.pow(255).subtract(BigInteger.valueOf(19))
    val d = BigInteger.valueOf(-121665).multiply(BigInteger.valueOf(121666).modInverse(p)).mod(p)
    val (x, y) = (hex(str(ed.head, "public_key_x")), hex(str(ed.head, "public_key_y")))
    val enc = new BigInteger(1, pk.grouped(2).toSeq.reverse.mkString.pipe(hexBytes))
    assert(y == enc.clearBit(255) && x.testBit(0) == enc.testBit(255))
    val x2 = x.multiply(x); val y2 = y.multiply(y)
    assert(y2.subtract(x2).subtract(BigInteger.ONE).subtract(d.multiply(x2).multiply(y2)).mod(p).signum == 0)
  }

  test("at least 500 vectors in total") {
    assert(VectorFiles.map(load(_).size).sum >= 500)
  }
}

object CryptoOracleSuite {
  type Point = Option[(BigInteger, BigInteger)] // None = point at infinity

  final case class Curve(p: BigInteger, a: BigInteger, b: BigInteger, g: Point, n: BigInteger) {
    def onCurve(pt: Point): Boolean = pt match {
      case None => true
      case Some((x, y)) =>
        x.signum >= 0 && x.compareTo(p) < 0 && y.signum >= 0 && y.compareTo(p) < 0 &&
          y.multiply(y).subtract(x.pow(3).add(a.multiply(x)).add(b)).mod(p).signum == 0
    }

    def neg(pt: Point): Point = pt.map((x, y) => (x, y.negate.mod(p)))

    def add(p1: Point, p2: Point): Point = (p1, p2) match {
      case (None, q) => q
      case (q, None) => q
      case (Some((x1, y1)), Some((x2, y2))) =>
        if (x1 == x2 && y1.add(y2).mod(p).signum == 0) None
        else {
          val lam =
            if (x1 == x2) x1.pow(2).multiply(Three).add(a).multiply(y1.shiftLeft(1).modInverse(p)).mod(p)
            else y2.subtract(y1).multiply(x2.subtract(x1).modInverse(p)).mod(p)
          val x3 = lam.pow(2).subtract(x1).subtract(x2).mod(p)
          Some((x3, lam.multiply(x1.subtract(x3)).subtract(y1).mod(p)))
        }
    }

    // Left-to-right double-and-add (the oracle is right-to-left); k is not reduced mod n.
    def mul(k: BigInteger, pt: Point): Point =
      (k.bitLength - 1 to 0 by -1).foldLeft(None: Point) { (acc, i) =>
        val d = add(acc, acc)
        if (k.testBit(i)) add(d, pt) else d
      }
  }

  val Three = BigInteger.valueOf(3)
  def hex(s: String) = new BigInteger(s, 16)
  def dec(s: String) = new BigInteger(s)
  def hexBytes(s: String): Array[Byte] = s.grouped(2).map(Integer.parseInt(_, 16).toByte).toArray
  def toHex(bs: Array[Byte]): String = bs.map(b => f"${b & 0xff}%02x").mkString
  extension [A](a: A) def pipe[B](f: A => B): B = f(a)

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

  val EdgeCaseNames = Set(
    "identity_P_plus_O", "identity_O_plus_P", "identity_O_plus_O", "inverse_P_plus_negP",
    "doubling_G_plus_G", "order_mult_zero", "order_mult_nG", "order_mult_n_plus_1_G",
    "order_mult_n_minus_1_G_eq_negG",
  )

  val VectorFiles = Seq(
    "secp256k1_vectors.json", "nist_p256_vectors.json", "edge_cases_vectors.json",
    "modular_arithmetic_vectors.json", "rfc6979_vectors.json", "rfc7748_vectors.json", "rfc8032_vectors.json",
  )

  // vectors/ is a test resource directory (see build.sbt), so the suite does not depend on the cwd.
  def load(name: String): Seq[Json] = {
    val url = Option(getClass.getResource("/" + name)).getOrElse(throw new AssertionError(s"missing vector file $name"))
    val src = Source.fromURL(url, "UTF-8")
    try parse(src.mkString).fold(throw _, _.asArray.get) finally src.close()
  }

  def isNull(v: Json, key: String): Boolean = v.hcursor.downField(key).focus.forall(_.isNull)
  def str(v: Json, key: String): String = v.hcursor.get[String](key).fold(throw _, identity)
  def bool(v: Json, key: String): Boolean = v.hcursor.get[Boolean](key).fold(throw _, identity)
  def point(v: Json): Point = if (v.isNull) None else Some((hex(str(v, "x")), hex(str(v, "y"))))

  def checkCurveVectors(vs: Seq[Json]): Int = {
    assert(vs.nonEmpty, "no curve vectors")
    for (v <- vs) {
      val c = Curves(str(v, "curve"))
      def pt(key: String) = point(v.hcursor.downField(key).focus.get)
      for (key <- Seq("p", "q") if v.hcursor.downField(key).succeeded) assert(c.onCurve(pt(key)), s"input not on curve: $v")
      val got = str(v, "op") match {
        case "mul" => c.mul(hex(str(v, "k")), c.g)
        case "add" => c.add(pt("p"), pt("q"))
      }
      assert(got == pt("result"), s"recomputation differs from oracle: $v")
      assert(c.onCurve(got), s"result not on curve: $v")
      // Edge-case invariants checked directly, not via the stored result.
      v.hcursor.get[String]("name").toOption.foreach {
        case "inverse_P_plus_negP" => assert(pt("q") == c.neg(pt("p")) && got.isEmpty, v)
        case "order_mult_n_minus_1_G_eq_negG" => assert(got == c.neg(c.g), v)
        case "order_mult_nG" => assert(got.isEmpty, v)
        case _ =>
      }
    }
    vs.size
  }
}
