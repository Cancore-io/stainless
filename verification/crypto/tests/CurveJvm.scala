package crypto

import crypto.Curve._
import java.nio.file.{Files, Path}

/**
 * Executes the verified group law on the JVM against the PR 1 curve vectors:
 * every input and result point is checked with isOnCurve, every `add` vector
 * with add, every `mul` vector [k]G with a test-side double-and-add over the
 * verified add/double, and the 20 edge cases. Associativity (TCB T3) is pinned
 * on vector points.
 */
object CurveJvm {
  private var checks = 0
  private def check(cond: Boolean, msg: => String): Unit = {
    checks += 1
    if (!cond) { System.err.println(s"FAIL: $msg"); sys.exit(1) }
  }
  private def hex(s: String) = BigInt(s, 16)

  // SEC 2 / FIPS 186-4 parameters and generators; n is the group order.
  val curves: Map[String, (CurveParams, ECPoint, BigInt)] = Map(
    "secp256k1" -> (CurveParams(0, 7, hex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F")),
      AffinePoint(hex("79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798"),
        hex("483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8")),
      hex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141")),
    "NIST_P256" -> (CurveParams(-3, hex("5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B"),
      hex("FFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF")),
      AffinePoint(hex("6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296"),
        hex("4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5")),
      hex("FFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551")),
    "toy_p23" -> (CurveParams(-1, 0, 23), AffinePoint(1, 0), BigInt(2)),
  )

  /** Test-side left-to-right double-and-add over the verified add/double. */
  def mul(k: BigInt, pt: ECPoint, c: CurveParams): ECPoint =
    (k.bitLength - 1 to 0 by -1).foldLeft(InfinityPoint: ECPoint) { (acc, i) =>
      val d = double(acc, c)
      if (k.testBit(i)) add(d, pt, c) else d
    }

  private def point(v: ujson.Value): ECPoint =
    if (v.isNull) InfinityPoint else AffinePoint(hex(v("x").str), hex(v("y").str))

  private def run(v: ujson.Value): ECPoint = {
    val (c, g, _) = curves(v("curve").str)
    v("op").str match {
      case "add" =>
        val (p, q) = (point(v("p")), point(v("q")))
        check(isOnCurve(p, c) && isOnCurve(q, c), s"input off the curve: $v")
        add(p, q, c)
      case "mul" => mul(hex(v("k").str), g, c)
    }
  }

  def main(args: Array[String]): Unit = {
    val dir = Path.of(args.headOption.getOrElse("verification/crypto-oracle/vectors"))
    def load(f: String) = ujson.read(Files.readString(dir.resolve(f))).arr.toSeq
    val curveVs = load("secp256k1_vectors.json") ++ load("nist_p256_vectors.json")
    val edgeVs = load("edge_cases_vectors.json")
    check(curveVs.size == 532 && edgeVs.size == 20, s"vector counts ${curveVs.size}, ${edgeVs.size}")

    for (v <- curveVs ++ edgeVs) {
      val (c, _, _) = curves(v("curve").str)
      val got = run(v)
      check(got == point(v("result")), s"${v("curve").str} ${v("op").str}: got $got for $v")
      check(isOnCurve(got, c), s"result off the curve: $v")
    }

    for ((name, (c, g, n)) <- curves) {
      // [n]G == O and [n-1]G == -G (PR 6 proves the scalar multiplication; here the group law).
      check(mul(n, g, c) == InfinityPoint, s"[n]G on $name")
      check(mul(n - 1, g, c) == neg(g, c), s"[n-1]G == -G on $name")
      check(add(g, neg(g, c), c) == InfinityPoint, s"G + (-G) on $name")
      // Off-curve points are rejected (y + 1 breaks the equation).
      g match {
        case AffinePoint(x, y) =>
          check(!isOnCurve(AffinePoint(x, (y + 1).mod(c.p)), c), s"off-curve point accepted on $name")
          check(!isOnCurve(AffinePoint(x, y + c.p), c), s"out-of-field y accepted on $name")
        case _ =>
      }
    }

    // Commutativity and associativity (TCB T3) on vector points.
    for (name <- Seq("secp256k1", "NIST_P256")) {
      val (c, _, _) = curves(name)
      val pts = curveVs.filter(_("curve").str == name).map(v => point(v("result"))).take(24)
      for (Seq(p, q, r) <- pts.sliding(3)) {
        check(add(p, q, c) == add(q, p, c), s"commutativity on $name")
        check(add(add(p, q, c), r, c) == add(p, add(q, r, c), c), s"associativity on $name")
        check(add(add(p, p, c), neg(p, c), c) == p, s"2P - P == P on $name")
      }
    }

    println(s"Curve JVM: ${curveVs.size} curve vectors, ${edgeVs.size} edge cases, $checks checks passed")
  }
}
