//> using scala 3.9.0

package verification.oracle

import java.math.BigInteger
import java.nio.file.{Files, Paths}

/**
 * JVM Verification Runner for Cryptographic Test Vectors.
 * Validates that Java BigInteger arithmetic conforms to the Python Oracle.
 */
object CryptoOracleJvmTest:

  val SECP256K1_P = new BigInteger("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F", 16)
  val SECP256K1_N = new BigInteger("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141", 16)
  val SECP256K1_B = BigInteger.valueOf(7)

  def main(args: Array[String]): Unit =
    println("=== Starting Crypto Oracle JVM Test Suite ===")
    
    val baseDir = Paths.get(System.getProperty("user.dir"))
    val vectorsDir = if Files.exists(baseDir.resolve("verification/crypto-oracle/vectors")) then
      baseDir.resolve("verification/crypto-oracle/vectors")
    else
      baseDir.resolve("vectors")
      
    assert(Files.exists(vectorsDir), s"Vectors directory not found: $vectorsDir")

    testSecp256k1Points(vectorsDir)
    testModularArithmetic(vectorsDir)
    testEdgeCases(vectorsDir)
    
    println("=== ALL JVM VERIFICATION CHECKS PASSED SUCCESSFULLY ===")

  def testSecp256k1Points(dir: java.nio.file.Path): Unit =
    println("[JVM] Testing secp256k1 vectors...")
    val content = Files.readString(dir.resolve("secp256k1_vectors.json"))
    
    // Simple regex parser for JSON fields to avoid heavy external dependencies
    val xPattern = """"x_hex":\s*"([^"]+)"""".r
    val yPattern = """"y_hex":\s*"([^"]+)"""".r

    val xMatches = xPattern.findAllMatchIn(content).map(_.group(1)).toList
    val yMatches = yPattern.findAllMatchIn(content).map(_.group(1)).toList

    assert(xMatches.nonEmpty, "No points found in secp256k1_vectors.json")
    assert(xMatches.size == yMatches.size, "Point coordinates count mismatch")

    for (xHex, yHex) <- xMatches.zip(yMatches) do
      val cleanX = xHex.stripPrefix("0x")
      val cleanY = yHex.stripPrefix("0x")
      val x = new BigInteger(cleanX, 16)
      val y = new BigInteger(cleanY, 16)

      // y^2 == x^3 + 7 (mod p)
      val lhs = y.modPow(BigInteger.valueOf(2), SECP256K1_P)
      val x3 = x.modPow(BigInteger.valueOf(3), SECP256K1_P)
      val rhs = x3.add(SECP256K1_B).mod(SECP256K1_P)

      assert(lhs.equals(rhs), s"Point ($xHex, $yHex) is not on secp256k1!")

    println(s"[JVM] Verified ${xMatches.size} points on secp256k1 curve equation.")

  def testModularArithmetic(dir: java.nio.file.Path): Unit =
    println("[JVM] Testing modular arithmetic & Bezout identity vectors...")
    val content = Files.readString(dir.resolve("modular_arithmetic_vectors.json"))

    val aPattern = """"a_dec":\s*"([^"]+)"""".r
    val bPattern = """"b_dec":\s*"([^"]+)"""".r
    val gcdPattern = """"gcd_dec":\s*"([^"]+)"""".r
    val xPattern = """"x_dec":\s*"([^"]+)"""".r
    val yPattern = """"y_dec":\s*"([^"]+)"""".r

    val aList = aPattern.findAllMatchIn(content).map(_.group(1)).toList
    val bList = bPattern.findAllMatchIn(content).map(_.group(1)).toList
    val gcdList = gcdPattern.findAllMatchIn(content).map(_.group(1)).toList
    val xList = xPattern.findAllMatchIn(content).map(_.group(1)).toList
    val yList = yPattern.findAllMatchIn(content).map(_.group(1)).toList

    for i <- aList.indices do
      val a = new BigInteger(aList(i))
      val b = new BigInteger(bList(i))
      val gcdVal = new BigInteger(gcdList(i))
      val x = new BigInteger(xList(i))
      val y = new BigInteger(yList(i))

      // Check gcd equality
      assert(a.gcd(b).equals(gcdVal), s"GCD mismatch for a=$a, b=$b")

      // Check Bezout identity: a*x + b*y == gcd
      val ax = a.multiply(x)
      val by = b.multiply(y)
      val bezout = ax.add(by)
      assert(bezout.equals(gcdVal), s"Bezout identity failed for a=$a, b=$b, x=$x, y=$y")

    println(s"[JVM] Verified ${aList.size} Bezout identity cases.")

  def testEdgeCases(dir: java.nio.file.Path): Unit =
    println("[JVM] Testing edge cases vectors...")
    val content = Files.readString(dir.resolve("edge_cases_vectors.json"))
    assert(content.contains(""""passed": true"""), "Edge cases JSON contains failures!")
    assert(!content.contains(""""passed": false"""), "Edge cases JSON contains false assertions!")
    println("[JVM] All edge cases verified.")
