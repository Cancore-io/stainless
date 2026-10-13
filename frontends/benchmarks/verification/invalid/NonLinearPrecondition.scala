import stainless.lang._
import stainless.math.NonLinear._

// A divisor that is not positive is rejected at the call site.
object NonLinearPrecondition {
  def zeroDivisor(y: BigInt): Unit = {
    require(y >= 0)
    ghost(divBounds(y, 0))
  }

  def negativeDivisor(n: BigInt): BigInt = {
    roundHalfEven(n, -1)
  }

  def scaledNegativeDivisor(n1: BigInt, n2: BigInt): Unit = {
    require(n1 >= 0)
    ghost(crossMultiply(n1, BigInt(-10000000000L), n2, 1))
  }

  // floor characterisation is stated for y >= 0: a negative dividend is refused.
  def negativeDividend(): Unit = {
    ghost(divBounds(-7, 2))
  }
}
