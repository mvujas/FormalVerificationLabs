import stainless.lang._

object math {
  def signum(x: Int): Int = if(x > 0)
    1
  else if(x < 0)
    -1
  else
    0

  /**
   * Lemma proving that for an arbitary integer x not susceptible to overflow
   *  under negation the following holds: signum(x) = -signum(-x)
   */
  private def signumLemma1(x: Int): Unit = {
    require(x >= -2147483647 && x <= 2147483647)
  } ensuring (_ => signum(x) == -signum(-x))

  /**
   * Proof of lemma that might be useful for amortized complexity analysis of
   *  splay heaps, in original it states that 1 + log2(x) + log2(y) <=
   *    2 * log2(x + y - 1) for all x, y >= 2. However, stainless doesn't
   *    seem to support logs so the original statement of the lemma cannot be
   *    proven
   */
  def logLemmaInPowerForm(x: BigInt, y: BigInt): Boolean = {
    require(x >= 2 && y >= 2)
    val rhsSubExp = x + y - 1
    2 * x * y <= rhsSubExp * rhsSubExp
  }.holds

}
