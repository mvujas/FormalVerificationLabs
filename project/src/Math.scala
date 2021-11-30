object math {
  def signum(x: Int): Int = if(x > 0)
    1
  else if(x < 0)
    -1
  else
    0

  private def signumLemma1(x: Int): Unit = {
    require(x >= -2147483647 && x <= 2147483647)
  } ensuring (_ => signum(x) == -signum(-x))

  private def signumLemma2(x: Int): Unit = {
    require(x >= -2147483647 && x <= 2147483647)
  } ensuring (_ => signum(x) * signum(-x) != 1)
}
