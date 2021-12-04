import stainless.annotation._

object StainlessUtils {
  @extern
  def assume(pred: () => Boolean): Unit = {
    assert(pred())
  }
}
