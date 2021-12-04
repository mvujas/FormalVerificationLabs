import stainless.lang._
import stainless.annotation._

object StainlessUtils {
  @extern
  def assume(pred: () => Boolean): Unit = {
    assert(pred())
  }

  def setForall[T](set: Set[T], predicate: T => Boolean): Boolean = forall {
    (el: T) => set.contains(el) ==> predicate(el)
  }
}
