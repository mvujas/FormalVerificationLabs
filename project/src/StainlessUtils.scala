import stainless.lang._
import stainless.annotation._

object StainlessUtils {
  @extern
  def assume(b: Boolean): Unit = {
  } ensuring (_ => b)

  def setForall[T](set: Set[T], predicate: T => Boolean): Boolean = forall {
    (el: T) => set.contains(el) ==> predicate(el)
  }
}
