import stainless.lang._
import stainless.annotation._

object StainlessUtils {
  /**
   *  Debugging feature that 'lies' to stainless that the given boolean holds.
   *    Set to private to make sure it is not used anywhere outside of this
   *    object
   */
  @extern
  private def assume(b: Boolean): Unit = {} ensuring (_ => b)

  /**
   *  Returns whether the given predicate holds for all the elements of the
   *    given set
   */
  def setForall[T](set: Set[T], predicate: T => Boolean): Boolean = forall {
    (el: T) => set.contains(el) ==> predicate(el)
  }

  /**
   *  Checks whether the given value is the minimal element of the set under
   *    the given ordering
   */
  def isMinSetEl[T](set: Set[T], ord: Ordering[T])(value: T): Boolean =
    set.contains(value) &&
    setForall(set, (el: T) => ord.compare(el, value) >= 0)
}
