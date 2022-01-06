import stainless.lang._
import stainless.annotation._

object StainlessUtils {
  /**
   *  Debugging feature that 'lies' to stainless that the given boolean holds
   */
  @extern
  def assume(b: Boolean): Unit = {} ensuring (_ => b)

  def echo(b: Boolean): Unit = {
    require(b)
  } ensuring (_ => b)

  /**
   *  Returns whether the given predicate holds for all the elements of the
   *    given set
   */
  def setForall[T](set: Set[T], predicate: T => Boolean): Boolean = forall {
    (el: T) => set.contains(el) ==> predicate(el)
  }
}
