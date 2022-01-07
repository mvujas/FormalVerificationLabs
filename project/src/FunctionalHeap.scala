import stainless.lang._
import stainless.annotation._
import StainlessUtils._

trait FunctionalHeap[T] {
  /**
   *  Functionally inserts the element in the heap and returns a new
   *    functional heap as the result
   */
  def insert(element: T): FunctionalHeap[T]
  /**
   *  Functionally removes a minimum element from the heap if the heap is not
   *    empty and returns the resulting heap as the result. If the heap is empty
   *    the result is the same heap
   */
  def delMin(): FunctionalHeap[T]
  /**
   *  Returns the smallest element of the given functional heap if there is
   *    any. Otherwise, return None
   */
  def min: Option[T]
  /**
   *  Returns whether the given functional heap contains any elements
   */
  def isEmpty: Boolean
  /**
   *  Returns number of elements in the heap
   */
  def size: BigInt
  /**
   *  Returns all elemenets from the heap in form of a set
   */
  def set: Set[T]
  /**
   *  Returns ordering rule of the heap
   */
  def ordering: Ordering[T]

  /**
   *  Set of constraints that have to be held under insertion of a new element
   */
  @law
  def insertLaw(element: T): Boolean = {
    val res = this insert element
    (res.size == size + 1) && (res.set == set ++ Set(element))
  }

  /**
   *  Set of constraints that have to be held under deletion and retrieval of
   *    the minimal element of the heap
   */
  @law
  def minLaw: Boolean = {
    (isEmpty ==> (delMin.isEmpty && min.isEmpty)) &&
    (!isEmpty ==> (min.nonEmpty && isMinSetEl(set, ordering)(min.get) &&
      delMin.size + 1 == size && delMin.set ++ Set(min.get) == set))
  }
}
