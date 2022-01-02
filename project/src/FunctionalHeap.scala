import stainless.lang._
import stainless.annotation._

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
  def getMin(): Option[T]
  def isEmpty(): Boolean
}
