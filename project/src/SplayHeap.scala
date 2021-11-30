import stainless.lang._

case class SplayHeap[T](ordering: Ordering[T]) extends Heap[T] {
  override def insert(element: T): Unit = {

  }

  override def delMin(): Option[T] = {
    None[T]
  }
}
