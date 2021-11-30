import stainless.lang._

trait Heap[T] {
  def insert(element: T): Unit
  def delMin(): Option[T]
}
