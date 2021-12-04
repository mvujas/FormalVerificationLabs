import stainless.lang._
import stainless.annotation._

@mutable
trait CustomHeap[T] {
  // Maybe put and pop is better
  def insert(element: T): Unit
  def delMin(): Option[T]
}
