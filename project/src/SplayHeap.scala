import stainless.lang._
import stainless.annotation._
import stainless.collection._
import stainless.proof._
import StainlessUtils._
import Trees._

object SplayHeap {
  /**
   *  Returns a new empty heap with the given ordering
   */
  def createEmpty[T](implicit ord: Ordering[T]): SplayHeap[T] = {
    new SplayHeap[T](Leaf[T](), ord)
  } ensuring (_.isEmpty)

  /**
   *  Returns a heap containing all elements of the given list
   */
  def createFromList[T](l: List[T])(implicit ord: Ordering[T]):
    FunctionalHeap[T] = (
      l match {
        case Nil() => createEmpty[T](ord)
        case Cons(x, xs) => {
          val subHeap = createFromList[T](xs)
          assert(subHeap.insertLaw(x))
          subHeap insert x
        }
      }
    ) ensuring {
      (res: FunctionalHeap[T]) => res.size == l.size && l.content == res.set
    }
}

// In order to save an end user from having to pass a tree everytime it wants
//  to construct a heap, the constructor is set to be private and all
//  instantiations of the class are done using the companion object
case class SplayHeap[T] private(val tree: Tree[T], implicit val ord: Ordering[T]) extends FunctionalHeap[T] {
  require(isBinarySearchTree(tree)(ord))

  override def insert(element: T): FunctionalHeap[T] = {
    SplayHeap(binarySearchTreeSplayInsertion(tree, element)(ord), ord)
  }

  override def delMin(): FunctionalHeap[T] = tree match {
    case Leaf() => SplayHeap(Leaf(), ord)
    case other => SplayHeap(getMinTreeEl(other)(ord)._1, ord)
  }

  override def min: Option[T] = tree match {
    case Leaf() => None[T]()
    case other => Some[T](getMinTreeEl(other)(ord)._2)
  }

  override def isEmpty: Boolean = isTreeEmpty(tree)
  override def size: BigInt = treeSize(tree)
  override def set: Set[T] = treeSet(tree)
  override def ordering: Ordering[T] = ord
}
