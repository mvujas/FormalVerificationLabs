import stainless.lang._
import stainless.annotation._
import stainless.proof._
import StainlessUtils._
import Trees._

// This gimick required as Stainless doesn't allow mutable variables out
//  of functions or class instantiations...
case class SplayHeap[T](val tree: Tree[T] = Leaf(), implicit val ord: Ordering[T]) extends FunctionalHeap[T] {
  require(isBinarySearchTree(tree)(ord))

  override def insert(element: T): FunctionalHeap[T] = {
    SplayHeap(tree, ord)
    // require(isBinarySearchTree(tree))
    // tree = insert(element, tree)(ord)
  }

  // Will have to change delMin(Tree[T]) to make it work with this
  //  Maybe split it into delMin and getMin or something like that
  override def delMin(): FunctionalHeap[T] = {
    SplayHeap(tree, ord)
  }
  

  override def getMin(): Option[T] = (tree match {
    case Leaf() => None[T]()
    case other => Some[T](getMinTreeEl(other)(ord))
  }) ensuring {
    res =>
      (!isTreeEmpty(tree) ==> {
        val minVal = res.get
        treeSet(tree).contains(minVal) &&
          setForall(treeSet(tree), (el: T) => ord.compare(el, minVal) >= 0)
      }) &&
      (isTreeEmpty(tree) ==> res.isEmpty)
  }

  // {
  //   (tree == Leaf[T]() && res.isEmpty) ^
  //   (tree != Leaf[T]() && {
  //      val Some(v) = res
  //      true
  //   })
    // (tree == Leaf() && res == None[T]()) ^
    // (tree != Leaf() && {
    //   val Some(v) = res
    //   setForall(treeSet(tree), (el: T) => ord.compare(el, v) >= 0)
    // })
  // })

  // private def insert(x: T, h: Tree[T])(implicit ord: Ordering[T]): Tree[T] = {
  //   require(isBinarySearchTree(h))
  //   val (l, r) = partition[T](x, h)
  //   Node(l, x, r)
  // } ensuring (res =>
  //   isBinarySearchTree(res) &&
  //   (treeSet(res) subsetOf (treeSet(h) ++ Set(x)))
  // )
  //
  //
  // private def treeDelMin(t: Tree[T])(implicit ord: Ordering[T]): Tree[T] = {
  //   require(isBinarySearchTree(t))
  //   t match {
  //     case Leaf() => Leaf[T]()
  //     case Node(Leaf(), uu, r) => r
  //     case node @ Node(innerNode @ Node(ll, a, lr), b, r) => ll match {
  //       case Leaf() => Node[T](lr, b, r)
  //       case _ => {
  //         // Working proof (sometimes) - have to be "sped up"
  //         val left = treeDelMin(ll)
  //         val right = Node[T](lr, b, r)
  //         val res = Node[T](left, a, right)
  //
  //         assert(isBinarySearchTree(left))
  //
  //         assert(
  //           ord.compare(b, a) >= 0 &&
  //           setForall(treeSet(r), (el: T) => {
  //             ord.compare(el, b) >= 0 && {
  //               ord.nonStrictTransitivityLemma(el, b, a)
  //               ord.compare(el, a) >= 0
  //             }
  //           }) &&
  //           setForall(treeSet(right), (el: T) => {
  //             ord.compare(el, a) >= 0
  //           })
  //         )
  //
  //         assert(setForall(treeSet(left), (el: T) => {
  //           ord.compare(a, el) >= 0
  //         }))
  //
  //         assert(isBinarySearchTree(right))
  //
  //         check{isBinarySearchTree(res) && (treeSet(res) subsetOf treeSet(t))}
  //
  //         res
  //       }
  //     }
  //   }
  // } ensuring (res => {
  //   isBinarySearchTree(res) && (treeSet(res) subsetOf treeSet(t))
  // })


}
