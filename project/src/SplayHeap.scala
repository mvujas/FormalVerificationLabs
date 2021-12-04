import stainless.lang._
import stainless.annotation._

// This gimick required as Stainless doesn't allow mutable variables out
//  of functions or class instantiations...
case class SplayHeap[T](var tree: Tree[T] = Leaf()) extends Heap[T] {

  override def insert(element: T)(implicit ord: Ordering[T]): Unit = {
    tree = insert(element, tree)(ord)
  }

  // Will have to change delMin(Tree[T]) to make it work with this
  //  Maybe split it into delMin and getMin or something like that
  override def delMin()(implicit ord: Ordering[T]): Option[T] = {
    None[T]
  }

  // Reports failure due to not knowing whether the function terminates.
  //  Weirdly, sometimes it can infer by itself in my runs...
  private def partition[T](p: T, tree: Tree[T])(implicit ord: Ordering[T]):
        (Tree[T], Tree[T]) = tree match {
    case Leaf() => (Leaf(), Leaf())
    case aTree @ Node(al, a, ar) if(ord.compare(a, p) <= 0) => ar match {
      case Leaf() => (aTree, Leaf())
      case Node(bl, b, br) if(ord.compare(b, p) <= 0) => {
        val (pl, y) = partition(p, br)
        (Node(Node(al, a, bl), b, pl), y)
      }
      case Node(bl, b, br) => {
        val (pl, pr) = partition(p, bl)
        (Node(al, a, pl), Node(pr, b, br))
      }
    }
    case aTree @ Node(al, a, ar) => al match {
      case Leaf() => (Leaf(), aTree)
      case Node(bl, b, br) if (ord.compare(b, p) <= 0) => {
        val (pl, pr) = partition(p, br)
        (Node(bl, b, pl), Node(pr, a, ar))
      }
      case Node(bl, b, br) => {
        val (pl, pr) = partition(p, bl)
        (pl, Node(pr, b, Node(br, a, ar)))
      }
    }
  }

  private def insert[T](x: T, h: Tree[T])(implicit ord: Ordering[T]): Tree[T] =
    partition(x, h)(ord) match {
      case (l, r) => Node(l, x, r)
    }

  private def delMin[T](t: Tree[T])(implicit ord: Ordering[T]): Tree[T] =
    t match {
      case Leaf() => Leaf()
      case Node(Leaf(), uu, r) => r
      case Node(Node(ll, a, lr), b, r) => ll match {
        case Leaf() => Node(lr, b, r)
        case _ => Node(delMin(ll), a, Node(lr, b, r))
      }
    }


  private def treeSet[T](tree: Tree[T]): Set[T] = tree match {
    case Leaf() => Set.empty[T]
    case Node(l, v, r) => Set(v) ++ treeSet(l) ++ treeSet(r)
  }

  private def isBinarySearchTree[T](tree: Tree[T])(implicit ord: Ordering[T]):
      Boolean = tree match {
    case Leaf() => true
    case Node(l, v, r) => isBinarySearchTree(l) && isBinarySearchTree(r) &&
      {
        // Abuse of Scala syntax since stainless.collection.setForall cannot be
        //  imported
        val leftSide: Set[T] = treeSet(l)
        forall { (el: T) => leftSide.contains(el) ==> ord.compare(v, el) >= 0 }
      } &&
      {
        val rightSide: Set[T] = treeSet(r)
        forall { (el: T) => rightSide.contains(el) ==> ord.compare(el, v) >= 0 }
      }
  }

  // Useful example
  private def treeSubset[T](t: Tree[T])(implicit ord: Ordering[T]): Unit = {
    require(isBinarySearchTree(t)(ord))
    t match {
      case Node(l, v, r) => {
        val lSet = treeSet(l)
        val rSet = treeSet(r)
        assert(forall {
          (lEl: T, rEl: T) => (lSet.contains(lEl) && rSet.contains(rEl)) ==> {
            ord.nonStrictTransitivityLemma(rEl, v, lEl)
            ord.compare(v, lEl) >= 0 && ord.compare(rEl, v) >= 0 &&
              ord.compare(rEl, lEl) >= 0

          }
        })
      }
      case other => ()
    }
  }


}
