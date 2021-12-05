import stainless.lang._
import stainless.annotation._
import stainless.proof._
import StainlessUtils._

// This gimick required as Stainless doesn't allow mutable variables out
//  of functions or class instantiations...
case class SplayHeap[T](var tree: Tree[T] = Leaf()) extends CustomHeap[T] {

  override def insert(element: T)(implicit ord: Ordering[T]): Unit = {
    // require(isBinarySearchTree(tree))
    // tree = insert(element, tree)(ord)
  }

  // Will have to change delMin(Tree[T]) to make it work with this
  //  Maybe split it into delMin and getMin or something like that
  override def delMin()(implicit ord: Ordering[T]): Option[T] = {
    None[T]()
  }

  // Reports failure due to not knowing whether the function terminates.
  //  Weirdly, sometimes it can infer by itself in my runs...
  //  Also fulling full tuple2 constructor recommended as Stainless complains
  //    otherwise.
  @extern
  private def partition(p: T, tree: Tree[T])(implicit ord: Ordering[T]):
        (Tree[T], Tree[T]) = {
    // Metric
    decreases(tree)
    // Precondition
    require(isBinarySearchTree(tree))
    // Logic
    tree match {
      case Leaf() => Tuple2[Tree[T], Tree[T]](Leaf(), Leaf())
      case aTree @ Node(al, a, ar) if(ord.compare(a, p) <= 0) => {
        assert(ord.inverse(a, p))
        assert(ord.compare(p, a) >= 0)
        assert(isBinarySearchTree(al))
        assert(setForall(treeSet(al), (el: T) => {
          val tmp = ord.compare(p, a) >= 0 && ord.compare(a, el) >= 0
          ord.nonStrictTransitivityLemma(p, a, el)
          tmp
        }))
        // assert(setForall(treeSet(al), (el: T) => {
        //   ord.nonStrictTransitivityLemma(p, a, el)
        //   ord.compare(p, el) >= 0
        // }))
        // assert(setForall(treeSet(al), (el: T) => {
        //   ord.nonStrictTransitivityLemma(p, a, el)
        //   ord.compare(p, el) >= 0
        // }))

        ar match {
          case Leaf() => {
            Tuple2[Tree[T], Tree[T]](aTree, Leaf())
          }
          case other => Tuple2[Tree[T], Tree[T]](Leaf(), Leaf())
        }
        //   case Node(bl, b, br) if(ord.compare(b, p) <= 0) => {
        //     val (pl, y) = partition(p, br)
        //     Tuple2[Tree[T], Tree[T]](Node(Node(al, a, bl), b, pl), y)
        //   }
        //   case Node(bl, b, br) => {
        //     assert(treeSet(bl) subsetOf treeSet(tree))
        //     val (pl, pr) = partition(p, bl)
        //     Tuple2[Tree[T], Tree[T]](Node(al, a, pl), Node(pr, b, br))
        //   }
        // }
      }
      case aTree @ Node(al, a, ar) => al match {
        case any => Tuple2[Tree[T], Tree[T]](Leaf(), Leaf())
        // case Leaf() => Tuple2[Tree[T], Tree[T]](Leaf(), aTree)
        // case Node(bl, b, br) if (ord.compare(b, p) <= 0) => {
        //   val (pl, pr) = partition(p, br)
        //   Tuple2[Tree[T], Tree[T]](Node(bl, b, pl), Node(pr, a, ar))
        // }
        // case Node(bl, b, br) => {
        //   val (pl, pr) = partition(p, bl)
        //   Tuple2[Tree[T], Tree[T]](pl, Node(pr, b, Node(br, a, ar)))
        // }
      }
    }
  } ensuring {
    res => {
      // Last two probably unnecessary
      isBinarySearchTree(res._1) && isBinarySearchTree(res._2) &&
      setForall(treeSet(res._1), (el: T) => ord.compare(p, el) >= 0) &&
      setForall(treeSet(res._2), (el: T) => ord.compare(el, p) >= 0) &&
      (treeSet(res._1) subsetOf treeSet(tree)) &&
      (treeSet(res._2) subsetOf treeSet(tree))
    }
  }

  // private def treeOrderingTransitivity(tree: Tree[T], p: T)(implicit ord: Ordering[T]): Unit = {
  //   require(tree != Leaf())
  //
  // }

  private def insert(x: T, h: Tree[T])(implicit ord: Ordering[T]): Tree[T] = {
    require(isBinarySearchTree(h))
    val (l, r) = partition(x, h)
    Node(l, x, r)
  } ensuring (isBinarySearchTree(_))


  private def treeDelMin(t: Tree[T])(implicit ord: Ordering[T]): Tree[T] = {
    require(isBinarySearchTree(t))
    t match {
      case Leaf() => Leaf[T]()
      case Node(Leaf(), uu, r) => r
      case node @ Node(innerNode @ Node(ll, a, lr), b, r) => ll match {
        case Leaf() => Node[T](lr, b, r)
        case _ => {
          // Working proof (sometimes) - have to be "sped up"
          val left = treeDelMin(ll)
          val right = Node[T](lr, b, r)
          val res = Node[T](left, a, right)

          assert(isBinarySearchTree(left))

          assert(
            ord.compare(b, a) >= 0 &&
            setForall(treeSet(r), (el: T) => {
              ord.compare(el, b) >= 0 && {
                ord.nonStrictTransitivityLemma(el, b, a)
                ord.compare(el, a) >= 0
              }
            }) &&
            setForall(treeSet(right), (el: T) => {
              ord.compare(el, a) >= 0
            })
          )

          assert(setForall(treeSet(left), (el: T) => {
            ord.compare(a, el) >= 0
          }))

          assert(isBinarySearchTree(right))

          check{isBinarySearchTree(res) && (treeSet(res) subsetOf treeSet(t))}

          res
        }
      }
    }
  } ensuring (res => {
    isBinarySearchTree(res) && (treeSet(res) subsetOf treeSet(t))
  })

  private def treeSet(tree: Tree[T]): Set[T] = tree match {
    case Leaf() => Set.empty[T]
    case Node(l, v, r) => Set(v) ++ treeSet(l) ++ treeSet(r)
  }

  private def isBinarySearchTree(tree: Tree[T])(implicit ord: Ordering[T]):
      Boolean = tree match {
    case Leaf() => true
    case Node(l, v, r) => isBinarySearchTree(l) && isBinarySearchTree(r) &&
      setForall(treeSet(l), (el: T) => ord.compare(v, el) >= 0) &&
      setForall(treeSet(r), (el: T) => ord.compare(el, v) >= 0)
  }

  // Useful example
  private def treeSubset(t: Tree[T])(implicit ord: Ordering[T]): Unit = {
    require(isBinarySearchTree(t)(ord))
    t match {
      case Node(l, v, r) => {
        val lSet = treeSet(l)
        val rSet = treeSet(r)
        assert(forall {
          (lEl: T, rEl: T) => (lSet.contains(lEl) && rSet.contains(rEl)) ==> {
            // check {ord.compare(rEl, v) >= 0}
            // check {ord.compare(v, lEl) >= 0}
            ord.nonStrictTransitivityLemma(rEl, v, lEl)
            ord.compare(rEl, lEl) >= 0
          }
        })
      }
      case other => ()
    }
  }


}
