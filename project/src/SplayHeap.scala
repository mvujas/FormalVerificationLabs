import stainless.lang._
import stainless.annotation._
import stainless.proof._
import StainlessUtils._
import Trees._

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
  //  Proof of postcondition takes time,  around 15 seconds from runs.
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
        check{
          ord.inverse(a, p) &&
          ord.compare(p, a) >= 0 &&
          setForall(treeSet(al), (el: T) => {
            ord.compare(a, el) >= 0 && {
              ord.nonStrictTransitivityLemma(p, a, el)
              ord.compare(p, el) >= 0
            }
          })
        }

        ar match {
          case Leaf() => Tuple2[Tree[T], Tree[T]](aTree, Leaf())
          case Node(bl, b, br) if(ord.compare(b, p) <= 0) => {
            val (pl, y) = partition(p, br)
            val _1_left = Node(al, a, bl)
            val _1 = Node(_1_left, b, pl)
            val _2 = y

            assert {
              (Set(b) subsetOf treeSet(ar)) &&
              ord.compare(b, a) >= 0 &&
              // Proof _1_left is a binary search tree
              (treeSet(bl) subsetOf treeSet(ar)) &&
              setForall(treeSet(bl), (el: T) => ord.compare(el, a) >= 0) &&
              setForall(treeSet(al), (el: T) => ord.compare(a, el) >= 0) &&
              isBinarySearchTree(al) &&
              isBinarySearchTree(ar) &&
              isBinarySearchTree(bl) &&
              isBinarySearchTree(_1_left) &&
              // Proof that treeSet(_1_left) is <= b
              setForall(treeSet(al), (el: T) => {
                ord.compare(a, el) >= 0 && {
                  ord.nonStrictTransitivityLemma(b, a, el)
                  ord.compare(b, el) >= 0
                }
              }) &&
              setForall(treeSet(_1_left), (el: T) => ord.compare(b, el) >= 0) &&
              // Proof that treeSet(pl) is <= b
              (treeSet(pl) subsetOf treeSet(br)) &&
              setForall(treeSet(pl), (el: T) => ord.compare(el, b) >= 0) &&
              // Proof pl is a binary search tree
              isBinarySearchTree(pl) &&
              // Proof _1 is a binary search tree
              isBinarySearchTree(_1)
            }

            assert {
              {
                // p >= b
                ord.monotonicInverseLemmaSmaller(b, p)
                ord.compare(p, b) >= 0
              } &&
              setForall(treeSet(_1_left), (el: T) => {
                ord.compare(b, el) >= 0 && {
                  ord.nonStrictTransitivityLemma(p, b, el)
                  ord.compare(p, el) >= 0
                }
              }) &&
              setForall(treeSet(pl), (el: T) => ord.compare(p, el) >= 0)
            }


            val res = Tuple2[Tree[T], Tree[T]](_1, _2)

            check {
              (treeSet(res._1) subsetOf treeSet(tree)) &&
              isBinarySearchTree(res._1) &&
              setForall(treeSet(res._1), (el: T) => ord.compare(p, el) >= 0) &&
              (treeSet(res._2) subsetOf treeSet(tree)) &&
              isBinarySearchTree(res._2) &&
              setForall(treeSet(res._2), (el: T) => ord.compare(el, p) >= 0)
            }
            res
          }
          case other => Tuple2[Tree[T], Tree[T]](Leaf(), Leaf())
        }
        //
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


}
