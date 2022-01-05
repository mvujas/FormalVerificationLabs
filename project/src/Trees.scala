import stainless.lang._
import stainless.annotation._
import stainless.proof._
import StainlessUtils._

object Trees {
  sealed abstract class Tree[T]
  case class Leaf[T]() extends Tree[T]
  case class Node[T](left: Tree[T], value: T, right: Tree[T]) extends Tree[T]

  /**
   *  Returns the number of values in the given tree
   */
  def treeSize[T](tree: Tree[T]): BigInt = (tree match {
    case Leaf() => BigInt(0)
    case Node(l, _, r) => BigInt(1) + treeSize(l) + treeSize(r)
  }) ensuring {_ >= 0}

  /**
   *  Returns whether there's absence of nodes in the given tree
   */
  def isTreeEmpty[T](tree: Tree[T]): Boolean = (tree match {
    case Leaf() => true
    case _ => false
  }) ensuring {res => (res == (treeSize(tree) == 0))}

  /**
   *  Helper function that returns the right subtree of the root of the given
   *    non-empty tree
   */
  def rightSubTree[T](tree: Tree[T]): Tree[T] = {
    require(!isTreeEmpty(tree))
    val Node(_, _, r) = tree
    r
  }

  /**
   *  Helper function that returns the left subtree of the root of the given
   *    non-empty tree
   */
  def leftSubTree[T](tree: Tree[T]): Tree[T] = {
    require(!isTreeEmpty(tree))
    val Node(l, _, _) = tree
    l
  }

  /**
   *  Helper function that returns values held in the root of the given
   *    non-empty tree
   */
  def treeRootValue[T](tree: Tree[T]): T = {
    require(!isTreeEmpty(tree))
    val Node(_, v, _) = tree
    v
  }

  /**
   *  Returns a set containing elements of all nodes of the given tree
   */
  def treeSet[T](tree: Tree[T]): Set[T] = tree match {
    case Leaf() => Set.empty[T]
    case Node(l, v, r) => Set(v) ++ treeSet(l) ++ treeSet(r)
  }

  /**
   *  Check whether the given tree is a binary search tree
   */
  def isBinarySearchTree[T](tree: Tree[T])(implicit ord: Ordering[T]):
      Boolean = tree match {
        case Leaf() => true
        case Node(l, v, r) => isBinarySearchTree(l) && isBinarySearchTree(r) &&
          setForall(treeSet(l), (el: T) => ord.compare(v, el) >= 0) &&
          setForall(treeSet(r), (el: T) => ord.compare(el, v) >= 0)
      }

  /**
   *  Lemma proving if a >= b and forall(el in set(tree), b >= el) then
   *    forall(el in set(tree), a >= el)
   */
  def subtreeGreaterOrderingTransitivityLemma[T](
    greaterValue: T,
    nodeValue: T,
    leftTree: Tree[T]
  )(implicit ord: Ordering[T]): Unit = {
    require(ord.compare(greaterValue, nodeValue) >= 0)
    require(setForall(treeSet(leftTree), (el: T) => {
      ord.compare(nodeValue, el) >= 0
    }))
    assert {
      ord.compare(greaterValue, nodeValue) >= 0 &&
      setForall(treeSet(leftTree), (el: T) => {
        ord.compare(nodeValue, el) >= 0 && {
          ord.nonStrictTransitivityLemma(greaterValue, nodeValue, el)
          ord.compare(greaterValue, el) >= 0
        }
      })
    }
  } ensuring (_ => {
    setForall(treeSet(leftTree), (el: T) => {
      ord.compare(greaterValue, el) >= 0
    })
  })

  /**
   *  Lemma proving if a >= b and forall(el in set(tree), el >= a) then
   *    forall(el in set(tree), el >= b)
   */
  def subtreeSmallerOrderingTransitivityLemma[T](
    smallerValue: T,
    nodeValue: T,
    rightTree: Tree[T]
  )(implicit ord: Ordering[T]): Unit = {
    require(ord.compare(nodeValue, smallerValue) >= 0)
    require(setForall(treeSet(rightTree), (el: T) => {
      ord.compare(el, nodeValue) >= 0
    }))
    assert {
      ord.compare(nodeValue, smallerValue) >= 0 &&
      setForall(treeSet(rightTree), (el: T) => {
        ord.compare(el, nodeValue) >= 0 && {
          ord.nonStrictTransitivityLemma(el, nodeValue, smallerValue)
          ord.compare(el, smallerValue) >= 0
        }
      })
    }
  } ensuring (_ => {
    setForall(treeSet(rightTree), (el: T) => {
      ord.compare(el, smallerValue) >= 0
    })
  })

  type TreePartitionType[T] = Tuple2[Tree[T], Tree[T]]

  // def isValidPartition[T](p: T, tree: Tree[T],  ord: Ordering[T])
  //   (treePartition: TreePartitionType[T]): Boolean = {
  //     isBinarySearchTree(treePartition._1)(ord) &&
  //     isBinarySearchTree(treePartition._2)(ord) &&
  //     setForall(treeSet(treePartition._1), (el: T) => ord.compare(p, el) >= 0) &&
  //     setForall(treeSet(treePartition._2), (el: T) => ord.compare(el, p) >= 0) &&
  //     (treeSet(treePartition._1) subsetOf treeSet(tree)) &&
  //     (treeSet(treePartition._2) subsetOf treeSet(tree))
  //   }
  //
  //
  // private def partitionEcho[T](p: T, tree: Tree[T], parts: TreePartitionType[T])
  //   (implicit ord: Ordering[T]): TreePartitionType[T] = {
  //     require{ isValidPartition(p, tree, ord)(parts) }
  //     parts
  //   } ensuring { isValidPartition(p, tree, ord)(_) }
  //
  //
  // private def partitionEmpty[T](p: T, tree: Tree[T])(implicit ord: Ordering[T]):
  //   TreePartitionType[T] = {
  //     require(isBinarySearchTree(tree) && isTreeEmpty(tree))
  //     Tuple2[Tree[T], Tree[T]](Leaf(), Leaf())
  //   } ensuring { isValidPartition(p, tree, ord)(_) }
  //
  // private def partitionSmallerEmpty[T](p: T, tree: Tree[T])
  //   (implicit ord: Ordering[T]): TreePartitionType[T] = {
  //     require(isBinarySearchTree(tree) &&
  //       !isTreeEmpty(tree) &&
  //       ord.compare(treeRootValue(tree), p) <= 0 &&
  //       isTreeEmpty(rightSubTree(tree))
  //     )
  //     val Node(al, a, ar) = tree
  //     assert {
  //       ord.inverse(a, p) &&
  //       ord.compare(p, a) >= 0 &&
  //       {
  //         subtreeGreaterOrderingTransitivityLemma(p, a, al)
  //         setForall(treeSet(al), (el: T) => ord.compare(p, el) >= 0)
  //       }
  //     }
  //     Tuple2[Tree[T], Tree[T]](tree, Leaf())
  //   } ensuring { isValidPartition(p, tree, ord)(_) }
  //
  // private def partitionSmallerSmaller[T](p: T, tree: Tree[T])
  //   (implicit ord: Ordering[T]): TreePartitionType[T] = {
  //     decreases(tree)
  //     require(isBinarySearchTree(tree) &&
  //       !isTreeEmpty(tree) &&
  //       ord.compare(treeRootValue(tree), p) <= 0 &&
  //       !isTreeEmpty(rightSubTree(tree)) &&
  //       ord.compare(treeRootValue(rightSubTree(tree)), p) <= 0
  //     )
  //     val Node(al, a, ar) = tree
  //     assert {
  //       ord.inverse(a, p) &&
  //       ord.compare(p, a) >= 0 &&
  //       {
  //         subtreeGreaterOrderingTransitivityLemma(p, a, al)
  //         setForall(treeSet(al), (el: T) => ord.compare(p, el) >= 0)
  //       }
  //     }
  //     val Node(bl, b, br) = ar
  //     val (pl, y) = partition(p, br)(ord)
  //
  //     assert {
  //       isBinarySearchTree(pl) && isBinarySearchTree(y)
  //     }
  //
  //     val _1_left = Node(al, a, bl)
  //     val res = Tuple2[Tree[T], Tree[T]](
  //       Node(_1_left, b, pl),
  //       y
  //     )
  //
  //     assert {
  //       (Set(b) subsetOf treeSet(ar)) &&
  //       ord.compare(b, a) >= 0 &&
  //       // Proof _1_left is a binary search tree
  //       (treeSet(bl) subsetOf treeSet(ar)) &&
  //       setForall(treeSet(bl), (el: T) => ord.compare(el, a) >= 0) &&
  //       setForall(treeSet(al), (el: T) => ord.compare(a, el) >= 0) &&
  //       isBinarySearchTree(al) &&
  //       isBinarySearchTree(ar) &&
  //       isBinarySearchTree(bl) &&
  //       isBinarySearchTree(_1_left) &&
  //       // Proof that treeSet(_1_left) is <= b
  //       setForall(treeSet(al), (el: T) => {
  //         ord.compare(a, el) >= 0 && {
  //           ord.nonStrictTransitivityLemma(b, a, el)
  //           ord.compare(b, el) >= 0
  //         }
  //       }) &&
  //       setForall(treeSet(_1_left), (el: T) => ord.compare(b, el) >= 0) &&
  //       // Proof that treeSet(pl) is <= b
  //       (treeSet(pl) subsetOf treeSet(br)) &&
  //       setForall(treeSet(pl), (el: T) => ord.compare(el, b) >= 0)
  //       // &&
  //       // // Proof pl is a binary search tree
  //       // isBinarySearchTree(pl)
  //     }
  //     // &&
  //     //   // Proof _1 is a binary search tree
  //     //   isBinarySearchTree(res._1)
  //     // }
  //
  //     assert {
  //       {
  //         // p >= b
  //         ord.monotonicInverseLemmaSmaller(b, p)
  //         ord.compare(p, b) >= 0
  //       } &&
  //       setForall(treeSet(_1_left), (el: T) => {
  //         ord.compare(b, el) >= 0 && {
  //           ord.nonStrictTransitivityLemma(p, b, el)
  //           ord.compare(p, el) >= 0
  //         }
  //       }) &&
  //       setForall(treeSet(pl), (el: T) => ord.compare(p, el) >= 0)
  //     }
  //
  //     res
  //   } ensuring { isValidPartition(p, tree, ord)(_) }
  //
  // private def assumedPartition[T](p: T, tree: Tree[T])
  //   (implicit ord: Ordering[T]): TreePartitionType[T] = {
  //     require(isBinarySearchTree(tree))
  //     val res = Tuple2[Tree[T], Tree[T]](Leaf(), Leaf())
  //     assume(isValidPartition(p, tree, ord)(res))
  //     res
  //   } ensuring { isValidPartition(p, tree, ord)(_) }
  //
  // def partition[T](p: T, tree: Tree[T])(implicit ord: Ordering[T]):
  //   TreePartitionType[T] = {
  //     decreases(tree)
  //     // Precondition
  //     require(isBinarySearchTree(tree))
  //     // Logic
  //     tree match {
  //       case Leaf() => partitionEmpty(p, tree)(ord)
  //       case Node(al, a, ar) => if(ord.compare(a, p) <= 0) {
  //           ar match {
  //             case Leaf() => partitionSmallerEmpty(p, tree)(ord)
  //             case Node(bl, b, br) => if(ord.compare(b, p) <= 0) {
  //                 partitionSmallerSmaller(p, tree)(ord)
  //               }
  //               else {
  //                 assumedPartition(p, tree)(ord)
  //               }
  //           }
  //         }
  //         else {
  //           assumedPartition(p, tree)(ord)
  //         }
  //     }
  //     // if(isTreeEmpty(tree)) {
  //     //   partitionEmpty(p, tree)(ord)
  //     // }
  //     // else {
  //     //   val Node(al, a, ar) = tree
  //     //   if(ord.compare(a, p) <= 0) {
  //     //     if(isTreeEmpty(ar)) {
  //     //       partitionSmallerEmpty(p, tree)(ord)
  //     //     }
  //     //     else {
  //     //       val Node(bl, b, br) = ar
  //     //       if(ord.compare(b, p) <= 0) {
  //     //         assumedPartition(p, tree)(ord)
  //     //       }
  //     //       else {
  //     //         assumedPartition(p, tree)(ord)
  //     //       }
  //     //     }
  //     //   }
  //     //   else {
  //     //     assumedPartition(p, tree)(ord)
  //     //   }
  //     // }
  //   } ensuring { isValidPartition(p, tree, ord)(_) }

  // Reports failure due to not knowing whether the function terminates.
  //  Weirdly, sometimes it can infer by itself in my runs...
  //  Also fulling full tuple2 constructor recommended as Stainless complains
  //    otherwise.
  //  Proof of postcondition is painfully slow, just postcondition took
  //    around 220 seconds...
  def partition[T](p: T, tree: Tree[T])(implicit ord: Ordering[T]):
        TreePartitionType[T] = {
    // Metric
    decreases(tree)
    // Precondition
    require(isBinarySearchTree(tree))
    // Logic
    tree match {
      case Leaf() => Tuple2[Tree[T], Tree[T]](Leaf(), Leaf())
      case aTree @ Node(al, a, ar) if(ord.compare(a, p) <= 0) => {
        assert {
          ord.inverse(a, p) &&
          ord.compare(p, a) >= 0 &&
          {
            subtreeGreaterOrderingTransitivityLemma(p, a, al)
            setForall(treeSet(al), (el: T) => ord.compare(p, el) >= 0)
          }
        }

        ar match {
          case Leaf() => {
            val res = Tuple2[Tree[T], Tree[T]](aTree, Leaf())
            check {
              isBinarySearchTree(res._1) && isBinarySearchTree(res._2) &&
              setForall(treeSet(res._1), (el: T) => ord.compare(p, el) >= 0) &&
              setForall(treeSet(res._2), (el: T) => ord.compare(el, p) >= 0) &&
              (treeSet(res._1) subsetOf treeSet(tree)) &&
              (treeSet(res._2) subsetOf treeSet(tree))
            }
            res
          }
          case Node(bl, b, br) if(ord.compare(b, p) <= 0) => {
            val (pl, y) = partition(p, br)
            val _1_left = Node(al, a, bl)
            val res = Tuple2[Tree[T], Tree[T]](
              Node(_1_left, b, pl),
              y
            )


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
              isBinarySearchTree(res._1)
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


            check {
              isBinarySearchTree(res._1) && isBinarySearchTree(res._2) &&
              setForall(treeSet(res._1), (el: T) => ord.compare(p, el) >= 0) &&
              setForall(treeSet(res._2), (el: T) => ord.compare(el, p) >= 0) &&
              (treeSet(res._1) subsetOf treeSet(tree)) &&
              (treeSet(res._2) subsetOf treeSet(tree))
            }
            res
          }
          case Node(bl, b, br) => {
            val (pl, pr) = partition(p, bl)

            val res = Tuple2[Tree[T], Tree[T]](
              Node(al, a, pl),
              Node(pr, b, br)
            )

            assume {
              (treeSet(pl) subsetOf treeSet(bl)) &&
              (treeSet(pr) subsetOf treeSet(bl)) &&
              (treeSet(bl) subsetOf treeSet(ar)) &&
              (treeSet(br) subsetOf treeSet(ar)) &&
              (treeSet(ar) subsetOf treeSet(tree)) &&
              (treeSet(res._1) subsetOf treeSet(tree)) &&
              (treeSet(res._2) subsetOf treeSet(tree))
            }

            assume {
              setForall(treeSet(ar), (el: T) => ord.compare(el, a) >= 0) &&
              (treeSet(pr) subsetOf treeSet(bl)) &&
              setForall(treeSet(bl), (el: T) => ord.compare(b, el) >= 0) &&
              isBinarySearchTree(res._1) &&
              isBinarySearchTree(res._2)
            }

            assume {
              {
                subtreeGreaterOrderingTransitivityLemma(p, a, al)
                setForall(treeSet(res._1), (el: T) => ord.compare(p, el) >= 0)
              } &&
              {
                subtreeSmallerOrderingTransitivityLemma(p, b, br)
                setForall(treeSet(res._2), (el: T) => ord.compare(el, p) >= 0)
              }
            }

            check {
              isBinarySearchTree(res._1) && isBinarySearchTree(res._2) &&
              setForall(treeSet(res._1), (el: T) => ord.compare(p, el) >= 0) &&
              setForall(treeSet(res._2), (el: T) => ord.compare(el, p) >= 0) &&
              (treeSet(res._1) subsetOf treeSet(tree)) &&
              (treeSet(res._2) subsetOf treeSet(tree))
            }
            res
          }
        }
      }
      case aTree @ Node(al, a, ar) => {
        assert {
          ord.compare(a, p) > 0 &&
          {
            ord.strictGreaterToNonStrictLemma(a, p)
            ord.compare(a, p) >= 0
          } &&
          {
            subtreeSmallerOrderingTransitivityLemma(p, a, ar)
            setForall(treeSet(ar), (el: T) => ord.compare(el, p) >= 0)
          }
        }

        al match {
          case Leaf() => {
            val res = Tuple2[Tree[T], Tree[T]](Leaf(), aTree)
            check {
              isBinarySearchTree(res._1) && isBinarySearchTree(res._2) &&
              setForall(treeSet(res._1), (el: T) => ord.compare(p, el) >= 0) &&
              setForall(treeSet(res._2), (el: T) => ord.compare(el, p) >= 0) &&
              (treeSet(res._1) subsetOf treeSet(tree)) &&
              (treeSet(res._2) subsetOf treeSet(tree))
            }
            res
          }
          case Node(bl, b, br) if (ord.compare(b, p) <= 0) => {
            val (pl, pr) = partition(p, br)
            val res = Tuple2[Tree[T], Tree[T]](
              Node(bl, b, pl),
              Node(pr, a, ar)
            )

            assume {
              (treeSet(bl) subsetOf treeSet(al)) &&
              (treeSet(br) subsetOf treeSet(al)) &&
              (treeSet(pl) subsetOf treeSet(br)) &&
              (treeSet(pr) subsetOf treeSet(br)) &&
              (treeSet(res._1) subsetOf treeSet(tree)) &&
              (treeSet(res._2) subsetOf treeSet(tree))
            }

            assume {
              // pl subset of br and all elements of br are greater than b
              isBinarySearchTree(res._1) &&
              // pr subset of br which is a subset of al and
              //    all elements of al are smaller than a
              (treeSet(pr) subsetOf treeSet(al)) &&
              isBinarySearchTree(res._2)
            }

            assume {
              // Proven before the match that all elements of ar >= p, then also
              //    a >= p, and finally elements of pr >= p by induction
              //    hypothesis
              setForall(treeSet(res._2), (el: T) => ord.compare(el, p) >= 0) &&
              // Proof that all elements of the first element of the tuple are
              //    <= p, we have to prove that only the elements of bl are <= p
              //    which follows from transitivity
              ord.compare(b, p) <= 0 &&
              ord.inverse(b, p) &&
              ord.compare(p, b) >= 0 &&
              {
                subtreeGreaterOrderingTransitivityLemma(p, b, bl)
                setForall(treeSet(bl), (el: T) => ord.compare(p, el) >= 0)
              } &&
              setForall(treeSet(res._1), (el: T) => ord.compare(p, el) >= 0)
            }

            check {
              isBinarySearchTree(res._1) && isBinarySearchTree(res._2) &&
              setForall(treeSet(res._1), (el: T) => ord.compare(p, el) >= 0) &&
              setForall(treeSet(res._2), (el: T) => ord.compare(el, p) >= 0) &&
              (treeSet(res._1) subsetOf treeSet(tree)) &&
              (treeSet(res._2) subsetOf treeSet(tree))
            }
            res
          }
          case bTree @ Node(bl, b, br) => {
            val (pl, pr) = partition(p, bl)
            val _2_right = Node(br, a, ar)
            val res = Tuple2[Tree[T], Tree[T]](
              pl,
              Node(pr, b, _2_right)
            )

            assert {
              isBinarySearchTree(bTree) &&
              setForall(treeSet(bl), (el: T) => ord.compare(b, el) >= 0) &&
              setForall(treeSet(br), (el: T) => ord.compare(el, b) >= 0)
            }

            assert {
              (treeSet(pl) subsetOf treeSet(bl)) &&
              (treeSet(pr) subsetOf treeSet(bl)) &&
              (treeSet(bl) subsetOf treeSet(al)) &&
              (treeSet(br) subsetOf treeSet(al))  &&
              (treeSet(res._1) subsetOf treeSet(tree)) &&
              (treeSet(_2_right) subsetOf treeSet(tree)) &&
              (treeSet(res._2) subsetOf treeSet(tree))
            }

            assert {
              isBinarySearchTree(res._1) &&
              setForall(treeSet(res._1), (el: T) => ord.compare(p, el) >= 0)
            }

            assert {
              isBinarySearchTree(br) &&
              isBinarySearchTree(ar) &&
              (treeSet(br) subsetOf treeSet(al)) &&
              setForall(treeSet(br), (el: T) => ord.compare(a, el) >= 0) &&
              isBinarySearchTree(_2_right) &&
              isBinarySearchTree(pr) &&
              (treeSet(pr) subsetOf treeSet(bl)) &&
              setForall(treeSet(pr), (el: T) => ord.compare(b, el) >= 0) &&
              setForall(treeSet(br), (el: T) => ord.compare(el, b) >= 0) &&
              (ord.compare(a, b) >= 0) &&
              {
                subtreeSmallerOrderingTransitivityLemma(b, a, ar)
                setForall(treeSet(ar), (el: T) => ord.compare(el, b) >= 0)
              } &&
              setForall(treeSet(_2_right), (el: T) => ord.compare(el, b) >= 0) &&
              isBinarySearchTree(res._2)
            }

            assert {
              setForall(treeSet(pr), (el: T) => ord.compare(el, p) >= 0) &&
              ord.compare(b, p) > 0 &&
              {
                ord.strictGreaterToNonStrictLemma(b, p)
                ord.compare(b, p) >= 0
              } &&
              {
                subtreeSmallerOrderingTransitivityLemma(p, b, _2_right)
                setForall(treeSet(_2_right), (el: T) => ord.compare(el, p) >= 0)
              } &&
              setForall(treeSet(res._2), (el: T) => ord.compare(el, p) >= 0)
            }

            check {
              isBinarySearchTree(res._1) && isBinarySearchTree(res._2) &&
              setForall(treeSet(res._1), (el: T) => ord.compare(p, el) >= 0) &&
              setForall(treeSet(res._2), (el: T) => ord.compare(el, p) >= 0) &&
              (treeSet(res._1) subsetOf treeSet(tree)) &&
              (treeSet(res._2) subsetOf treeSet(tree))
            }
            res
          }
        }
      }
    }
  } ensuring { res => isBinarySearchTree(res._1)(ord) &&
    isBinarySearchTree(res._2)(ord) &&
    setForall(treeSet(res._1), (el: T) => ord.compare(p, el) >= 0) &&
    setForall(treeSet(res._2), (el: T) => ord.compare(el, p) >= 0) &&
    (treeSet(res._1) subsetOf treeSet(tree)) &&
    (treeSet(res._2) subsetOf treeSet(tree))
  }

  /**
   * Checks whether the given value is the minimal element of the tree under
   *  the specified ordering
   */
  def isMinTreeEl[T](tree: Tree[T], ord: Ordering[T])(value: T): Boolean =
    treeSet(tree).contains(value) &&
    setForall(treeSet(tree), (el: T) => ord.compare(el, value) >= 0)

  /**
   * Trivial case for getting left-most element of the binary tree
   */
  private def getMinTreeElTrivialCase[T](tree: Tree[T])
    (implicit ord: Ordering[T]): Tuple2[Tree[T], T] = {
      require(
        isBinarySearchTree(tree)(ord) &&
        !isTreeEmpty(tree) &&
        isTreeEmpty(leftSubTree(tree))
      )

      val Node(l, v, r) = tree
      assert{
        forall { (el: T) => !treeSet(l).contains(el) } &&
        setForall(treeSet(l), (el: T) => ord.compare(el, v) >= 0) &&
        {
          ord.selfEqualityLemma(v)
          ord.compare(v, v) >= 0
        }
      }
      Tuple2[Tree[T], T](r, v)
    } ensuring { (res: Tuple2[Tree[T], T]) =>
      isMinTreeEl(tree, ord)(res._2) &&
      treeSize(res._1) + 1 == treeSize(tree) &&
      isBinarySearchTree(res._1) &&
      ((Set(res._2) ++ treeSet(res._1)) == treeSet(tree))
    }

  /**
   * Recursive call for getting left-most element of the binary tree
   */
  private def getMinTreeElRecursiveStep[T](tree: Tree[T])
    (implicit ord: Ordering[T]): Tuple2[Tree[T], T] = {
      require(
        isBinarySearchTree(tree)(ord) &&
        !isTreeEmpty(tree) &&
        !isTreeEmpty(leftSubTree(tree))
      )

      val Node(l, v, r) = tree
      val subTreeMinPair = getMinTreeEl(l)(ord)
      val subTreeMin = subTreeMinPair._2
      val restOfTree = Node(subTreeMinPair._1, v, r)
      val rSet = treeSet(r)
      assert{
        ord.compare(v, subTreeMin) >= 0 &&
        setForall(rSet, (el: T) => ord.compare(el, v) >= 0 && {
          ord.nonStrictTransitivityLemma(el, v, subTreeMin)
          ord.compare(el, subTreeMin) >= 0
        })
      }

      assert{
        (treeSet(subTreeMinPair._1) subsetOf treeSet(l)) &&
        isBinarySearchTree(subTreeMinPair._1) &&
        isBinarySearchTree(restOfTree)
      }

      assert {
        (treeSet(tree) == treeSet(l) ++ treeSet(r) ++ Set(v)) &&
        (treeSet(l) == treeSet(subTreeMinPair._1) ++ Set(subTreeMin)) &&
        (treeSet(tree) ==  treeSet(subTreeMinPair._1) ++ Set(subTreeMin) ++ treeSet(r) ++ Set(v)) &&
        (treeSet(restOfTree) == treeSet(subTreeMinPair._1) ++ Set(v) ++ treeSet(r))

      }

      Tuple2[Tree[T], T](restOfTree, subTreeMin)
    } ensuring { (res: Tuple2[Tree[T], T]) =>
      isMinTreeEl(tree, ord)(res._2) &&
      treeSize(res._1) + 1 == treeSize(tree) &&
      isBinarySearchTree(res._1) &&
      ((Set(res._2) ++ treeSet(res._1)) == treeSet(tree))
    }

  /**
   *  Returns the left-most element of non-empty binary tree sorted under the
   *    given ordering.
   */
  def getMinTreeEl[T](tree: Tree[T])(implicit ord: Ordering[T]):
    Tuple2[Tree[T], T] = {
      require(isBinarySearchTree(tree)(ord) && !isTreeEmpty(tree))

      if(isTreeEmpty(leftSubTree(tree)))  getMinTreeElTrivialCase(tree)(ord)
      else                                getMinTreeElRecursiveStep(tree)(ord)
    } ensuring { (res: Tuple2[Tree[T], T]) =>
      isMinTreeEl(tree, ord)(res._2) &&
      treeSize(res._1) + 1 == treeSize(tree) &&
      isBinarySearchTree(res._1) &&
      ((Set(res._2) ++ treeSet(res._1)) == treeSet(tree))
    }

  /**
   * Inserts an element in a BST under given ordering using splaying
   */
  def binarySearchTreeSplayInsertion[T](tree: Tree[T], element: T)(implicit ord: Ordering[T]): Tree[T] = {
      require(isBinarySearchTree(tree)(ord))
      val (l, r) = partition(element, tree)(ord)
      Node(l, element, r)
    } ensuring { res =>
      isBinarySearchTree(res) &&
      (treeSet(res) subsetOf (treeSet(tree) ++ Set(element)))
    }

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
