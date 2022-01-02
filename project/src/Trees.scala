import stainless.lang._
import stainless.annotation._
import stainless.proof._
import StainlessUtils._

object Trees {
  sealed abstract class Tree[T]
  case class Leaf[T]() extends Tree[T]
  case class Node[T](left: Tree[T], value: T, right: Tree[T]) extends Tree[T]

  def isTreeEmpty[T](tree: Tree[T]): Boolean = tree match {
    case Leaf() => true
    case _ => false
  }

  def rightSubTree[T](tree: Tree[T]): Tree[T] = {
    require(!isTreeEmpty(tree))
    val Node(_, _, r) = tree
    r
  }

  def leftSubTree[T](tree: Tree[T]): Tree[T] = {
    require(!isTreeEmpty(tree))
    val Node(l, _, _) = tree
    l
  }

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

  type treePartitionType[T] = Tuple2[Tree[T], Tree[T]]

  def isValidPartition[T](p: T, tree: Tree[T],
    treePartition: treePartitionType[T])(implicit ord: Ordering[T]): Boolean =
      isBinarySearchTree(treePartition._1) && isBinarySearchTree(treePartition._2) &&
      setForall(treeSet(treePartition._1), (el: T) => ord.compare(p, el) >= 0) &&
      setForall(treeSet(treePartition._2), (el: T) => ord.compare(el, p) >= 0) &&
      (treeSet(treePartition._1) subsetOf treeSet(tree)) &&
      (treeSet(treePartition._2) subsetOf treeSet(tree))

  private def partitionEcho[T](p: T, tree: Tree[T], res: treePartitionType[T])
    (implicit ord: Ordering[T]): treePartitionType[T] = {
      require{
        isValidPartition(p, tree, res)(ord)
      }
      res
    } ensuring (r => {
      isValidPartition(p, tree, r)(ord)
    })

  // Reports failure due to not knowing whether the function terminates.
  //  Weirdly, sometimes it can infer by itself in my runs...
  //  Also fulling full tuple2 constructor recommended as Stainless complains
  //    otherwise.
  //  Proof of postcondition is painfully slow, just postcondition took
  //    around 220 seconds...
  def partition[T](p: T, tree: Tree[T])(implicit ord: Ordering[T]):
        treePartitionType[T] = {
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
            partitionEcho(p, tree, res)(ord)
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
            partitionEcho(p, tree, res)(ord)
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
            partitionEcho(p, tree, res)(ord)
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
            partitionEcho(p, tree, res)
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
            partitionEcho(p, tree, res)(ord)
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
            partitionEcho(p, tree, res)(ord)
          }
        }
      }
    }
  } ensuring {
    isValidPartition(p, tree, _)(ord)
  }


  /**
   * Trivial case for getting left-most element of the binary tree
   */
  private def getMinTreeElTrivialCase[T](tree: Tree[T])
    (implicit ord: Ordering[T]): T = {
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
      v
    } ensuring { res =>
      treeSet(tree).contains(res) &&
      setForall(treeSet(tree), (el: T) => ord.compare(el, res) >= 0)
    }

  /**
   * Recursive call for getting left-most element of the binary tree
   */
  private def getMinTreeElRecursiveStep[T](tree: Tree[T])
    (implicit ord: Ordering[T]): T = {
      require(
        isBinarySearchTree(tree)(ord) &&
        !isTreeEmpty(tree) &&
        !isTreeEmpty(leftSubTree(tree))
      )

      val Node(l, v, r) = tree
      val subTreeMin = getMinTreeEl(l)
      val rSet = treeSet(r)
      assert{
        ord.compare(v, subTreeMin) >= 0 &&
        setForall(rSet, (el: T) => ord.compare(el, v) >= 0 && {
          ord.nonStrictTransitivityLemma(el, v, subTreeMin)
          ord.compare(el, subTreeMin) >= 0
        })
      }
      subTreeMin
    } ensuring { res =>
      treeSet(tree).contains(res) &&
      setForall(treeSet(tree), (el: T) => ord.compare(el, res) >= 0)
    }

  /**
   *  Returns the left-most element of non-empty binary tree sorted under the
   *    given ordering.
   */
  def getMinTreeEl[T](tree: Tree[T])(implicit ord: Ordering[T]): T = {
    require(isBinarySearchTree(tree)(ord) && !isTreeEmpty(tree))

    if(isTreeEmpty(leftSubTree(tree)))  getMinTreeElTrivialCase(tree)
    else                                getMinTreeElRecursiveStep(tree)
  } ensuring { res =>
    treeSet(tree).contains(res) &&
    setForall(treeSet(tree), (el: T) => ord.compare(el, res) >= 0)
  }
}
