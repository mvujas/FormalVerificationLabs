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

  def treeGreaterEqThanValue[T](tree: Tree[T], value: T)
    (implicit ord: Ordering[T]): Boolean =
      setForall(treeSet(tree), (el: T) => ord.compare(el, value) >= 0)

  def treeSmallerEqThanValue[T](tree: Tree[T], value: T)
    (implicit ord: Ordering[T]): Boolean =
      setForall(treeSet(tree), (el: T) => ord.compare(value, el) >= 0)

  /**
   *  Check whether the given tree is a binary search tree
   */
  def isBinarySearchTree[T](tree: Tree[T])(implicit ord: Ordering[T]):
      Boolean = tree match {
        case Leaf() => true
        case Node(l, v, r) => isBinarySearchTree(l) && isBinarySearchTree(r) &&
          treeSmallerEqThanValue(l, v) &&
          treeGreaterEqThanValue(r, v)
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
    require{
      ord.compare(greaterValue, nodeValue) >= 0 &&
      treeSmallerEqThanValue(leftTree, nodeValue)
    }
    assert {
      ord.compare(greaterValue, nodeValue) >= 0 &&
      setForall(treeSet(leftTree), (el: T) => {
        ord.compare(nodeValue, el) >= 0 && {
          ord.nonStrictTransitivityLemma(greaterValue, nodeValue, el)
          ord.compare(greaterValue, el) >= 0
        }
      })
    }
  } ensuring (_ => treeSmallerEqThanValue(leftTree, greaterValue))

  /**
   *  Lemma proving if a >= b and forall(el in set(tree), el >= a) then
   *    forall(el in set(tree), el >= b)
   */
  def subtreeSmallerOrderingTransitivityLemma[T](
    smallerValue: T,
    nodeValue: T,
    rightTree: Tree[T]
  )(implicit ord: Ordering[T]): Unit = {
    require{
      ord.compare(nodeValue, smallerValue) >= 0 &&
      treeGreaterEqThanValue(rightTree, nodeValue)
    }
    assert {
      ord.compare(nodeValue, smallerValue) >= 0 &&
      setForall(treeSet(rightTree), (el: T) => {
        ord.compare(el, nodeValue) >= 0 && {
          ord.nonStrictTransitivityLemma(el, nodeValue, smallerValue)
          ord.compare(el, smallerValue) >= 0
        }
      })
    }
  } ensuring (_ => treeGreaterEqThanValue(rightTree, smallerValue))

  // def smallerThanLeftSmallerThanTreeLemma[T](tree: Tree[T], value: T)
  //   (implicit ord: Ordering[T]): Unit = {
  //   require(isBinarySearchTree(tree) && !isTreeEmpty(tree) &&
  //     treeSmallerEqThanValue(rightSubTree(tree), value))
  // } ensuring (_ => treeGreaterEqThanValue)

  // def greaterThanRightGreaterThanTreeLemma[T](tree: Tree[T], value: T)
  //   (implicit ord: Ordering[T]): Unit = {
  //   require(isBinarySearchTree(tree) && !isTreeEmpty(tree) &&
  //     treeSmallerEqThanValue(rightSubTree(tree), value))
  //   val Node(l, x, r) = tree
  //   assert(treeSmallerEqThanValue(r, value))
  //   assert(
  //     setForall(treeSet(r), (el: T) => {
  //       ord.compare(el, x) >= 0 && ord.compare(value, el) >= 0 && {
  //         ord.nonStrictTransitivityLemma(value, el, x)
  //         ord.compare(value, x) >= 0
  //       }
  //     })
  //   )
  // } ensuring (_ => treeSmallerEqThanValue(tree, value))

  type TreePartitionType[T] = Tuple2[Tree[T], Tree[T]]

  def isValidPartition[T](p: T, tree: Tree[T],  ord: Ordering[T])
    (treePartition: TreePartitionType[T]): Boolean = {
      isBinarySearchTree(treePartition._1)(ord) &&
      isBinarySearchTree(treePartition._2)(ord) &&
      treeSmallerEqThanValue(treePartition._1, p)(ord) &&
      treeGreaterEqThanValue(treePartition._2, p)(ord) &&
      ((treeSet(treePartition._1) ++ treeSet(treePartition._2)) == treeSet(tree))
    }


  private def partitionEcho[T](p: T, tree: Tree[T], parts: TreePartitionType[T])
    (implicit ord: Ordering[T]): TreePartitionType[T] = {
      require{ isValidPartition(p, tree, ord)(parts) }
      parts
    } ensuring { isValidPartition(p, tree, ord)(_) }


  private def partitionEmpty[T](p: T, tree: Tree[T])(implicit ord: Ordering[T]):
    TreePartitionType[T] = {
      require(isBinarySearchTree(tree) && isTreeEmpty(tree))
      Tuple2[Tree[T], Tree[T]](Leaf(), Leaf())
    } ensuring { isValidPartition(p, tree, ord)(_) }

  private def partitionSmallerEmpty[T](p: T, tree: Tree[T])
    (implicit ord: Ordering[T]): TreePartitionType[T] = {
      require(isBinarySearchTree(tree) &&
        !isTreeEmpty(tree) &&
        ord.compare(treeRootValue(tree), p) <= 0 &&
        isTreeEmpty(rightSubTree(tree))
      )
      val Node(al, a, ar) = tree
      assert {
        ord.inverse(a, p) &&
        ord.compare(p, a) >= 0 &&
        {
          subtreeGreaterOrderingTransitivityLemma(p, a, al)
          setForall(treeSet(al), (el: T) => ord.compare(p, el) >= 0)
        }
      }
      Tuple2[Tree[T], Tree[T]](tree, Leaf())
    } ensuring { isValidPartition(p, tree, ord)(_) }

  private def partitionSmallerSmaller[T](p: T, tree: Tree[T], subParts: TreePartitionType[T])
    (implicit ord: Ordering[T]): TreePartitionType[T] = {
      require{
        isBinarySearchTree(tree) &&
        !isTreeEmpty(tree) &&
        ord.compare(treeRootValue(tree), p) <= 0 &&
        !isTreeEmpty(rightSubTree(tree)) &&
        ord.compare(treeRootValue(rightSubTree(tree)), p) <= 0 &&
        isValidPartition(p, rightSubTree(rightSubTree(tree)), ord)(subParts)
      }

      assert {
        ord.inverse(treeRootValue(tree), p) &&
        ord.compare(p, treeRootValue(tree)) >= 0 &&
        ord.inverse(treeRootValue(rightSubTree(tree)), p) &&
        ord.compare(p, treeRootValue(rightSubTree(tree))) >= 0
      }
      val Node(al, a, ar) = tree
      assert {
        ord.inverse(a, p) &&
        ord.compare(p, a) >= 0 &&
        {
          subtreeGreaterOrderingTransitivityLemma(p, a, al)
          treeSmallerEqThanValue(al, p)
        }
      }
      val Node(bl, b, br) = ar
      val (pl, y) = subParts

      val bGreaterThanAProof =
        (treeSet(ar) contains b) &&
        ord.compare(b, a) >= 0

      val _1_left = Node(al, a, bl)
      val res = Tuple2[Tree[T], Tree[T]](
        Node(_1_left, b, pl),
        y
      )

      val setUnionProof =
        (treeSet(res._1) == treeSet(_1_left) ++ treeSet(pl) ++ Set(b)) &&
        (treeSet(_1_left) == treeSet(al) ++ Set(a) ++ treeSet(bl)) &&
        (treeSet(res._1) == treeSet(al) ++ Set(a) ++ treeSet(bl) ++ treeSet(pl) ++ Set(b)) &&
        (treeSet(res._2) == treeSet(y)) &&
        ((treeSet(res._1) ++ treeSet(res._2)) == (treeSet(al) ++ Set(a) ++
          treeSet(bl) ++ treeSet(pl) ++ Set(b) ++ treeSet(y))) &&
        (treeSet(br) == treeSet(y) ++ treeSet(pl)) &&
        (treeSet(ar) == treeSet(bl) ++ treeSet(br) ++ Set(b)) &&
        (treeSet(ar) == treeSet(bl) ++ treeSet(y) ++ treeSet(pl) ++ Set(b)) &&
        ((treeSet(res._1) ++ treeSet(res._2)) == (treeSet(al) ++ Set(a) ++
          treeSet(ar))) &&
        ((treeSet(res._1) ++ treeSet(res._2)) == treeSet(tree))

      assert(setUnionProof)

      val secondGreater = treeGreaterEqThanValue(y, p)
      val secondBST = isBinarySearchTree(y)
      val secondProof = secondGreater && secondBST

      assert(secondProof)

      val _1_left_BSTProof =
        isBinarySearchTree(al) &&
        isBinarySearchTree(bl) &&
        treeGreaterEqThanValue(ar, a) &&
        (treeSet(bl) subsetOf treeSet(ar)) &&
        treeGreaterEqThanValue(bl, a) &&
        isBinarySearchTree(_1_left)

      assert(_1_left_BSTProof)

      val firstBST =
        treeSmallerEqThanValue(bl, b) &&
        bGreaterThanAProof &&
        {
          subtreeGreaterOrderingTransitivityLemma(b, a, al)
          treeSmallerEqThanValue(al, b)
        } &&
        treeSmallerEqThanValue(_1_left, b) &&
        (treeSet(pl) subsetOf treeSet(br)) &&
        treeGreaterEqThanValue(br, b) &&
        treeGreaterEqThanValue(pl, b) &&
        isBinarySearchTree(pl) &&
        isBinarySearchTree(res._1)

      assert(firstBST)

      val firstSmaller =
        ord.compare(p, b) >= 0 &&
        treeSmallerEqThanValue(pl, p) &&
        treeSmallerEqThanValue(_1_left, b) &&
        {
          subtreeGreaterOrderingTransitivityLemma(p, b, _1_left)
          treeSmallerEqThanValue(_1_left, p)
        } &&
        treeSmallerEqThanValue(res._1, p)

      assert(firstSmaller)

      res
    } ensuring { isValidPartition(p, tree, ord)(_) }

  private def partitionSmallerGreater[T](p: T, tree: Tree[T], subParts: TreePartitionType[T])
    (implicit ord: Ordering[T]): TreePartitionType[T] = {
      require{
        isBinarySearchTree(tree) &&
        !isTreeEmpty(tree) &&
        ord.compare(treeRootValue(tree), p) <= 0 &&
        !isTreeEmpty(rightSubTree(tree)) &&
        ord.compare(treeRootValue(rightSubTree(tree)), p) > 0 &&
        isValidPartition(p, leftSubTree(rightSubTree(tree)), ord)(subParts)
      }

      assert{
        ord.compare(treeRootValue(rightSubTree(tree)), p) >= 0 &&
        ord.inverse(treeRootValue(tree), p) &&
        ord.compare(p, treeRootValue(tree)) >= 0
      }

      val Node(al, a, ar) = tree
      assert {
        ord.inverse(a, p) &&
        ord.compare(p, a) >= 0 &&
        {
          subtreeGreaterOrderingTransitivityLemma(p, a, al)
          treeSmallerEqThanValue(al, p)
        }
      }
      val Node(bl, b, br) = ar
      val (pl, pr) = subParts

      val res = Tuple2[Tree[T], Tree[T]](
        Node(al, a, pl),
        Node(pr, b, br)
      )

      val setUnionProof =
        (treeSet(res._1) == treeSet(al) ++ treeSet(pl) ++ Set(a)) &&
        (treeSet(res._2) == treeSet(pr) ++ treeSet(br) ++ Set(b)) &&
        (treeSet(res._1) ++ treeSet(res._2) == treeSet(al) ++ treeSet(pl) ++
          Set(a) ++ treeSet(pr) ++ treeSet(br) ++ Set(b)) &&
        (treeSet(bl) == treeSet(pl) ++ treeSet(pr)) &&
        (treeSet(res._1) ++ treeSet(res._2) == treeSet(al) ++ Set(a) ++
          treeSet(bl) ++ treeSet(br) ++ Set(b)) &&
        (treeSet(ar) == treeSet(bl) ++ treeSet(br) ++ Set(b)) &&
        (treeSet(res._1) ++ treeSet(res._2) == treeSet(al) ++ Set(a) ++
          treeSet(ar)) &&
        (treeSet(tree) == treeSet(al) ++ Set(a) ++ treeSet(ar)) &&
        (treeSet(res._1) ++ treeSet(res._2) == treeSet(tree))

      assert(setUnionProof)

      val firstBST =
        isBinarySearchTree(al) &&
        isBinarySearchTree(pl) &&
        treeSmallerEqThanValue(al, a) &&
        (treeSet(pl) subsetOf treeSet(bl)) &&
        (treeSet(bl) subsetOf treeSet(ar)) &&
        (treeSet(pl) subsetOf treeSet(ar)) &&
        treeGreaterEqThanValue(ar, a) &&
        treeGreaterEqThanValue(pl, a) &&
        isBinarySearchTree(res._1)

      assert(firstBST)

      val firstSmaller =
        ord.compare(p, a) >= 0 &&
        {
          subtreeGreaterOrderingTransitivityLemma(p, a, al)
          treeSmallerEqThanValue(al, p)
        } &&
        treeSmallerEqThanValue(pl, p) &&
        treeSmallerEqThanValue(res._1, p)

      assert(firstSmaller)

      val secondBST =
        isBinarySearchTree(pr) &&
        isBinarySearchTree(br) &&
        treeGreaterEqThanValue(br, b) &&
        (treeSet(pr) subsetOf treeSet(bl)) &&
        treeSmallerEqThanValue(bl, b) &&
        treeSmallerEqThanValue(pr, b) &&
        isBinarySearchTree(res._2)

      assert(secondBST)

      val secondGreater =
        ord.compare(b, p) >= 0 &&
        {
          subtreeSmallerOrderingTransitivityLemma(p, b, br)
          treeGreaterEqThanValue(br, p)
        } &&
        treeGreaterEqThanValue(pr, p) &&
        treeGreaterEqThanValue(res._2, p)

      assert(secondGreater)

      res
    } ensuring { isValidPartition(p, tree, ord)(_) }

  private def partitionGreaterEmpty[T](p: T, tree: Tree[T])
    (implicit ord: Ordering[T]): TreePartitionType[T] = {
      require(isBinarySearchTree(tree) &&
        !isTreeEmpty(tree) &&
        ord.compare(treeRootValue(tree), p) > 0 &&
        isTreeEmpty(leftSubTree(tree))
      )
      val Node(al, a, ar) = tree
      assert {
        ord.compare(a, p) >= 0 &&
        {
          subtreeSmallerOrderingTransitivityLemma(p, a, ar)
          treeGreaterEqThanValue(ar, p)
        }
      }
      Tuple2[Tree[T], Tree[T]](Leaf(), tree)
    } ensuring { isValidPartition(p, tree, ord)(_) }

  private def partitionGreaterSmaller[T](p: T, tree: Tree[T], subParts: TreePartitionType[T])
    (implicit ord: Ordering[T]): TreePartitionType[T] = {
      require{
        isBinarySearchTree(tree) &&
        !isTreeEmpty(tree) &&
        ord.compare(treeRootValue(tree), p) > 0 &&
        !isTreeEmpty(leftSubTree(tree)) &&
        ord.compare(treeRootValue(leftSubTree(tree)), p) <= 0 &&
        isValidPartition(p, rightSubTree(leftSubTree(tree)), ord)(subParts)
      }

      assert{
        ord.inverse(treeRootValue(leftSubTree(tree)), p) &&
        ord.compare(p, treeRootValue(leftSubTree(tree))) >= 0
      }

      val Node(al, a, ar) = tree
      val Node(bl, b, br) = al

      assert {
        ord.compare(a, p) >= 0 &&
        {
          subtreeSmallerOrderingTransitivityLemma(p, a, ar)
          treeGreaterEqThanValue(ar, p)
        }
      }

      val (pl, pr) = subParts
      val res = Tuple2[Tree[T], Tree[T]](
        Node(bl, b, pl),
        Node(pr, a, ar)
      )

      val setUnionProof =
        (treeSet(res._1) == treeSet(bl) ++ treeSet(pl) ++ Set(b)) &&
        (treeSet(res._2) == treeSet(pr) ++ treeSet(ar) ++ Set(a)) &&
        (treeSet(res._1) ++ treeSet(res._2) == treeSet(bl) ++ treeSet(pl) ++
          Set(b) ++ treeSet(pr) ++ treeSet(ar) ++ Set(a)) &&
        (treeSet(br) == treeSet(pl) ++ treeSet(pr)) &&
        (treeSet(res._1) ++ treeSet(res._2) == treeSet(bl) ++ treeSet(br) ++
          Set(b) ++ treeSet(ar) ++ Set(a)) &&
        (treeSet(al) == treeSet(bl) ++ treeSet(br) ++ Set(b)) &&
        (treeSet(res._1) ++ treeSet(res._2) == treeSet(al) ++ Set(a) ++
          treeSet(ar)) &&
        (treeSet(tree) == treeSet(al) ++ Set(a) ++ treeSet(ar)) &&
        (treeSet(res._1) ++ treeSet(res._2) == treeSet(tree))

      assert(setUnionProof)

      val firstBST =
        isBinarySearchTree(bl) &&
        isBinarySearchTree(pl) &&
        treeSmallerEqThanValue(bl, b) &&
        (treeSet(pl) subsetOf treeSet(br)) &&
        treeGreaterEqThanValue(br, b) &&
        treeGreaterEqThanValue(pl, b) &&
        isBinarySearchTree(res._1)

      assert(firstBST)

      val firstSmaller =
        ord.compare(p, b) >= 0 &&
        {
          subtreeGreaterOrderingTransitivityLemma(p, b, bl)
          treeSmallerEqThanValue(bl, p)
        } &&
        treeSmallerEqThanValue(pl, p) &&
        treeSmallerEqThanValue(res._1, p)

      assert(firstSmaller)

      val secondBST =
        isBinarySearchTree(pr) &&
        isBinarySearchTree(ar) &&
        treeGreaterEqThanValue(ar, a) &&
        (treeSet(pr) subsetOf treeSet(br)) &&
        (treeSet(br) subsetOf treeSet(al)) &&
        (treeSet(pr) subsetOf treeSet(al)) &&
        treeSmallerEqThanValue(al, a) &&
        treeSmallerEqThanValue(pr, a) &&
        isBinarySearchTree(res._2)

      assert(secondBST)

      val secondGreater =
        ord.compare(a, p) >= 0 &&
        {
          subtreeSmallerOrderingTransitivityLemma(p, a, ar)
          treeGreaterEqThanValue(ar, p)
        } &&
        treeGreaterEqThanValue(pr, p) &&
        treeGreaterEqThanValue(res._2, p)

      assert(secondGreater)

      res
    } ensuring { isValidPartition(p, tree, ord)(_) }

  private def partitionGreaterGreater[T](p: T, tree: Tree[T], subParts: TreePartitionType[T])
    (implicit ord: Ordering[T]): TreePartitionType[T] = {
      require{
        isBinarySearchTree(tree) &&
        !isTreeEmpty(tree) &&
        ord.compare(treeRootValue(tree), p) > 0 &&
        !isTreeEmpty(leftSubTree(tree)) &&
        ord.compare(treeRootValue(leftSubTree(tree)), p) > 0 &&
        isValidPartition(p, leftSubTree(leftSubTree(tree)), ord)(subParts)
      }

      assert{
        ord.compare(treeRootValue(leftSubTree(tree)), p) >= 0
      }

      val Node(al, a, ar) = tree
      val Node(bl, b, br) = al

      assert {
        ord.compare(a, p) >= 0 &&
        {
          subtreeSmallerOrderingTransitivityLemma(p, a, ar)
          treeGreaterEqThanValue(ar, p)
        }
      }

      val (pl, pr) = subParts
      val _2_right = Node(br, a, ar)
      val res = Tuple2[Tree[T], Tree[T]](
        pl,
        Node(pr, b, _2_right)
      )

      val setUnionProof =
        (treeSet(res._1) == treeSet(pl)) &&
        (treeSet(res._2) == treeSet(pr) ++ Set(b) ++ treeSet(_2_right)) &&
        (treeSet(_2_right) == treeSet(br) ++ treeSet(ar) ++ Set(a)) &&
        (treeSet(res._2) == treeSet(pr) ++ Set(b) ++ treeSet(br) ++
          treeSet(ar) ++ Set(a)) &&
        (treeSet(res._1) ++ treeSet(res._2) == treeSet(pl) ++ treeSet(pr) ++
          Set(b) ++ treeSet(br) ++ treeSet(ar) ++ Set(a)) &&
        (treeSet(bl) == treeSet(pl) ++ treeSet(pr)) &&
        (treeSet(res._1) ++ treeSet(res._2) == treeSet(bl) ++
          Set(b) ++ treeSet(br) ++ treeSet(ar) ++ Set(a)) &&
        (treeSet(al) == treeSet(bl) ++ Set(b) ++ treeSet(br)) &&
        (treeSet(res._1) ++ treeSet(res._2) == treeSet(al) ++ treeSet(ar) ++
          Set(a)) &&
        (treeSet(res._1) ++ treeSet(res._2) == treeSet(tree))

      assert(setUnionProof)

      val firstBST = isBinarySearchTree(pl)

      assert(firstBST)

      val firstSmaller = treeSmallerEqThanValue(pl, p)

      assert(firstSmaller)

      val _2_rightBSTProof =
        isBinarySearchTree(br) &&
        isBinarySearchTree(ar) &&
        treeGreaterEqThanValue(ar, a) &&
        (treeSet(br) subsetOf treeSet(al)) &&
        treeSmallerEqThanValue(al, a) &&
        treeSmallerEqThanValue(br, a) &&
        isBinarySearchTree(_2_right)

      assert(_2_rightBSTProof)

      val secondBST =
        isBinarySearchTree(pr) &&
        isBinarySearchTree(_2_right) &&
        (treeSet(pr) subsetOf treeSet(bl)) &&
        treeSmallerEqThanValue(bl, b) &&
        treeSmallerEqThanValue(pr, b) &&
        treeGreaterEqThanValue(br, b) &&
        (treeSet(al) contains b) &&
        treeSmallerEqThanValue(al, a) &&
        treeGreaterEqThanValue(ar, a)
        ord.compare(a, b) >= 0 &&
        {
          subtreeSmallerOrderingTransitivityLemma(b, a, ar)
          treeGreaterEqThanValue(ar, b)
        } &&
        treeGreaterEqThanValue(_2_right, b) &&
        isBinarySearchTree(res._2)

      assert(secondBST)

      val secondGreater =
        treeGreaterEqThanValue(pr, p) &&
        ord.compare(b, p) >= 0 &&
        {
          subtreeSmallerOrderingTransitivityLemma(p, b, _2_right)
          treeGreaterEqThanValue(_2_right, p)
        } &&
        treeGreaterEqThanValue(res._2, p)

      assert(secondGreater)

      res
    } ensuring { isValidPartition(p, tree, ord)(_) }

  private def assumedPartition[T](p: T, tree: Tree[T])
    (implicit ord: Ordering[T]): TreePartitionType[T] = {
      require(isBinarySearchTree(tree))
      val res = Tuple2[Tree[T], Tree[T]](Leaf(), Leaf())
      assume(isValidPartition(p, tree, ord)(res))
      res
    } ensuring { isValidPartition(p, tree, ord)(_) }

  def partition[T](p: T, tree: Tree[T])(implicit ord: Ordering[T]):
    TreePartitionType[T] = {
      // Measure
      decreases(tree)
      // Precondition
      require(isBinarySearchTree(tree))
      // Logic
      tree match {
        case Leaf() => partitionEmpty(p, tree)(ord)
        case Node(al, a, ar) if(ord.compare(a, p) <= 0) => ar match {
          case Leaf() => partitionSmallerEmpty(p, tree)(ord)
          case Node(bl, b, br) if(ord.compare(b, p) <= 0) => {
            val subParts = partition(p, br)(ord)
            partitionSmallerSmaller(p, tree, subParts)(ord)
          }
          case Node(bl, b, br) => {
            val subParts = partition(p, bl)(ord)
            partitionSmallerGreater(p, tree, subParts)(ord)
          }
        }
        case Node(al, a, ar) => al match {
          case Leaf() => partitionGreaterEmpty(p, tree)(ord)
          case Node(bl, b, br) if(ord.compare(b, p) <= 0) => {
            val subParts = partition(p, br)(ord)
            partitionGreaterSmaller(p, tree, subParts)(ord)
          }
          case Node(bl, b, br) => {
            val subParts = partition(p, bl)(ord)
            partitionGreaterGreater(p, tree, subParts)(ord)
          }
        }
      }
    } ensuring { isValidPartition(p, tree, ord)(_) }

  // Reports failure due to not knowing whether the function terminates.
  //  Weirdly, sometimes it can infer by itself in my runs...
  //  Also fulling full tuple2 constructor recommended as Stainless complains
  //    otherwise.
  //  Proof of postcondition is painfully slow, just postcondition took
  //    around 220 seconds...
  // def partition[T](p: T, tree: Tree[T])(implicit ord: Ordering[T]):
  //       TreePartitionType[T] = {
  //   // Metric
  //   decreases(tree)
  //   // Precondition
  //   require(isBinarySearchTree(tree))
  //   // Logic
  //   tree match {
  //     case Leaf() => Tuple2[Tree[T], Tree[T]](Leaf(), Leaf())
  //     case aTree @ Node(al, a, ar) if(ord.compare(a, p) <= 0) => {
  //       assert {
  //         ord.inverse(a, p) &&
  //         ord.compare(p, a) >= 0 &&
  //         {
  //           subtreeGreaterOrderingTransitivityLemma(p, a, al)
  //           setForall(treeSet(al), (el: T) => ord.compare(p, el) >= 0)
  //         }
  //       }
  //
  //       ar match {
  //         case Leaf() => {
  //           val res = Tuple2[Tree[T], Tree[T]](aTree, Leaf())
  //           check {
  //             isBinarySearchTree(res._1) && isBinarySearchTree(res._2) &&
  //             setForall(treeSet(res._1), (el: T) => ord.compare(p, el) >= 0) &&
  //             setForall(treeSet(res._2), (el: T) => ord.compare(el, p) >= 0) &&
  //             (treeSet(res._1) subsetOf treeSet(tree)) &&
  //             (treeSet(res._2) subsetOf treeSet(tree))
  //           }
  //           res
  //         }
  //         case Node(bl, b, br) if(ord.compare(b, p) <= 0) => {
  //           val (pl, y) = partition(p, br)
  //           val _1_left = Node(al, a, bl)
  //           val res = Tuple2[Tree[T], Tree[T]](
  //             Node(_1_left, b, pl),
  //             y
  //           )
  //
  //
  //           assert {
  //             (Set(b) subsetOf treeSet(ar)) &&
  //             ord.compare(b, a) >= 0 &&
  //             // Proof _1_left is a binary search tree
  //             (treeSet(bl) subsetOf treeSet(ar)) &&
  //             setForall(treeSet(bl), (el: T) => ord.compare(el, a) >= 0) &&
  //             setForall(treeSet(al), (el: T) => ord.compare(a, el) >= 0) &&
  //             isBinarySearchTree(al) &&
  //             isBinarySearchTree(ar) &&
  //             isBinarySearchTree(bl) &&
  //             isBinarySearchTree(_1_left) &&
  //             // Proof that treeSet(_1_left) is <= b
  //             setForall(treeSet(al), (el: T) => {
  //               ord.compare(a, el) >= 0 && {
  //                 ord.nonStrictTransitivityLemma(b, a, el)
  //                 ord.compare(b, el) >= 0
  //               }
  //             }) &&
  //             setForall(treeSet(_1_left), (el: T) => ord.compare(b, el) >= 0) &&
  //             // Proof that treeSet(pl) is <= b
  //             (treeSet(pl) subsetOf treeSet(br)) &&
  //             setForall(treeSet(pl), (el: T) => ord.compare(el, b) >= 0) &&
  //             // Proof pl is a binary search tree
  //             isBinarySearchTree(pl) &&
  //             // Proof _1 is a binary search tree
  //             isBinarySearchTree(res._1)
  //           }
  //
  //           assert {
  //             {
  //               // p >= b
  //               ord.monotonicInverseLemmaSmaller(b, p)
  //               ord.compare(p, b) >= 0
  //             } &&
  //             setForall(treeSet(_1_left), (el: T) => {
  //               ord.compare(b, el) >= 0 && {
  //                 ord.nonStrictTransitivityLemma(p, b, el)
  //                 ord.compare(p, el) >= 0
  //               }
  //             }) &&
  //             setForall(treeSet(pl), (el: T) => ord.compare(p, el) >= 0)
  //           }
  //
  //
  //           check {
  //             isBinarySearchTree(res._1) && isBinarySearchTree(res._2) &&
  //             setForall(treeSet(res._1), (el: T) => ord.compare(p, el) >= 0) &&
  //             setForall(treeSet(res._2), (el: T) => ord.compare(el, p) >= 0) &&
  //             (treeSet(res._1) subsetOf treeSet(tree)) &&
  //             (treeSet(res._2) subsetOf treeSet(tree))
  //           }
  //           res
  //         }
  //         case Node(bl, b, br) => {
  //           val (pl, pr) = partition(p, bl)
  //
  //           val res = Tuple2[Tree[T], Tree[T]](
  //             Node(al, a, pl),
  //             Node(pr, b, br)
  //           )
  //
  //           assert {
  //             (treeSet(pl) subsetOf treeSet(bl)) &&
  //             (treeSet(pr) subsetOf treeSet(bl)) &&
  //             (treeSet(bl) subsetOf treeSet(ar)) &&
  //             (treeSet(br) subsetOf treeSet(ar)) &&
  //             (treeSet(ar) subsetOf treeSet(tree)) &&
  //             (treeSet(res._1) subsetOf treeSet(tree)) &&
  //             (treeSet(res._2) subsetOf treeSet(tree))
  //           }
  //
  //           assert {
  //             setForall(treeSet(ar), (el: T) => ord.compare(el, a) >= 0) &&
  //             (treeSet(pr) subsetOf treeSet(bl)) &&
  //             setForall(treeSet(bl), (el: T) => ord.compare(b, el) >= 0) &&
  //             isBinarySearchTree(res._1) &&
  //             isBinarySearchTree(res._2)
  //           }
  //
  //           assert {
  //             {
  //               subtreeGreaterOrderingTransitivityLemma(p, a, al)
  //               setForall(treeSet(res._1), (el: T) => ord.compare(p, el) >= 0)
  //             } &&
  //             {
  //               subtreeSmallerOrderingTransitivityLemma(p, b, br)
  //               setForall(treeSet(res._2), (el: T) => ord.compare(el, p) >= 0)
  //             }
  //           }
  //
  //           check {
  //             isBinarySearchTree(res._1) && isBinarySearchTree(res._2) &&
  //             setForall(treeSet(res._1), (el: T) => ord.compare(p, el) >= 0) &&
  //             setForall(treeSet(res._2), (el: T) => ord.compare(el, p) >= 0) &&
  //             (treeSet(res._1) subsetOf treeSet(tree)) &&
  //             (treeSet(res._2) subsetOf treeSet(tree))
  //           }
  //           res
  //         }
  //       }
  //     }
  //     case aTree @ Node(al, a, ar) => {
  //       assert {
  //         ord.compare(a, p) > 0 &&
  //         {
  //           ord.strictGreaterToNonStrictLemma(a, p)
  //           ord.compare(a, p) >= 0
  //         } &&
  //         {
  //           subtreeSmallerOrderingTransitivityLemma(p, a, ar)
  //           setForall(treeSet(ar), (el: T) => ord.compare(el, p) >= 0)
  //         }
  //       }
  //
  //       al match {
  //         case Leaf() => {
  //           val res = Tuple2[Tree[T], Tree[T]](Leaf(), aTree)
  //           check {
  //             isBinarySearchTree(res._1) && isBinarySearchTree(res._2) &&
  //             setForall(treeSet(res._1), (el: T) => ord.compare(p, el) >= 0) &&
  //             setForall(treeSet(res._2), (el: T) => ord.compare(el, p) >= 0) &&
  //             (treeSet(res._1) subsetOf treeSet(tree)) &&
  //             (treeSet(res._2) subsetOf treeSet(tree))
  //           }
  //           res
  //         }
  //         case Node(bl, b, br) if (ord.compare(b, p) <= 0) => {
  //           val (pl, pr) = partition(p, br)
  //           val res = Tuple2[Tree[T], Tree[T]](
  //             Node(bl, b, pl),
  //             Node(pr, a, ar)
  //           )
  //
  //           assert {
  //             (treeSet(bl) subsetOf treeSet(al)) &&
  //             (treeSet(br) subsetOf treeSet(al)) &&
  //             (treeSet(pl) subsetOf treeSet(br)) &&
  //             (treeSet(pr) subsetOf treeSet(br)) &&
  //             (treeSet(res._1) subsetOf treeSet(tree)) &&
  //             (treeSet(res._2) subsetOf treeSet(tree))
  //           }
  //
  //           assert {
  //             // pl subset of br and all elements of br are greater than b
  //             isBinarySearchTree(res._1) &&
  //             // pr subset of br which is a subset of al and
  //             //    all elements of al are smaller than a
  //             (treeSet(pr) subsetOf treeSet(al)) &&
  //             isBinarySearchTree(res._2)
  //           }
  //
  //           assert {
  //             // Proven before the match that all elements of ar >= p, then also
  //             //    a >= p, and finally elements of pr >= p by induction
  //             //    hypothesis
  //             setForall(treeSet(res._2), (el: T) => ord.compare(el, p) >= 0) &&
  //             // Proof that all elements of the first element of the tuple are
  //             //    <= p, we have to prove that only the elements of bl are <= p
  //             //    which follows from transitivity
  //             ord.compare(b, p) <= 0 &&
  //             ord.inverse(b, p) &&
  //             ord.compare(p, b) >= 0 &&
  //             {
  //               subtreeGreaterOrderingTransitivityLemma(p, b, bl)
  //               setForall(treeSet(bl), (el: T) => ord.compare(p, el) >= 0)
  //             } &&
  //             setForall(treeSet(res._1), (el: T) => ord.compare(p, el) >= 0)
  //           }
  //
  //           check {
  //             isBinarySearchTree(res._1) && isBinarySearchTree(res._2) &&
  //             setForall(treeSet(res._1), (el: T) => ord.compare(p, el) >= 0) &&
  //             setForall(treeSet(res._2), (el: T) => ord.compare(el, p) >= 0) &&
  //             (treeSet(res._1) subsetOf treeSet(tree)) &&
  //             (treeSet(res._2) subsetOf treeSet(tree))
  //           }
  //           res
  //         }
  //         case bTree @ Node(bl, b, br) => {
  //           val (pl, pr) = partition(p, bl)
  //           val _2_right = Node(br, a, ar)
  //           val res = Tuple2[Tree[T], Tree[T]](
  //             pl,
  //             Node(pr, b, _2_right)
  //           )
  //
  //           assert {
  //             isBinarySearchTree(bTree) &&
  //             setForall(treeSet(bl), (el: T) => ord.compare(b, el) >= 0) &&
  //             setForall(treeSet(br), (el: T) => ord.compare(el, b) >= 0)
  //           }
  //
  //           assert {
  //             (treeSet(pl) subsetOf treeSet(bl)) &&
  //             (treeSet(pr) subsetOf treeSet(bl)) &&
  //             (treeSet(bl) subsetOf treeSet(al)) &&
  //             (treeSet(br) subsetOf treeSet(al))  &&
  //             (treeSet(res._1) subsetOf treeSet(tree)) &&
  //             (treeSet(_2_right) subsetOf treeSet(tree)) &&
  //             (treeSet(res._2) subsetOf treeSet(tree))
  //           }
  //
  //           assert {
  //             isBinarySearchTree(res._1) &&
  //             setForall(treeSet(res._1), (el: T) => ord.compare(p, el) >= 0)
  //           }
  //
  //           assert {
  //             isBinarySearchTree(br) &&
  //             isBinarySearchTree(ar) &&
  //             (treeSet(br) subsetOf treeSet(al)) &&
  //             setForall(treeSet(br), (el: T) => ord.compare(a, el) >= 0) &&
  //             isBinarySearchTree(_2_right) &&
  //             isBinarySearchTree(pr) &&
  //             (treeSet(pr) subsetOf treeSet(bl)) &&
  //             setForall(treeSet(pr), (el: T) => ord.compare(b, el) >= 0) &&
  //             setForall(treeSet(br), (el: T) => ord.compare(el, b) >= 0) &&
  //             (ord.compare(a, b) >= 0) &&
  //             {
  //               subtreeSmallerOrderingTransitivityLemma(b, a, ar)
  //               setForall(treeSet(ar), (el: T) => ord.compare(el, b) >= 0)
  //             } &&
  //             setForall(treeSet(_2_right), (el: T) => ord.compare(el, b) >= 0) &&
  //             isBinarySearchTree(res._2)
  //           }
  //
  //           assert {
  //             setForall(treeSet(pr), (el: T) => ord.compare(el, p) >= 0) &&
  //             ord.compare(b, p) > 0 &&
  //             {
  //               ord.strictGreaterToNonStrictLemma(b, p)
  //               ord.compare(b, p) >= 0
  //             } &&
  //             {
  //               subtreeSmallerOrderingTransitivityLemma(p, b, _2_right)
  //               setForall(treeSet(_2_right), (el: T) => ord.compare(el, p) >= 0)
  //             } &&
  //             setForall(treeSet(res._2), (el: T) => ord.compare(el, p) >= 0)
  //           }
  //
  //           check {
  //             isBinarySearchTree(res._1) && isBinarySearchTree(res._2) &&
  //             setForall(treeSet(res._1), (el: T) => ord.compare(p, el) >= 0) &&
  //             setForall(treeSet(res._2), (el: T) => ord.compare(el, p) >= 0) &&
  //             (treeSet(res._1) subsetOf treeSet(tree)) &&
  //             (treeSet(res._2) subsetOf treeSet(tree))
  //           }
  //           res
  //         }
  //       }
  //     }
  //   }
  // } ensuring { res => isBinarySearchTree(res._1)(ord) &&
  //   isBinarySearchTree(res._2)(ord) &&
  //   setForall(treeSet(res._1), (el: T) => ord.compare(p, el) >= 0) &&
  //   setForall(treeSet(res._2), (el: T) => ord.compare(el, p) >= 0) &&
  //   (treeSet(res._1) subsetOf treeSet(tree)) &&
  //   (treeSet(res._2) subsetOf treeSet(tree))
  // }
  // def partition[T](p: T, tree: Tree[T])(implicit ord: Ordering[T]):
  //       TreePartitionType[T] = {
  //   // Metric
  //   decreases(tree)
  //   // Precondition
  //   require(isBinarySearchTree(tree))
  //   // Logic
  //   tree match {
  //     case Leaf() => Tuple2[Tree[T], Tree[T]](Leaf(), Leaf())
  //     case aTree @ Node(al, a, ar) if(ord.compare(a, p) <= 0) => {
  //       assert {
  //         ord.inverse(a, p) &&
  //         ord.compare(p, a) >= 0 &&
  //         {
  //           subtreeGreaterOrderingTransitivityLemma(p, a, al)
  //           setForall(treeSet(al), (el: T) => ord.compare(p, el) >= 0)
  //         }
  //       }
  //
  //       ar match {
  //         case Leaf() => {
  //           val res = Tuple2[Tree[T], Tree[T]](aTree, Leaf())
  //           check {
  //             isBinarySearchTree(res._1) && isBinarySearchTree(res._2) &&
  //             setForall(treeSet(res._1), (el: T) => ord.compare(p, el) >= 0) &&
  //             setForall(treeSet(res._2), (el: T) => ord.compare(el, p) >= 0) &&
  //             (treeSet(res._1) subsetOf treeSet(tree)) &&
  //             (treeSet(res._2) subsetOf treeSet(tree))
  //           }
  //           res
  //         }
  //         case Node(bl, b, br) if(ord.compare(b, p) <= 0) => {
  //           val (pl, y) = partition(p, br)
  //           val _1_left = Node(al, a, bl)
  //           val res = Tuple2[Tree[T], Tree[T]](
  //             Node(_1_left, b, pl),
  //             y
  //           )
  //
  //           assume {
  //             isBinarySearchTree(res._1) && isBinarySearchTree(res._2) &&
  //             setForall(treeSet(res._1), (el: T) => ord.compare(p, el) >= 0) &&
  //             setForall(treeSet(res._2), (el: T) => ord.compare(el, p) >= 0) &&
  //             (treeSet(res._1) subsetOf treeSet(tree)) &&
  //             (treeSet(res._2) subsetOf treeSet(tree))
  //           }
  //           res
  //         }
  //         case Node(bl, b, br) => {
  //           val (pl, pr) = partition(p, bl)
  //
  //           assert{
  //             (treeSet(pl) subsetOf treeSet(bl)) &&
  //             (treeSet(pr) subsetOf treeSet(bl)) &&
  //             isBinarySearchTree(pl) &&
  //             isBinarySearchTree(pr)
  //           }
  //
  //           val res = Tuple2[Tree[T], Tree[T]](
  //             Node(al, a, pl),
  //             Node(pr, b, br)
  //           )
  //
  //           assert {
  //             (treeSet(pl) subsetOf treeSet(bl)) &&
  //             (treeSet(pr) subsetOf treeSet(bl)) &&
  //             (treeSet(bl) subsetOf treeSet(ar)) &&
  //             (treeSet(br) subsetOf treeSet(ar)) &&
  //             (treeSet(ar) subsetOf treeSet(tree)) &&
  //             (treeSet(res._1) subsetOf treeSet(tree)) &&
  //             (treeSet(res._2) subsetOf treeSet(tree))
  //           }
  //
  //           assert {
  //             {
  //               subsetSmallerEqTransitivityLemma(treeSet(pl), treeSet(ar), a)
  //               subsetGreaterEqTransitivityLemma(treeSet(pr), treeSet(bl), b)
  //               isBinarySearchTree(res._1) && isBinarySearchTree(res._2)
  //             }
  //           }
  //
  //           assert {
  //             {
  //               subtreeGreaterOrderingTransitivityLemma(p, a, al)
  //               setForall(treeSet(res._1), (el: T) => ord.compare(p, el) >= 0)
  //             } &&
  //             {
  //               subtreeSmallerOrderingTransitivityLemma(p, b, br)
  //               setForall(treeSet(res._2), (el: T) => ord.compare(el, p) >= 0)
  //             }
  //           }
  //
  //           check {
  //             isBinarySearchTree(res._1) && isBinarySearchTree(res._2) &&
  //             setForall(treeSet(res._1), (el: T) => ord.compare(p, el) >= 0) &&
  //             setForall(treeSet(res._2), (el: T) => ord.compare(el, p) >= 0) &&
  //             (treeSet(res._1) subsetOf treeSet(tree)) &&
  //             (treeSet(res._2) subsetOf treeSet(tree))
  //           }
  //           res
  //         }
  //       }
  //     }
  //     case aTree @ Node(al, a, ar) => {
  //       assert {
  //         ord.compare(a, p) > 0 &&
  //         {
  //           ord.strictGreaterToNonStrictLemma(a, p)
  //           ord.compare(a, p) >= 0
  //         } &&
  //         {
  //           subtreeSmallerOrderingTransitivityLemma(p, a, ar)
  //           setForall(treeSet(ar), (el: T) => ord.compare(el, p) >= 0)
  //         }
  //       }
  //
  //       al match {
  //         case Leaf() => {
  //           val res = Tuple2[Tree[T], Tree[T]](Leaf(), aTree)
  //           assume {
  //             isBinarySearchTree(res._1) && isBinarySearchTree(res._2) &&
  //             setForall(treeSet(res._1), (el: T) => ord.compare(p, el) >= 0) &&
  //             setForall(treeSet(res._2), (el: T) => ord.compare(el, p) >= 0) &&
  //             (treeSet(res._1) subsetOf treeSet(tree)) &&
  //             (treeSet(res._2) subsetOf treeSet(tree))
  //           }
  //           res
  //         }
  //         case Node(bl, b, br) if (ord.compare(b, p) <= 0) => {
  //           val (pl, pr) = partition(p, br)
  //           val res = Tuple2[Tree[T], Tree[T]](
  //             Node(bl, b, pl),
  //             Node(pr, a, ar)
  //           )
  //
  //           assume {
  //             isBinarySearchTree(res._1) && isBinarySearchTree(res._2) &&
  //             setForall(treeSet(res._1), (el: T) => ord.compare(p, el) >= 0) &&
  //             setForall(treeSet(res._2), (el: T) => ord.compare(el, p) >= 0) &&
  //             (treeSet(res._1) subsetOf treeSet(tree)) &&
  //             (treeSet(res._2) subsetOf treeSet(tree))
  //           }
  //           res
  //         }
  //         case bTree @ Node(bl, b, br) => {
  //           val (pl, pr) = partition(p, bl)
  //           val _2_right = Node(br, a, ar)
  //           val res = Tuple2[Tree[T], Tree[T]](
  //             pl,
  //             Node(pr, b, _2_right)
  //           )
  //
  //           assume {
  //             isBinarySearchTree(res._1) && isBinarySearchTree(res._2) &&
  //             setForall(treeSet(res._1), (el: T) => ord.compare(p, el) >= 0) &&
  //             setForall(treeSet(res._2), (el: T) => ord.compare(el, p) >= 0) &&
  //             (treeSet(res._1) subsetOf treeSet(tree)) &&
  //             (treeSet(res._2) subsetOf treeSet(tree))
  //           }
  //           res
  //         }
  //       }
  //     }
  //   }
  // } ensuring { res => isBinarySearchTree(res._1)(ord) &&
  //   isBinarySearchTree(res._2)(ord) &&
  //   setForall(treeSet(res._1), (el: T) => ord.compare(p, el) >= 0) &&
  //   setForall(treeSet(res._2), (el: T) => ord.compare(el, p) >= 0) &&
  //   (treeSet(res._1) subsetOf treeSet(tree)) &&
  //   (treeSet(res._2) subsetOf treeSet(tree))
  // }
  //
  // def subsetGreaterEqTransitivityLemma[T](a: Set[T], b: Set[T], x: T)(implicit ord: Ordering[T]): Unit = {
  //   require((a subsetOf b) && setForall(b, (el: T) => ord.compare(x, el) >= 0))
  // } ensuring { _ => setForall(a, (el: T) => ord.compare(x, el) >= 0) }
  //
  // def subsetSmallerEqTransitivityLemma[T](a: Set[T], b: Set[T], x: T)(implicit ord: Ordering[T]): Unit = {
  //   require((a subsetOf b) && setForall(b, (el: T) => ord.compare(el, x) >= 0))
  // } ensuring { _ => setForall(a, (el: T) => ord.compare(el, x) >= 0) }

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
}
