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
   *  Returns whether every value in the given tree is greater or equal than the
   *    given value
   */
  def treeGreaterEqThanValue[T](tree: Tree[T], value: T)
    (implicit ord: Ordering[T]): Boolean =
      setForall(treeSet(tree), (el: T) => ord.compare(el, value) >= 0)

  /**
   *  Returns whether every value in the given tree is smaller or equal than the
   *    given value
   */
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

  type TreePartitionType[T] = Tuple2[Tree[T], Tree[T]]

  def isValidPartition[T](p: T, tree: Tree[T],  ord: Ordering[T])
    (treePartition: TreePartitionType[T]): Boolean = {
      isBinarySearchTree(treePartition._1)(ord) &&
      isBinarySearchTree(treePartition._2)(ord) &&
      treeSmallerEqThanValue(treePartition._1, p)(ord) &&
      treeGreaterEqThanValue(treePartition._2, p)(ord) &&
      ((treeSet(treePartition._1) ++ treeSet(treePartition._2)) == treeSet(tree)) &&
      (treeSize(treePartition._1) + treeSize(treePartition._2) == treeSize(tree))
    }



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

      val sizeProof =
        (treeSize(res._1) == treeSize(_1_left) + treeSize(pl) + 1) &&
        (treeSize(_1_left) == treeSize(al) + 1 + treeSize(bl)) &&
        (treeSize(res._1) == treeSize(al) + 1 + treeSize(bl) + treeSize(pl) + 1) &&
        (treeSize(res._2) == treeSize(y)) &&
        ((treeSize(res._1) + treeSize(res._2)) == (treeSize(al) + 1 +
          treeSize(bl) + treeSize(pl) + 1 + treeSize(y))) &&
        (treeSize(br) == treeSize(y) + treeSize(pl)) &&
        (treeSize(ar) == treeSize(bl) + treeSize(br) + 1) &&
        (treeSize(ar) == treeSize(bl) + treeSize(y) + treeSize(pl) + 1) &&
        ((treeSize(res._1) + treeSize(res._2)) == (treeSize(al) + 1 +
          treeSize(ar))) &&
        ((treeSize(res._1) + treeSize(res._2)) == treeSize(tree))

      assert(sizeProof)

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

      val sizeProof =
        (treeSize(res._1) == treeSize(al) + treeSize(pl) + 1) &&
        (treeSize(res._2) == treeSize(pr) + treeSize(br) + 1) &&
        (treeSize(res._1) + treeSize(res._2) == treeSize(al) + treeSize(pl) +
          1 + treeSize(pr) + treeSize(br) + 1) &&
        (treeSize(bl) == treeSize(pl) + treeSize(pr)) &&
        (treeSize(res._1) + treeSize(res._2) == treeSize(al) + 1 +
          treeSize(bl) + treeSize(br) + 1) &&
        (treeSize(ar) == treeSize(bl) + treeSize(br) + 1) &&
        (treeSize(res._1) + treeSize(res._2) == treeSize(al) + 1 +
          treeSize(ar)) &&
        (treeSize(tree) == treeSize(al) + 1 + treeSize(ar)) &&
        (treeSize(res._1) + treeSize(res._2) == treeSize(tree))

      assert(sizeProof)

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

      val sizeProof =
        (treeSize(res._1) == treeSize(bl) + treeSize(pl) + 1) &&
        (treeSize(res._2) == treeSize(pr) + treeSize(ar) + 1) &&
        (treeSize(res._1) + treeSize(res._2) == treeSize(bl) + treeSize(pl) +
          1 + treeSize(pr) + treeSize(ar) + 1) &&
        (treeSize(br) == treeSize(pl) + treeSize(pr)) &&
        (treeSize(res._1) + treeSize(res._2) == treeSize(bl) + treeSize(br) +
          1 + treeSize(ar) + 1) &&
        (treeSize(al) == treeSize(bl) + treeSize(br) + 1) &&
        (treeSize(res._1) + treeSize(res._2) == treeSize(al) + 1 +
          treeSize(ar)) &&
        (treeSize(tree) == treeSize(al) + 1 + treeSize(ar)) &&
        (treeSize(res._1) + treeSize(res._2) == treeSize(tree))

      assert(sizeProof)

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

      val sizeProof =
        (treeSize(res._1) == treeSize(pl)) &&
        (treeSize(res._2) == treeSize(pr) + 1 + treeSize(_2_right)) &&
        (treeSize(_2_right) == treeSize(br) + treeSize(ar) + 1) &&
        (treeSize(res._2) == treeSize(pr) + 1 + treeSize(br) +
          treeSize(ar) + 1) &&
        (treeSize(res._1) + treeSize(res._2) == treeSize(pl) + treeSize(pr) +
          1 + treeSize(br) + treeSize(ar) + 1) &&
        (treeSize(bl) == treeSize(pl) + treeSize(pr)) &&
        (treeSize(res._1) + treeSize(res._2) == treeSize(bl) +
          1 + treeSize(br) + treeSize(ar) + 1) &&
        (treeSize(al) == treeSize(bl) + 1 + treeSize(br)) &&
        (treeSize(res._1) + treeSize(res._2) == treeSize(al) + treeSize(ar) +
          1) &&
        (treeSize(res._1) + treeSize(res._2) == treeSize(tree))

      assert(sizeProof)

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

  /**
   * Partitions a BST into 2 BSTs where all elements of the first are smaller
   *  than the given value, and all values of the second are greater than the
   *  given value
   */
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

  /**
   * Checks whether the given value is the minimal element of the tree under
   *  the specified ordering
   */
  def isMinTreeEl[T](tree: Tree[T], ord: Ordering[T])(value: T): Boolean =
    isMinSetEl(treeSet(tree), ord)(value)

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

      val minElProof =
        (treeSet(l) contains subTreeMin) &&
        treeGreaterEqThanValue(l, subTreeMin) &&
        ord.compare(v, subTreeMin) >= 0 &&
        treeGreaterEqThanValue(r, v) &&
        {
            subtreeSmallerOrderingTransitivityLemma(subTreeMin, v, r)
            treeGreaterEqThanValue(r, subTreeMin)
        } &&
        treeGreaterEqThanValue(tree, subTreeMin) &&
        isMinTreeEl(tree, ord)(subTreeMin)

      assert(minElProof)

      val bstProof =
        (treeSet(subTreeMinPair._1) subsetOf treeSet(l)) &&
        treeSmallerEqThanValue(l, v) &&
        treeSmallerEqThanValue(subTreeMinPair._1, v) &&
        treeGreaterEqThanValue(r, v) &&
        isBinarySearchTree(subTreeMinPair._1) &&
        isBinarySearchTree(r) &&
        isBinarySearchTree(restOfTree)

      assert(bstProof)

      val setProof =
        (treeSet(tree) == treeSet(l) ++ treeSet(r) ++ Set(v)) &&
        (treeSet(l) == treeSet(subTreeMinPair._1) ++ Set(subTreeMin)) &&
        (treeSet(tree) ==  treeSet(subTreeMinPair._1) ++ Set(subTreeMin) ++ treeSet(r) ++ Set(v)) &&
        (treeSet(restOfTree) == treeSet(subTreeMinPair._1) ++ Set(v) ++ treeSet(r))

      assert(setProof)

      val sizeProof =
        (treeSize(tree) == treeSize(l) + treeSize(r) + 1) &&
        (treeSize(l) == treeSize(subTreeMinPair._1) + 1) &&
        (treeSize(tree) ==  treeSize(subTreeMinPair._1) + 1 + treeSize(r) + 1) &&
        (treeSize(restOfTree) == treeSize(subTreeMinPair._1) + 1 + treeSize(r))

      assert(sizeProof)

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
   * Inserts an element in a BST under given ordering using splay operation
   */
  def binarySearchTreeSplayInsertion[T](tree: Tree[T], element: T)(implicit ord: Ordering[T]): Tree[T] = {
      require(isBinarySearchTree(tree)(ord))
      val (l, r) = partition(element, tree)(ord)
      Node(l, element, r)
    } ensuring { res =>
      isBinarySearchTree(res) &&
      (treeSet(res) == (treeSet(tree) ++ Set(element))) &&
      (treeSize(res) == (treeSize(tree) + 1))
    }
}
