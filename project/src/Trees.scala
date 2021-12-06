import stainless.lang._
import stainless.annotation._
import stainless.proof._
import StainlessUtils._

object Trees {
  sealed abstract class Tree[T]
  case class Leaf[T]() extends Tree[T]
  case class Node[T](left: Tree[T], value: T, right: Tree[T]) extends Tree[T]

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
}
