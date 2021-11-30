sealed abstract class Tree[T]
case class Leaf[T]() extends Tree[T]
case class Node[T](left: Tree[T], value: T, right: Tree[T]) extends Tree[T]
