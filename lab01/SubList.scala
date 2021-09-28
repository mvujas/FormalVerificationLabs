import stainless.collection._
import stainless.lang._
import stainless.annotation._
 
object SubList {
 
  def subList[T](l1: List[T], l2: List[T]): Boolean = (l1, l2) match {
    case (Nil(), _)                 => true
    case (_, Nil())                 => false
    case (Cons(x, xs), Cons(y, ys)) => (x == y && subList(xs, ys)) || subList(l1, ys)
  }
 
  
  def subListRefl[T](l: List[T]): Unit = {
    if(!l.isEmpty) {
      subListRefl(l.tail)
    }
  }.ensuring(_ =>
    subList(l, l)
  )
 
  def subListTail[T](l1: List[T], l2: List[T]): Unit = {
    require(!l1.isEmpty && subList(l1, l2))
 
    // Checking to be sure Stainless can reason about this
    assert(!l2.isEmpty)


    // Makes sure l1 is at the beggining of what's left of l2
    if(subList(l1, l2.tail)) {
      subListTail(l1, l2.tail)
    }
    else {
      // Works without else, but provides deeper insight
      //  what Stainless is capable of
      assert(l1.head == l2.head)
    }
  }.ensuring(_ =>
    subList(l1.tail, l2)
  )
 
  def subListTails[T](l1: List[T], l2: List[T]): Unit = {
    require(!l1.isEmpty && !l2.isEmpty && l1.head == l2.head && subList(l1, l2))
 
    // Makes sure l1 is at the beggining of what's left of l2
    if(subList(l1, l2.tail)) {
      subListTail(l1, l2.tail)
    }
  }.ensuring(_ =>
    subList(l1.tail, l2.tail)
  )
 
  def subListTrans[T](l1: List[T], l2: List[T], l3: List[T]): Unit = {
    require(subList(l1, l2) && subList(l2, l3))

    if(l1.isEmpty) {
      // Check to make sure Stainless can prove for an empty list
      assert(subList(l1, l3))
    }
    else if(subList(l1, l2.tail)) {
      // Makes sure l1 is at the beggining of what's left of l2
      subListTail(l2, l3)
      subListTrans(l1, l2.tail, l3)
    }
    else if(subList(l2, l3.tail)) {
      // Makes sure what's left of l2 is at the beggining of what's left of l3
      subListTrans(l1, l2, l3.tail)
    }
    else {
      // Head of all three is the same so we can take it off
      assert(l1.head == l3.head)
      subListTrans(l1.tail, l2.tail, l3.tail)
    }
  }.ensuring(_ =>
    subList(l1, l3)
  )
 
  def subListLength[T](l1: List[T], l2: List[T]): Unit = {
    require(subList(l1, l2))

    if(l1.isEmpty) {
      assert(l1.length <= l2.length)
    }
    else if(subList(l1, l2.tail)) {
      // Makes sure l1 is at the beggining of what's left of l2
      subListLength(l1, l2.tail)
    }
    else {
      // Take head off both lists
      subListLength(l1.tail, l2.tail)
    }
  }.ensuring(_ =>
    l1.length <= l2.length
  )
 
  // def subListEqual[T](l1: List[T], l2: List[T]): Unit = {
  //   require(subList(l1, l2) && l1.length >= l2.length)

  // }.ensuring(_ =>
  //   l1 == l2
  // )
 
  // def subListAntisym[T](l1: List[T], l2: List[T]): Unit = {
  //   require(subList(l1, l2) && subList(l2, l1))
 
  // }.ensuring(_ =>
  //   l1 == l2
  // )
 
  @extern
  def main(args: Array[String]): Unit = {
    println(subList(List(0, 2), List(0, 1, 2))) // true
    println(subList(List(1, 0), List(0, 0, 1))) // false
    println(subList(List(10, 5, 25), List(70, 10, 11, 8, 5, 25, 22))) // true
  }
 
}
