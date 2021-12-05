import math._
import StainlessUtils._
import stainless.lang._ // ==> operator
import stainless.annotation._


/**
 * Interface for providing ordering between elements of type T.
 * Source: https://infoscience.epfl.ch/record/268824
 */
trait Ordering[T] {
  def compare(x: T, y: T): Int

  @law
  def inverse(x: T, y: T): Boolean =
    signum(compare(x, y)) == -signum(compare(y, x))

  @law
  def transitive(x: T, y: T, z: T): Boolean =
    (compare(x, y) > 0 && compare(y, z) > 0) ==> (compare(x, z) > 0)

  @law
  def consistent(x: T, y: T, z: T): Boolean =
    (compare(x, y) == 0) ==> (signum(compare(x, z)) == signum(compare(y, z)))


  def equalityTransitivityLemma(x: T, y: T, z: T): Unit = {
    require(compare(x, y) == 0 && compare(y, z) == 0)
    assert(consistent(x, y, z))
  } ensuring (_ => compare(x, z) == 0)

  def strictlyMonotonicInverseLemma(x: T, y: T): Unit = {
    require(compare(x, y) > 0)
    assert(inverse(x, y))
  } ensuring (_ => compare(y, x) < 0)

  def monotonicInverseLemmaGreater(x: T, y: T): Unit = {
    require(compare(x, y) >= 0)
    assert(inverse(x, y))
  } ensuring (_ => compare(y, x) <= 0)

  def monotonicInverseLemmaSmaller(x: T, y: T): Unit = {
    require(compare(x, y) <= 0)
    assert(inverse(x, y))
  } ensuring (_ => compare(y, x) >= 0)


  def nonStrictTransitivityLemma(x: T, y: T, z: T): Unit = {
    require(compare(x, y) >= 0)
    require(compare(y, z) >= 0)

    /*
      Different cases of the ordering proved as function.
      Stainless complains when these expressions are in branches,
        it fails to figure out postcondition implies from them...
    */
    def subcase1(x: T, y: T, z: T): Unit = {
      require(compare(x, y) == 0 && compare(y, z) == 0)
      equalityTransitivityLemma(x, y, z)
    } ensuring (_ => compare(x, z) >= 0)
    def subcase2(x: T, y: T, z: T): Unit = {
      require(compare(x, y) == 0 && compare(y, z) > 0)
      assert(consistent(x, y, z))
    } ensuring (_ => compare(x, z) >= 0)
    def subcase3(x: T, y: T, z: T): Unit = {
      require(compare(x, y) > 0 && compare(y, z) == 0)
      assert(inverse(x, y))
      strictlyMonotonicInverseLemma(x, y)
      assert(consistent(y, z, x))
      assert(inverse(z, x))
    } ensuring (_ => compare(x, z) >= 0)
    def subcase4(x: T, y: T, z: T): Unit = {
      require(compare(x, y) > 0 && compare(y, z) > 0)
      assert(transitive(x, y, z))
    } ensuring (_ => compare(x, z) >= 0)

    if(compare(x, y) == 0 && compare(y, z) == 0) {
      subcase1(x, y, z)
    }
    else if(compare(x, y) == 0 && compare(y, z) > 0) {
      subcase2(x, y, z)
    }
    else if(compare(x, y) > 0 && compare(y, z) == 0) {
      subcase3(x, y, z)
    }
    else {
      subcase4(x, y, z)
    }
  } ensuring (_ => compare(x, z) >= 0)
}
