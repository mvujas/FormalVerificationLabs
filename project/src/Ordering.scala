import math._
import StainlessUtils._
import stainless.lang._ // ==> operator
import stainless.annotation._
import stainless.proof._


/**
 * Interface for providing ordering between elements of type T.
 * Source: https://infoscience.epfl.ch/record/268824
 */
trait Ordering[T] {
  /**
   *  Compares x and y and returns an integer n, which for the
   *    context of further documentation is assumed to have given value:
   *      - x > y => n > 0
   *      - x = y => n = 0
   *      - x < y => n < 0
   *
   *  All proofs still hold for arbitary definition of compare.
   */
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


  /**
   * Lemma proving if x = y and y = z then x = z
   */
  def equalityTransitivityLemma(x: T, y: T, z: T): Unit = {
    require(compare(x, y) == 0 && compare(y, z) == 0)
    assert(consistent(x, y, z))
  } ensuring (_ => compare(x, z) == 0)

  /**
   * Lemma proving if x > y then y < x
   */
  def strictlyMonotonicInverseLemmaGreater(x: T, y: T): Unit = {
    require(compare(x, y) > 0)
    assert(inverse(x, y))
  } ensuring (_ => compare(y, x) < 0)

  /**
   * Lemma proving if x < y then y > x
   */
  def strictlyMonotonicInverseLemmaSmaller(x: T, y: T): Unit = {
    require(compare(x, y) < 0)
    assert(inverse(x, y))
  } ensuring (_ => compare(y, x) > 0)

  /**
   * Lemma proving if x >= y then y <= x
   */
  def monotonicInverseLemmaGreater(x: T, y: T): Unit = {
    require(compare(x, y) >= 0)
    assert(inverse(x, y))
  } ensuring (_ => compare(y, x) <= 0)

  /**
   * Lemma proving if x <= y then x >= y
   */
  def monotonicInverseLemmaSmaller(x: T, y: T): Unit = {
    require(compare(x, y) <= 0)
    assert(inverse(x, y))
  } ensuring (_ => compare(y, x) >= 0)

  /**
   * Lemma proving if x >= y and y >= z then x >= z
   */
  def nonStrictTransitivityLemma(x: T, y: T, z: T): Unit = {
    require(compare(x, y) >= 0)
    require(compare(y, z) >= 0)

    if(compare(x, y) == 0 && compare(y, z) == 0) {
      equalityTransitivityLemma(x, y, z)
      check {compare(x, z) >= 0}
    }
    else if(compare(x, y) == 0 && compare(y, z) > 0) {
      check {
        consistent(x, y, z) &&
        compare(x, z) >= 0
      }
    }
    else if(compare(x, y) > 0 && compare(y, z) == 0) {
      check {
        inverse(x, y) &&
        consistent(y, z, x) &&
        inverse(z, x) &&
        compare(x, z) >= 0
      }
    }
    else {
      check {
        transitive(x, y, z) &&
        compare(x, z) >= 0
      }
    }
  } ensuring (_ => compare(x, z) >= 0)
}
