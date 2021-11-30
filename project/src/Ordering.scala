import math._
import stainless.annotation._


/**
 * Interface for providing ordering between elements of type T.
 * Source: https://infoscience.epfl.ch/record/268824
 */
trait Ordering[T] {
  def compare(x: T, y: T): Int

  @law def inverse(x: T, y: T): Boolean =
    signum(compare(x, y)) == -signum(compare(y, x))

  @law def transitive(x: T, y: T, z: T): Boolean =
    !(compare(x, y) > 0 && compare(y, z) > 0) || (compare(x, z) > 0)

  @law
  def consistent(x: T, y: T, z: T): Boolean =
    !(compare(x, y) == 0) || (signum(compare(x, z)) == signum(compare(y, z)))
}
