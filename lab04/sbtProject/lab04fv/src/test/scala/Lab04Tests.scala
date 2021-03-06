import Lab04._
import org.scalatest.FunSuite

class Lab04Tests extends FunSuite {

  val IndexedSeq(a, b, c, x, y, z) = (0 until 6) map { i => Predicate(s"p$i", List()) }



  def applicationTest(transformation: Formula => Formula)(lhs_in: Formula, rhs: Formula): Unit = {
    assert(flatten(transformation(lhs_in)) == flatten(rhs))
  }

  val flattenTest: (Formula, Formula) => Unit = applicationTest(identity)
  test("flattenAndTest") {
    val lhs_in = And(List(a, And(List(b, c))))
    val rhs = And(List(a, b, c))
    flattenTest(lhs_in, rhs)
  }

  test("flattenOrTest") {
    val lhs_in = Or(List(a, Or(List(b, c))))
    val rhs = Or(List(a, b, c))
    flattenTest(lhs_in, rhs)
  }


  val negationNormalFormTest: (Formula, Formula) => Unit = applicationTest(negationNormalForm)
  test("negativeNormalFormTest0") {
    val lhs_in: Formula = Implies(a, b)
    val rhs: Formula = Or(List(Neg(a), b))
    negationNormalFormTest(lhs_in, rhs)
  }

  test("negativeNormalFormTest1") {
    val lhs_in: Formula = Neg(Implies(And(List(a, b, c)), x))
    val rhs: Formula = And(List(a, b, c, Neg(x)))
    negationNormalFormTest(lhs_in, rhs)
  }

  // An example from the slides (might be faulty)
  test("negativeNormalFormTest2") {
    val (x, y, z, a) = (Lab04.x, Lab04.y, Lab04.z, Lab04.a)
    val lhs_in: Formula = Neg(And(List(
      Forall("x", Exists("y", R(x, y))),
      Forall("x", Forall("y",
        Implies(R(x, y), Forall("z", R(x, f(y, z))))
      )),
      Implies(
        Forall("x", Or(List(P(x), P(f(x, a))))),
        Forall("x", Exists("y", And(List(R(x, y), P(y)))))
      )
    )))
    val rhs: Formula = And(List(
      Forall("x", Exists("y", R(x, y))),
      Forall("x", Forall("y", Or(List(
        Neg(R(x, y)), Forall("z", R(x, f(y, z))))
      ))),
      Forall("x", Or(List(P(x), P(f(x, a))))),
      Exists("x", Forall("y", Or(List(
        Neg(R(x, y)), Neg(P(y)))
      )))
    ))

    negationNormalFormTest(lhs_in, rhs)
  }


  val skolemizationNegationTest: (Formula, Formula) => Unit = applicationTest(skolemizationNegation)
  test("skolemizationNegationTest1") {
    val (x, y) = (Lab04.x, Lab04.y)
    val lhs_in: Formula = Forall("x", Exists("y", R(x, y)))
    val rhs: Formula = Forall("x", R(x, Function("s1", List(x))))

    skolemizationNegationTest(lhs_in, rhs)
  }

  test("skolemizationNegationTest2") {
    val (x, y) = (Lab04.x, Lab04.y)
    val lhs_in: Formula = Exists("x", Forall("y", Or(List(Neg(R(x, y)), Neg(P(y))))))
    val rhs: Formula = Forall("y", Or(List(Neg(R(Function("s1", List()), y)), Neg(P(y)))))

    skolemizationNegationTest(lhs_in, rhs)
  }

  test("skolemizationNegationTestBig") {
    val (x, y, z, a) = (Lab04.x, Lab04.y, Lab04.z, Lab04.a)
    val lhs_in: Formula = And(List(
      Forall("x", Exists("y", R(x, y))),
      Forall("x", Forall("y", Or(List(
        Neg(R(x, y)), Forall("z", R(x, f(y, z))))
      ))),
      Forall("x", Or(List(P(x), P(f(x, a))))),
      Exists("x", Forall("y", Or(List(
        Neg(R(x, y)), Neg(P(y)))
      )))
    ))
    val rhs: Formula = And(List(
      Forall("x", R(x, Function("s1", List(x)))),
      Forall("x", Forall("y", Or(List(
        Neg(R(x, y)), Forall("z", R(x, f(y, z))))
      ))),
      Forall("x", Or(List(P(x), P(f(x, a))))),
      Forall("y", Or(List(Neg(R(Function("s2", List()), y)), Neg(P(y)))))
    ))

    skolemizationNegationTest(lhs_in, rhs)
  }



  test("resolutionTestLectures") {
    import Lab04._
    val (x, y, z, a) = (Lab04.x, Lab04.y, Lab04.z, Lab04.a)
    val proof = List(
      (List(R(x, s1(x))), Assumed),
      (List(Neg(R(x, y)), R(x, f(y, z))), Assumed),
      (List(P(x), P(f(x, a))), Assumed),
      (List(Neg(R(s2, y)), Neg(P(y))), Assumed),
      (List(R(x, f(s1(x), z))), Deduced((0, 1), Map(y -> s1(x)))),
      (List(Neg(P(s1(s2)))), Deduced((0, 3), Map(x -> s2, y -> s1(x)))),
      (List(P(f(s1(s2), a))), Deduced((2, 5), Map(x -> s1(s2)))),
      (List(Neg(R(s2, f(s1(s2), a)))), Deduced((3, 6), Map(y -> f(s1(s2), a))))
    )
    // No clue how to represent false...
    assert(checkResolutionProof(proof))
  }

  test("resolutionTestLecturesModifiedToBeIncorrect") {
    import Lab04._
    val (x, y, z, a) = (Lab04.x, Lab04.y, Lab04.z, Lab04.a)
    val proof = List(
      (List(R(x, s1(x))), Assumed),
      (List(Neg(R(x, y)), R(x, f(y, z))), Assumed),
      (List(P(x), P(f(x, a))), Assumed),
      (List(Neg(R(s2, y)), Neg(P(y))), Assumed),
      (List(R(x, f(s1(x), z))), Deduced((0, 1), Map(y -> s1(s2)))),
      (List(Neg(P(s1(s2)))), Deduced((0, 3), Map(x -> s2, y -> s1(x)))),
      (List(P(f(s1(s2), a))), Deduced((2, 5), Map(x -> s1(a)))),
      (List(Neg(R(s2, f(s1(s2), a)))), Deduced((3, 6), Map(y -> f(s1(s2), a))))
    )
    assert(!checkResolutionProof(proof))
  }
}
