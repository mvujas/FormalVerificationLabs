object Lab04 {

  // Term syntax
  sealed abstract class Term
  case class Var(name: String) extends Term
  case class Function(name: String, children: List[Term]) extends Term

  //Formula syntax
  sealed abstract class Formula
  case class Predicate(name: String, children: List[Term]) extends Formula

  case class And(children: List[Formula]) extends Formula
  case class Or(children: List[Formula]) extends Formula
  case class Implies(left: Formula, right: Formula) extends Formula
  case class Neg(inner: Formula) extends Formula

  case class Forall(variable: String, inner: Formula) extends Formula
  case class Exists(variable: String, inner: Formula) extends Formula

  /*
  Computes the free variables of a Term, respectively a Formula.
   */
  def freeVariables(t: Term): Set[Var] = t match {
    case v: Var                   => Set(v)
    case Function(name, children) => children.flatMap(freeVariables).toSet
  }
  def freeVariables(f: Formula): Set[Var] = f match {
    case Predicate(name, children) => children.flatMap(freeVariables).toSet
    case And(children)             => children.flatMap(freeVariables).toSet
    case Or(children)              => children.flatMap(freeVariables).toSet
    case Implies(left, right)    => freeVariables(left) ++ freeVariables(right)
    case Neg(inner)              => freeVariables(inner)
    case Forall(variable, inner) => freeVariables(inner) - Var(variable)
    case Exists(variable, inner) => freeVariables(inner) - Var(variable)
  }

  /*
  Performs simultaneous substitution of Vars by Terms
   */
  def substitute(t: Term, subst: Map[Var, Term]): Term = t match {
    case v: Var => subst.getOrElse(v, v)
    case Function(name, children) =>
      Function(name, children.map(substitute(_, subst)))
  }
  //We don't need substitution in Formulas, which conveniently avoid having to implement capture avoiding substitution.

  /*
  Make sure that all bound variables are uniquely named, and with names different from free variables.
  This will simplify a lot future transformations. The specific renaming can be arbitrary
   */
  def makeVariableNamesUnique(f: Formula): Formula = {
    var i: Int = 0
    def mVNUForm(f: Formula, subst: Map[Var, Var]): Formula = {
      f match {
        case Predicate(name, children) =>
          Predicate(name, children.map(t => substitute(t, subst)))
        case And(children) => And(children.map(s => mVNUForm(s, subst)))
        case Or(children)  => Or(children.map(s => mVNUForm(s, subst)))
        case Implies(left, right) =>
          Implies(mVNUForm(left, subst), mVNUForm(right, subst))
        case Neg(inner) => Neg(mVNUForm(inner, subst))
        case Forall(variable, inner) =>
          val nvar = "x" + i
          i += 1
          val t = mVNUForm(inner, subst + ((Var(variable), Var(nvar))))
          Forall(nvar, t)
        case Exists(variable, inner) =>
          val nvar = "x" + i
          i += 1
          val t = mVNUForm(inner, subst + ((Var(variable), Var(nvar))))
          Exists(nvar, t)
      }
    }
    val alreadyTaken =
      freeVariables(f).zipWithIndex.map(p => (p._1, Var("x" + p._2)))
    i = alreadyTaken.size
    mVNUForm(f, alreadyTaken.toMap)
  }

  /*
  Put the formula in negation normal form.
   */
  def negationNormalForm(f: Formula): Formula = {

    /** Applies negation to all formulas in the list */
    def NegAll(fs: List[Formula]): List[Formula] = fs map { Neg(_) }

    /** Does a simple reduction pass of transformation to negation normal form
      */
    def reductionPass(f: Formula): Formula = f match {
      case Implies(a, b) => Or(List(Neg(reductionPass(a)), reductionPass(b)))
      case Neg(Neg(a))   => reductionPass(a)
      case Neg(And(children)) => Or(NegAll(children))
      case Neg(Or(children))  => And(NegAll(children))
      case Neg(Forall(x, a))  => Exists(x, Neg(reductionPass(a)))
      case Neg(Exists(x, a))  => Forall(x, Neg(reductionPass(a)))

      case p @ Predicate(_, _) => p
      case And(children)       => And(children map reductionPass)
      case Or(children)        => Or(children map reductionPass)
      case Neg(a)              => Neg(reductionPass(a))
      case Forall(v, a)        => Forall(v, reductionPass(a))
      case Exists(v, a)        => Exists(v, reductionPass(a))
    }

    /** Checks whether the given formula can be reduced anymore */
    def isReductionPossible(f: Formula): Boolean = f match {
      case Implies(_, _)     => true
      case Neg(Neg(_))       => true
      case Neg(And(_))       => true
      case Neg(Or(_))        => true
      case Neg(Forall(_, _)) => true
      case Neg(Exists(_, _)) => true

      case Predicate(_, _) => false
      case And(children) =>
        children.foldLeft(false) { (acc, curr) =>
          acc || isReductionPossible(curr)
        }
      case Or(children) =>
        children.foldLeft(false) { (acc, curr) =>
          acc || isReductionPossible(curr)
        }
      case Neg(a)       => isReductionPossible(a)
      case Forall(_, a) => isReductionPossible(a)
      case Exists(_, a) => isReductionPossible(a)
    }

    def reductor(f: Formula): Formula = if (isReductionPossible(f))
      reductor(reductionPass(f))
    else
      f

    flatten(reductor(f))
  }

  /*
  Put the formula in negation normal form and then eliminates existential quantifiers using Skolemization
   */
  def skolemizationNegation(f: Formula): Formula = {
    var i: Int = 0
    /* Performs skolemization formula that is already in negative normal form */
    def skolemize(f: Formula, subst: Map[Var, Term] = Map()): Formula =
      f match {
        case Predicate(name, terms) =>
          Predicate(name, terms map { substitute(_, subst) })
        case And(children) => And(children map { skolemize(_, subst) })
        case Or(children)  => Or(children map { skolemize(_, subst) })
        case Neg(inner)    => Neg(skolemize(inner, subst))
        case Forall(variable, inner) =>
          Forall(variable, skolemize(inner, subst))
        case exists @ Exists(variable, inner) => {
          i += 1
          val freeVariableFunction: Term =
            Function(s"s$i", freeVariables(exists).toList)
          val res =
            skolemize(inner, subst + (Var(variable) -> freeVariableFunction))
          res
        }
        case Implies(_, _) => throw new Exception("Unexpected matching")
      }

    flatten(skolemize(negationNormalForm(f)))
  }

  /*
  Return the matrix of f in negation normal, skolemized form and make sure variables are uniquely named. Since there are no existential
  quantifiers and all variable names are unique, the matrix is equivalent to the whole formula.
   */
  def prenexSkolemizationNegation(f: Formula): Formula = {
    /* Extracts all outter foralls into a function returned as the second element of the resulting tupple, while the
        first elemment of the tupple is the body of the innermost of the given foralls
     */
    def extractOutterForalls(f: Formula,
          cummulativeForallConstructor: Formula => Formula = identity): (Formula, Formula => Formula) = f match {
      case p @ Predicate(_, _) => (p, cummulativeForallConstructor)
      case neg @ Neg(_) => (neg, cummulativeForallConstructor)
      case and @ And(_) => (and, cummulativeForallConstructor)
      case or @ Or(_) => (or, cummulativeForallConstructor)
      case Forall(variable, inner) => extractOutterForalls(
        inner, cummulativeForallConstructor.compose(Forall(variable, _)))
    }

    /* Applies extractOutterForalls on the all elements of the given list and returns a tupple whose first element
        is the list of the repective first elements of the results of extractOutterForalls when applied to the list and
        the second is the composition of the functions returned as the second element of applying extractOutterForalls
        to each element
     */
    def extractOutterForallsFromList(fs: List[Formula]): (List[Formula], Formula => Formula) =
      fs.map{extractOutterForalls(_)}
        .foldRight((List[Formula](), identity[Formula](_))) { (current, acc) =>
          (current._1 :: acc._1, current._2.compose(acc._2))
        }

    /* Transforms given formula which does not contain existential quantifiers nor implications, and has all
        variables uniquely named into its prenex form
     */
    def pushForallOutwards(f: Formula): Formula = f match {
      case p @ Predicate(_, _) => p
      case Neg(inner) => {
        val (notFor, forAllWrapperConstructor) = extractOutterForalls(pushForallOutwards(inner))
        forAllWrapperConstructor(Neg(notFor))
      }
      case And(children) => {
        val (notForChildren, forAllWrapperConstructor) = extractOutterForallsFromList(children map pushForallOutwards)
        forAllWrapperConstructor(And(notForChildren))
      }
      case Or(children) => {
        val (notForChildren, forAllWrapperConstructor) = extractOutterForallsFromList(children map pushForallOutwards)
        forAllWrapperConstructor(Or(notForChildren))
      }
      case Forall(variable, inner) => Forall(variable, pushForallOutwards(inner))
      case Exists(_, _) | Implies(_, _) => throw new Exception("Unexpected matching")
    }

    val intermediateNoPrenex = makeVariableNamesUnique(skolemizationNegation(f))
    pushForallOutwards(intermediateNoPrenex)
  }

  type Clause = List[Formula]

  /*
  This may exponentially blowup the size in the formula in general.
  If we only preserve satisfiability, we can avoid it by introducing fresh predicates, but that is not asked here.
   */
  def conjunctionPrenexSkolemizationNegation(f: Formula): List[Clause] = {
    val prenex: Formula = prenexSkolemizationNegation(f)

    def removeUniversalQuantifiers(f: Formula): Formula = f match {
      case And(children) => And(children map removeUniversalQuantifiers)
      case Or(children)  => Or(children map removeUniversalQuantifiers)
      case Neg(inner)    => Neg(removeUniversalQuantifiers(inner))
      case Predicate(name, terms)  => Predicate(name, terms)
      case Forall(variable, inner) => removeUniversalQuantifiers(inner)
      case Implies(_, _)           => throw new Exception("Unexpected matching")
      case exists @ Exists(variable, inner) =>
        throw new Exception("Unexpected matching")
    }

    def conjunctiveNormalForm(f: Formula): List[Clause] = f match {
      case And(children) =>
        children.flatMap {
          case Or(c) =>
            c match {
              // given the logic of flatten, we can have such design?
              case head :: List(And(tail)) => tail.map(x => List(head, x))
              case _                       => List(c.toList)
            }
          case other => List(List(other))
        }
    }

    val body = flatten(removeUniversalQuantifiers(prenex))
    val cnf = conjunctiveNormalForm(body)
    cnf
  }
  /*
  A clause in a proof is either assumed, i.e. it is part of the initial formula, or it is deduced from previous clauses.
  A proof is written in a specific order, and a justification should not refer to a previous step.
   */
  sealed abstract class Justification
  case object Assumed extends Justification
  case class Deduced(premices: (Int, Int), subst: Map[Var, Term])
      extends Justification

  type ResolutionProof = List[(Clause, Justification)]

  /*
  Verify if a given proof is correct. The function should verify that every clause is correctly justified (unless assumed).

   */
  def checkResolutionProof(proof: ResolutionProof): Boolean = {
    ???
  }

  val a = Function("a", Nil)
  val b = Function("b", Nil)
  val c = Function("c", Nil)
  val x = Var("x")
  val y = Var("y")
  val z = Var("z")
  def lives(a: Term) = Predicate("lives", List(a))
  def killed(a: Term, b: Term) = Predicate("killed", List(a, b))
  def hates(a: Term, b: Term) = Predicate("hates", List(a, b))
  def richer(a: Term, b: Term) = Predicate("richer", List(a, b))
  def eq(a: Term, b: Term) = Predicate("=", List(a, b))

  val mansionMystery: Formula = And(
    List(
      Exists(
        "x",
        And(List(Predicate("lives", List(x)), Predicate("killed", List(x, a))))
      ),
      And(
        List(
          lives(a),
          lives(b),
          lives(c),
          Forall("x", Implies(lives(x), Or(List(eq(x, a), eq(x, b), eq(x, c)))))
        )
      ),
      Forall(
        "x",
        Forall(
          "y",
          Implies(killed(x, y), And(List(hates(x, y), Neg(richer(x, y)))))
        )
      ),
      Forall("x", Implies(hates(a, x), Neg(hates(c, x)))),
      Forall("x", Implies(hates(a, x), Neg(eq(x, b)))),
      Forall("x", Implies(Neg(eq(x, b)), hates(a, x))),
      Forall("x", Implies(hates(a, x), Neg(eq(x, b)))),
      Forall("x", Implies(hates(b, x), Neg(richer(x, a)))),
      Forall("x", Implies(Neg(richer(x, a)), hates(b, x))),
      Forall("x", Implies(Neg(hates(a, x)), hates(b, x))),
      Neg(Exists("x", Forall("y", hates(x, y)))),
      Neg(eq(a, b))
    )
  )

  /*
  To show that a formula phi is valid, we show that it's negation is unsatisfiable, i.e. !phi -> false.
  Hence if a Proof contains an empty clause, then the negation of the conjunction of all assumed clauses has to be valid
   */
  def extractTheorem(proof: ResolutionProof): Formula = {
    if (proof.exists(_._1.isEmpty))
      Neg(
        And(
          proof
            .filter(_._2 match {
              case Assumed                  => true
              case Deduced(premices, subst) => false
            })
            .map(_._1)
            .map(Or)
        )
      )
    else throw new Exception("The proof did not succeed")
  }

  def P(a: Term) = Predicate("P", List(a))
  def R(a: Term, b: Term) = Predicate("R", List(a, b))
  def f(a: Term, b: Term) = Function("f", List(a, b))
  def s1(a: Term) = Function("s1", List(a))
  val s2 = Function("s2", List())

  val exampleFromCourse: Formula = {
    val f1 = Forall("x", Exists("y", R(x, y)))
    val f2 = Forall("x", Forall("y", Implies(R(x, y), R(x, f(y, z)))))
    val f3 = Forall("x", Or(List(P(x), P(f(x, a)))))
    val f4 = Forall("x", Exists("y", And(List(R(x, y), P(y)))))

    Neg(Implies(And(List(f1, f2, f3)), f4))
  }

  val exampleFromCourseResult: List[Clause] = {
    val c1 = List(R(x, s1(x)))
    val c2 = List(Neg(R(x, y)), R(x, f(y, z)))
    val c3 = List(P(x), P(f(x, a)))
    val c4 = List(Neg(R(s2, y)), Neg(P(y)))
    List(c1, c2, c3, c4)
  }

  /** Helper function that transforms nested Ands and Ors into a single one */
  def flatten(f: Formula): Formula = f match {
    case p @ Predicate(_, _)     => p
    case Implies(left, right)    => Implies(flatten(left), flatten(right))
    case Neg(inner)              => Neg(flatten(inner))
    case Forall(variable, inner) => Forall(variable, flatten(inner))
    case Exists(variable, inner) => Exists(variable, flatten(inner))

    case Or(children) =>
      Or(
        children
          .map(flatten)
          .flatMap(_ match {
            case Or(subchildren) => subchildren
            case other           => List(other)
          })
      )
    case And(children) =>
      And(
        children
          .map(flatten)
          .flatMap(_ match {
            case And(subchildren) => subchildren
            case other            => List(other)
          })
      )
  }

  /* Returns string representation of the given term */
  def termToString(t: Term): String = t match {
    case Var(name) => name
    case Function(name, children) => if(children.isEmpty)
          name
        else
          s"$name(${children.map(termToString).mkString(",")})"
  }

  /* Returns string representation of the given term */
  def formulaToString(f: Formula): String = f match {
    case Predicate(name, children) => termToString(Function(name, children))
    case Forall(variable, inner) => s"∀$variable.${formulaToString(inner)}"
    case Exists(variable, inner) => s"∃$variable.${formulaToString(inner)}"
    case Implies(left, right) => s"(${formulaToString(left)}) → (${formulaToString(right)})"
    case Neg(inner) => s"¬(${formulaToString(inner)})"
    case And(children) => children.map(x => s"(${formulaToString(x)})").mkString(" ∧ ")
    case Or(children) => children.map(x => s"(${formulaToString(x)})").mkString(" ∨ ")
  }

  /* Prints the given formula in math-like representation to the command line */
  def printlnFormula(f: Formula): Unit = println(formulaToString(f))

  def main(args: Array[String]): Unit = {
    val f = Forall("x", Forall("y", And(List(Or(List(Neg(Exists("z", R(x, y))), Neg(P(a)))), Forall("m", Neg(P(b))), Forall("n", Neg(P(z)))))))

    printlnFormula(f)

    printlnFormula(prenexSkolemizationNegation(f))
//    println(prenexSkolemizationNegation(f))
//
//
//    println("∀")
//
//    println(prenexSkolemizationNegation(mansionMystery))
  }

}
