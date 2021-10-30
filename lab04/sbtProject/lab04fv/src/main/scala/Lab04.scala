

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
    flatten(pushForallOutwards(intermediateNoPrenex))
  }

  type Clause = List[Formula]

  /*
  This may exponentially blowup the size in the formula in general.
  If we only preserve satisfiability, we can avoid it by introducing fresh predicates, but that is not asked here.
   */
  def conjunctionPrenexSkolemizationNegation(f: Formula): List[Clause] = {
    /* Removes forall quantifiers from the given formula which is assumed
        to be in prenex skolemized negative normal form
     */
    def excludeOutterFors(f: Formula): Formula = f match {
      case Forall(_, inner) => excludeOutterFors(inner)
      case Exists(_, _) | Implies(_, _) => throw new Exception("Unexpected matching")
      case other => other
    }

    /* Does Cartesian product on curr addition to it and an accumulator of previous products, i.e. curr can be seen as A,
        while the accumulator could be seen as B1 X B2 X ... X Bm, the final result is A X B1 X B2 X ... X Bm. The
        parameters are passed in the given way so that the function can work effortlessly with foldRight
     */
    def product[A](curr: List[A], acc: List[List[A]]): List[List[A]] =
      for(el <- curr; sub <- acc) yield el :: sub

    /* Transforms the passed formula, assumed to be in prenex skolemized negative normal form without
        forall quantifiers, into conjuctive normal form
     */
    def conjunctiveNormalTransformation(f: Formula): Formula = f match {
      case p @ Predicate(_, _) => p
      case Neg(inner) => Neg(conjunctiveNormalTransformation(inner))
      case And(children) => {
        // Make sure all children are in conjuctive normal form
        val childrenResults = children map conjunctiveNormalTransformation
        // Top level only flatten (flatten could be used instead, but this is optimization of it for the
        //  given use-case
        val finalChildren = childrenResults flatMap {
          _ match {
            case And(subchildren) => subchildren
            case other => List(other)
          }
        }
        And(finalChildren)
      }
      case Or(children) => {
        // Make sure all children are in conjuctive normal form
        val childrenResults = children map conjunctiveNormalTransformation
        // The rest of the matching code pushes AND outwards, while putting OR inward
        val extractedFormulas: List[List[Formula]] = childrenResults map {
          _ match {
            case And(andChildren) => andChildren
            case other => List(other)
          }
        }
        val andOrLists: List[List[Formula]] = extractedFormulas.foldRight(List(List[Formula]()))(product)
        And(andOrLists map {
          Or(_)
        })
      }
      case Implies(_, _) | Forall(_, _) | Exists(_, _) => throw new Exception("Unexpected matching")
    }

    val prenex: Formula = prenexSkolemizationNegation(f)
    val prenexForsExcluded: Formula = excludeOutterFors(prenex)

    /* Transofrms formula to conjuctive normal form and extracts subformulas into lists as stated in the function
        requirement
    */
    conjunctiveNormalTransformation(prenexForsExcluded) match {
      case And(children) => children map { _ match {
        case Or(subchildren) => subchildren
        case other => List(other)
      }}
      case Or(children) => List(children)
      case other => List(List(other))
    }
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
    /* Tries substitution on the term multiple time until it no longer changes */
    def substituteTermWhileYouCan(term: Term, subst: Map[Var, Term]): Term = {
      val substitutionResult = substitute(term, subst)
      if(term equals substitutionResult)
        term
      else
        substituteTermWhileYouCan(substitutionResult, subst)
    }

    /* Substitute all terms in the formula according to the given substitution map */
    def formulaWideSubstitution(f: Formula, subst: Map[Var, Term]): Formula = f match {
      case Predicate(name, children) => Predicate(name, children map { substituteTermWhileYouCan(_, subst) })
      case Neg(inner) => Neg(formulaWideSubstitution(inner, subst))
      case And(_) | Or(_) | Implies(_, _) | Forall(_, _) | Exists(_, _) => throw new Exception("Unexpected matching")
    }

    /* Returns negation of the given formula */
    def negate(f: Formula): Formula = f match {
      case Neg(inner) => inner
      case other => Neg(other)
    }

    /* Returns whether toDeduce clause can be obtained by substituting terms in premice_1 and premice_2 according
        to the given substitution map and applying or between the clauses
     */
    def isDeducible(premice_1: Clause, premice_2: Clause, subst: Map[Var, Term], toDeduce: Clause): Boolean = {
      /* substitute and negate the first premice. Negation is done only on this since if this premice contains negations
          of the formulas in the second premice, by doing negation we would obtain same formulas as in the second premice
          and that makes it possible to do set operations that nonsensitive on order of formulas in a clause
       */
      val premice_1SubstedNegated = premice_1.map{ x => negate(formulaWideSubstitution(x, subst)) }.toSet
      // Only substitution is done on the second clause
      val premice_2Substed = premice_2.map{ formulaWideSubstitution(_, subst) }.toSet

      /* Do union of differences of both sides, but difference on the side of the first premise has
          to be negated back to its original form
       */
      val resultingClauseSet = premice_1SubstedNegated.diff(premice_2Substed).map(negate).union(
        premice_2Substed diff premice_1SubstedNegated
      )
      // make the clause that has to be deduced into a set and compare it with the resulting clause
      toDeduce.toSet equals resultingClauseSet
    }

    // Returns whether it is possible that there is an element in the list under given id (helper function)
    def isIndexValid[A](l: List[A], id: Int): Boolean = id >= 0 && id < l.size

    // Returns whether the clause is valid under given justification
    def isValid(clause: Clause, justification: Justification): Boolean = justification match {
      case Assumed => true
      case Deduced((premice_id_1, premice_id_2), subst) => isIndexValid(proof, premice_id_1) &&
        isIndexValid(proof, premice_id_2) &&
        isDeducible(proof(premice_id_1)._1, proof(premice_id_2)._1, subst, clause)
    }

    // Recursive way of looping through proofs and checking whether each of them is true
    def checkRemainingProofs(proofRemainder: ResolutionProof): Boolean = proofRemainder match {
      case Nil => true
      case (clause, justification) :: tail => isValid(clause, justification) && checkRemainingProofs(tail)
    }

    checkRemainingProofs(proof)
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
    case Neg(inner) => s"¬${formulaToString(inner)}"
    case And(children) => {
      val childrenStrings = children.map(x => s"${formulaToString(x)}")
      if(childrenStrings.length == 0)
        childrenStrings(0)
      else
        s"(${childrenStrings.mkString(" ∧ ")})"
    }
    case Or(children) => {
      val childrenStrings = children.map(x => s"${formulaToString(x)}")
      if(childrenStrings.length == 0)
        childrenStrings(0)
      else
        s"(${childrenStrings.mkString(" ∨ ")})"
    }
  }

  /* Prints the given formula in math-like representation to the command line */
  def printlnFormula(f: Formula): Unit = println(formulaToString(f))

  /* Returns the given substitution map as a human readable string */
  def substMapToString(substMap: Map[Var, Term]): String = {
    val entriesString = substMap.map{ case (v, t) => s"${termToString(v)} -> ${termToString(t)}"}
    s"{${ entriesString mkString ", " }}"
  }

  /* Prints resolution proof in a fancy format like in the slides */
  def printProof(proof: ResolutionProof): Unit =
    for(((clause, justification), index) <- proof.zipWithIndex) {
      val (justificationPrefixString, justificationPostString) = justification match {
        case Assumed => ("", "")
        case Deduced((_1, _2), subst) => (
          s"(${_1.toString}, ${_2.toString}): ",
          "\t\t\t\t" + substMapToString(subst)
        )
      }

      val clauseString = clause map formulaToString mkString " ∨ "
      println(s"$index. $justificationPrefixString$clauseString $justificationPostString")
    }

  def main(args: Array[String]): Unit = {
    /* Makes resolution proof with only assumptions out of given list of clauses such that each the assumptions tell
        that the given clauses are true
     */
    def makeAssumptionsOutOfClauses(clauses: List[Clause]): ResolutionProof =
      clauses map { (_, Assumed) }

    // Set of assumptions from the text of the problem
    val mansionMysteryClaims: ResolutionProof =
      makeAssumptionsOutOfClauses(conjunctionPrenexSkolemizationNegation(mansionMystery))

    // Mathematical properties that comes into help
    val additionalAssumptionsFormula = And(List(
      // equality commutation
      Forall("x", Forall("y", Implies(eq(Var("x"), Var("y")), eq(Var("y"), Var("x"))))),
      // Leibniz property
      Forall("x", Forall("y", Forall("z", Implies(eq(Var("x"), Var("y")),
        Implies(killed(Var("x"), Var("z")), killed(Var("y"), Var("z")))))))
    ))
    val additionalAssumptions: ResolutionProof = makeAssumptionsOutOfClauses(
      conjunctionPrenexSkolemizationNegation(additionalAssumptionsFormula))

    // Deduction of the conclusion
    val intermediateSteps: ResolutionProof = List(
      (List(hates(a, a)), Deduced((10, 16), Map(Var("x5") -> a))),
      (List(Neg(hates(c, a))), Deduced((8, 19), Map(Var("x3") -> a))),
      (List(eq(Function("s1", List()), a), eq(Function("s1", List()), b), eq(Function("s1", List()), c)),
        Deduced((0, 5), Map(Var("x0") -> Function("s1", List())))),
      (List(killed(Function("s1", List()), a), eq(Function("s1", List()), a), eq(Function("s1", List()), b),
        eq(Function("s1", List()), c)), Deduced((1, 21), Map())),
      (List(killed(a, a), eq(Function("s1", List()), b), eq(Function("s1", List()), c)),
        Deduced((18, 22), Map(Var("x2") -> Function("s1", List()), Var("x3") -> a, Var("x4") -> a))),
      (List(killed(a, a), killed(Function("s1", List()), a), eq(Function("s1", List()), b),
        eq(Function("s1", List()), c)), Deduced((1, 23), Map())),
      (List(killed(a, a), killed(b, a), eq(Function("s1", List()), c)),
        Deduced((18, 24), Map(Var("x2") -> Function("s1", List()), Var("x3") -> b, Var("x4") -> a))),
      (List(killed(a, a), killed(b, a), killed(Function("s1", List()), a), eq(Function("s1", List()), c)), Deduced((1, 25), Map())),
      (List(killed(a, a), killed(b, a), killed(c, a)),
        Deduced((18, 26), Map(Var("x2") -> Function("s1", List()), Var("x3") -> c, Var("x4") -> a))),
    )

    // Adds the three parts of the proof into a single one
    val proof = mansionMysteryClaims ++ additionalAssumptions ++ intermediateSteps

    // Printing the whole proof
    println("Proof: ")
    printProof(proof)
    println()

    // Checking validity of the proof
    println("Validity of the proof: " + checkResolutionProof(proof))
  }

}
