package ulang

sealed trait Expr extends Expr.term with Pretty {
  def free: Set[Id]

  def <=(that: Expr): Boolean = (this, that) match {
    case (_, Wildcard) =>
      true
    case (App(fun1,arg1), App(fun2, arg2)) =>
      fun1 <= fun2 && arg1 <= arg2
    case _ =>
      this == that
  }
}

object ProofTermChecker {

  /** Check a proof
   *
   *  The proof is assumed to have no global assumptions.
   */
  def check(proof: Expr, goal: Expr): Option[String] = check(Map(), proof, goal)

  /** Check a proof with context
   *
   *  This implements checking of proofs according to the
   *  Brouwer-Heyting-Kolmogorov interpretation of proofs (see Schwichtenberg
   *  & Wainer "Proofs and Computations", 2012, CUP, p313-314).
   *
   *  If a proof should be allowed to use axioms, they need to be present in
   *  the context.
   */
  def check(assumptions: Map[Id, Expr], proof: Expr, goal: Expr): Option[String] =
    (proof, goal) match {

      // Proof by assumption has to be the first case, this makes it possible
      // to match against any goal (even "False").  If the given goal is not
      // in the context we fall through to the other cases.
      case (id: Id, _) if assumptions.contains(id) =>
        if (assumptions(id) == goal) None
        else Some(f"Assumption $id does not match the goal $goal")
      // TODO if the id was not found in the local assumptions we want to look
      // at the gloablly available lemmas  (and axioms etc) or at defined
      // functions which the user might use to proof something.
      // Here local assumptions shadow lemmas which in turn shadow global
      // functions.
      //case (id: Id, _) if global_lemmas.contains(id) =>
      //  canBeUnified(global_lemmas(id), goal)
      //case (id: Id, _) if funs.contains(id) =>
      //  canBeUnified(funs(id), goal)

      // special cases
      case (True, True) => None // we use "True" to represent a trivial proof

      // propositional logic: introduction rules
      case (Pair(p1, p2), And(f1, f2)) =>
        check(assumptions, p1, f1) orElse check(assumptions, p2, f2)
      case (LeftE(p), Or(f, _)) => check(assumptions, p, f)
      case (RightE(p), Or(_, f)) => check(assumptions, p, f)
      // special case for one argument lambdas with a variable pattern
      case (Lam1(id, body), Imp(f1, f2)) =>
        check(assumptions + (id -> f1), body, f2)
      // and elimination
      case (Lam(List(Case(List(Pair(p1: Id, p2: Id)), body))), Imp(And(f1, f2), f3)) =>
        check(assumptions + (p1 -> f1) + (p2 -> f2), body, f3)
      case (Lam(List(Case(List(LeftE(p1: Id)), body))), Imp(Or(f1, _), f2)) =>
        check(assumptions + (p1 -> f1), body, f2)
      case (Lam(List(Case(List(RightE(p1: Id)), body))), Imp(Or(_, f1), f2)) =>
        check(assumptions + (p1 -> f1), body, f2)

      // Special cases for modus ponens
      // this is only a simpler case of the next case, the implementation
      // there also checks this case correctly
      case (App(f: Id, arg: Id), _)
      if assumptions.contains(f) && assumptions.contains(arg) =>
        val t1 = assumptions(f)
        val t2 = assumptions(arg)
        if (t1 == Imp(t2, goal)) None
        else Some(f"Formulas do not match: $t1 should be equal to $t2 ==> $goal")
      case (App(f: Id, arg), _)
        if assumptions.contains(f) && (assumptions(f) match {
          case Imp(precond, `goal`) => check(assumptions, arg, precond) match {
            case None => true
            case _ => false
          }
          case _ => false
        })
        => None
      case (App(Lam1(id, body), arg), _) =>
        check(assumptions, body.subst(Map(id -> arg)), goal)
      // generall applications need type inference for either the left or the
      // right side.  We use the left side for now.
      case (App(f, arg), _) =>
        infer(assumptions, arg) match {
          case Right(ty) => check(assumptions, f, Imp(ty, goal))
          // TODO there should be a case for all-elim here?
          case Left(err) => Some(err)
        }

      // propositional logic: elimination rules TODO
      // We could also introduce special term constructors that are recognized
      // here in order to eliminate connective: Elim-/\-1, Elim-/\-2, Elim-\/,
      // etc.

      // predicate logic introduction rules
      case (Pair(witness, p), Ex(id, matrix)) =>
        check(assumptions, p, matrix.subst(Map(id -> witness)))
      case (LamIds(params, body), All(id, matrix)) =>
        // For all-introduction there is a variable condition: the bound
        // variable must not occur free in any open assumption in body.
        // We emulate this by filtering all assumptions from the current proof
        // context where the vars are occurring free.
        // TODO is this enough to implement the variable condition?  With this
        // we must only accept closed formulas in open assumptions (lemmas and
        // axioms).
        def filtered = assumptions.filter(!_._2.free.contains(id))
        params match {
          case Nil => Some("Lambda abstraction without a variable!")
          case List(p) => check(filtered, body, matrix.subst(Map(id -> p)))
          // We unfold the list of quantified variables into a list of
          // universal quantifiers with one variable each.
          case p::ps =>
            check(filtered, LamIds(ps, body), matrix.subst(Map(id -> p)))
        }

      // TODO predicate logic elimination rules?

      // False is implicit here
      case _ => Some(f"Proof term $proof does not match the formula $goal.")
    }

  /**
   * Type inference for the proof checker
   */
  def infer(ctx: Map[Id, Expr], expr: Expr): Either[String, Expr] = expr match {
    case id: Id => ctx get id toRight s"Not in current type inference context: $id"
    case Pair(a, b) => infer(ctx, a).flatMap(a => infer(ctx, b).map(b => And(a, b))) // TODO existential quantifier?
    case LeftE(a) => infer(ctx, a).map(a => Or(a, ulang.Wildcard))
    case RightE(a) => infer(ctx, a).map(a => Or(ulang.Wildcard, a))
    case Lam1(v, body) => infer(ctx, v).flatMap(t1 => infer(ctx + (v -> t1), body).map(t2 => Imp(t1, t2))) // TODO universal quantifier?
    case _ => Left("Type inference for " + expr + " is not yet implemented.")
  }

  // TODO these functions are suggested by Gidon in order to check elimination
  // and introduction rules seperately.
  //def bind(ctx: Map[Id, Expr], pat: Expr, assm: Expr): Map[Id,Expr] =
  //  (pat, assm) match {
  //    case (Pair(p1, p2), And(a1, a2)) => bind(bind(ctx, p1, a1), p2, a2)
  //    case (LeftE(p), Or(f, _)) => bind(ctx, p, f)
  //    case (RightE(p), Or(_, f)) => bind(ctx, p, f)
  //  }
  //def elim(ctx: Map[Id, Expr], pats: List[Expr], body: Expr, goal: Expr): Boolean =
  //  (pats, goal) match {
  //    case (Nil, _) => check(ctx, body, goal)
  //    case (pat::rest, Imp(assm, concl)) =>
  //      val ctx_ = bind(ctx, pat, assm)
  //      elim(ctx_, rest, body, concl)
  //  }
  //def elim(ctx: Map[Id, Expr], cs: Case, goal: Expr): Boolean = ???
  //def elim(ctx: Map[Id, Expr], cases: List[Case], goal: Expr): Boolean =
  //  cases.forall(elim(ctx, _, goal))
}

object Expr extends Alpha[Expr, Id]

sealed trait Val extends Pretty
sealed trait Norm extends Val
sealed trait Data extends Norm

case object Wildcard extends Expr {
  def free = Set()
  def rename(re: Map[Id, Id]) = this
  def subst(su: Map[Id, Expr]) = this
}

case class Id(name: String, index: Option[Int]) extends Expr with Data with Expr.x {
  import context._
  def this(name: String) = this(name, None)
  def free = if(isTag(this) || isFun(this)) Set() else Set(this)
  def fresh(index: Int) = Id(name, Some(index))
}

object Id extends (String => Id) {
  def apply(name: String): Id = {
    Id(name, None)
  }
}

case class App(fun: Expr, arg: Expr) extends Expr {
  def free = fun.free ++ arg.free
  def rename(re: Map[Id, Id]) = App(fun rename re, arg rename re)
  def subst(su: Map[Id, Expr]) = App(fun subst su, arg subst su)
}

case class Ite(test: Expr, left: Expr, right: Expr) extends Expr {
  def free = test.free ++ left.free ++ right.free
  def rename(re: Map[Id, Id]) = Ite(test rename re, left rename re, right rename re)
  def subst(su: Map[Id, Expr]) = Ite(test subst su, left subst su, right subst su)
}

case class Case(pats: List[Expr], body: Expr) extends Expr.bind[Case] with Pretty {
  def arity = pats.length
  def free = body.free -- bound
  def bound = pats.free
  def rename(a: Map[Id, Id], re: Map[Id, Id]) = Case(pats rename a, body rename re)
  def subst(a: Map[Id, Id], su: Map[Id, Expr]) = Case(pats rename a, body subst su)
}

case class Case1(pat: Expr, arg: Expr) extends Pretty {
  def free = arg.free
  def bound = pat.free
  def rename(a: Map[Id, Id], re: Map[Id, Id]) = Case1(pat rename a, arg rename re)
  def subst(a: Map[Id, Id], su: Map[Id, Expr]) = Case1(pat rename a, arg subst su)
}

case class Lam(cases: List[Case]) extends Expr {
  def free = cases.free
  def bound = cases.bound
  def rename(re: Map[Id, Id]) = Lam(cases rename re)
  def subst(su: Map[Id, Expr]) = Lam(cases subst su)
}

case class Match(args: List[Expr], cases: List[Case]) extends Expr {
  def free = args.free ++ cases.free
  def rename(re: Map[Id, Id]) = Match(args rename re, cases rename re)
  def subst(su: Map[Id, Expr]) = Match(args subst su, cases subst su)
}

case class Let(eqs: List[Case1], body: Expr) extends Expr with Expr.bind[Let] {
  def pats = eqs.pats
  def args = eqs.args
  def bound = eqs.bound
  def free = eqs.free ++ (body.free -- bound)
  def rename(a: Map[Id, Id], re: Map[Id, Id]) = Let(eqs rename (a, re), body rename re)
  def subst(a: Map[Id, Id], su: Map[Id, Expr]) = Let(eqs subst (a, su), body subst su)
}

sealed trait Quant extends ((List[Id], Expr) => Expr) {
  def apply(args: List[Id], body: Expr): Expr = args match {
    case Nil => body
    case arg::args => Bind(this, arg, this(args, body))
  }
  def apply(arg: Id,  body: Expr) = Bind(this, arg, body)

  def unapply(expr: Expr) = expr match {
    case Bind(quant, arg, body) if quant == this =>
      Some((arg, body))
    case _ =>
      None
  }
}

case object Ex extends Quant
case object All extends Quant

case class Bind(quant: Quant, args: Id, body: Expr) extends Expr with Expr.bind[Bind] {
  def bound = Set(args)
  def free = body.free -- bound
  def rename(a: Map[Id, Id], re: Map[Id, Id]) = Bind(quant, args rename a, body rename re)
  def subst(a: Map[Id, Id], su: Map[Id, Expr]) = Bind(quant, args rename a, body subst su)
}

case class Obj(fun: Data, arg: Val) extends Data

case class Curry(cases: List[Case], rargs: List[Val], lex: Env) extends Data {
  ensure(cases.nonEmpty, "curried function with no cases")
  ensure(cases forall (_.arity == arity), "curried function with mixed arities")
  ensure(rargs.length <= arity, "curried function with too many arguments")
  def isComplete = arity == rargs.length
  def arity = cases.head.arity
}

case class Defer(expr: Expr, lex: Env) extends Val {
  override def toString = expr.toString
  lazy val norm = Eval.norm(expr, lex)
}
