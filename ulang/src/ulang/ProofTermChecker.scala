package ulang

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
      case (id: Id, _) if assumptions contains id =>
        if (assumptions(id) == goal) None
        else Some(f"Assumption $id does not match the goal $goal")
      // TODO lemmas and axioms etc should shadow defined functions
      //case (id: Id, _) if global_lemmas.contains(id) =>
      //  canBeUnified(global_lemmas(id), goal)
      case (id: Id, _) if context.funs contains id =>
        check(assumptions, Lam(context.funs(id)), goal)
      case (Id("elim", None), _) =>
        Some("The special function name 'elim' can only be used in applications.")
      case (Id("intro", None), _) =>
        Some("The special function name 'intro' can only be used in applications.")

      // special cases
      case (True, True) => None // we use "True" to represent a trivial proof

      // propositional logic: introduction rules
      case (Pair(p1, p2), And(f1, f2)) =>
        check(assumptions, p1, f1) orElse check(assumptions, p2, f2)
      case (LeftE(p), Or(f, _)) => check(assumptions, p, f)
      case (RightE(p), Or(_, f)) => check(assumptions, p, f)
      // special case for lambdas with one pattern only
      case (Lam(List(Case(List(pat), body))), Imp(ant, cons)) =>
        check(bind(assumptions, pat, ant), body, cons)

      // propositional logic: elimination rules TODO
      // We could also introduce special term constructors that are recognized
      // here in order to eliminate connective: Elim-/\-1, Elim-/\-2, Elim-\/,
      // etc.

      // predicate logic introduction rules
      case (Witness(witness, p), Ex(id, matrix)) =>
        check(assumptions, p, matrix.subst(Map(id -> witness)))
      case (LamId(param, body), All(id, matrix)) =>
        // For all-introduction there is a variable condition: the bound
        // variable must not occur free in any open assumption in body.
        val openFree = Expr free assumptions
        if (openFree contains id) Some("Capturing variable " + id)
        else check(assumptions, body, matrix.rename(Map(id -> param)))

      // TODO predicate logic elimination rules?

      // different cases for modus ponens
      case (App(LamId(id, body), arg), _) =>
        check(assumptions, body.subst(Map(id -> arg)), goal)
      // FIXME can this be merged into the next case?
      case (App(f: Id, arg: Id), _)
      if assumptions.contains(f) && assumptions.contains(arg) =>
        val fTy = assumptions(f)
        val argTy = assumptions(arg)
        if (fTy == Imp(argTy, goal)) None
        else if (argTy.isInstanceOf[Id] && fTy == All(argTy.asInstanceOf[Id], goal)) None
        else Some(f"Formulas do not match: $fTy should be equal to $argTy ==> $goal or forall $argTy. $goal")
      case (App(f: Id, arg), _)
        if assumptions.contains(f) && (assumptions(f) match {
          case Imp(precond, `goal`) => check(assumptions, arg, precond).isEmpty
          case All(x, matrix) => goal == matrix.subst(Map(x -> arg))
          case _ => false
        })
        // If the pattern guard did succeed we have already checked the proof
        // fully.  If the check failed we want to fall through to the lower
        // cases.
        => None
      // general applications need type inference for either the left or the
      // right side.  We use the left side for now.
      case (App(f, arg), _) =>
        infer(assumptions, arg) match {
          case Right(ty) if check(assumptions, f, Imp(ty, goal)).isEmpty => None
          case Right(ty: Id) => check(assumptions, f, All(ty, goal))
          case Left(err1) =>
            infer(assumptions, f) match {
              case Right(Imp(a, `goal`)) => check(assumptions, a, arg)
              case Right(All(v, matrix)) if matrix.subst(Map(v -> arg)) == goal => None
              case Left(err2) => Some(err1 + "\n" + err2)
            }
        }

      // False is implicit here
      case _ => Some(f"Proof term $proof does not match the formula $goal.")
    }

  val infer = TypeInference(_, _)

  def bind(ctx: Map[Id, Expr], pat: Expr, assm: Expr): Map[Id,Expr] =
    (pat, assm) match {
      case (p: Id, _) => ctx + (p -> assm)
      case (Pair(p1, p2), And(a1, a2)) => bind(bind(ctx, p1, a1), p2, a2)
      case (LeftE(p), Or(f, _)) => bind(ctx, p, f)
      case (RightE(p), Or(_, f)) => bind(ctx, p, f)
      case (Witness(w, p), Ex(x, matrix)) => bind(bind(ctx, w, x), p, matrix)
    }

  // Functions that have been suggested by Gidon but are not yet implemented.
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
  //def apply(assumption: Map[Id, Expr], fun: Expr, arg: Expr): Expr =
  //  (fun, arg) match {
  //    case (LamId(v, body), _) => body.subst(Map(v -> arg))
  //    case (All(x, matrix), _) =>
  //       (forall x -> p) t == p[x -> t]
  //       (a ==> b) a       == b
  //  case _ => App(fun, arg)
  //}
}

/**
 * Type inference for the proof checker
 *
 * The algorithm is based on the lecture notes of Uli Schöpp from the lecure
 * "Typsysteme" (summer term 2018).
 */
object TypeInference extends ((Map[Id, Expr], Expr) => Either[String, Expr]) {

  import scala.util.Try

  // this type is used to represent type checking/inference context, equations
  // assiging types to type variables (used for equation solving and also as
  // substitutions)
  type Ctx = Map[Id, Expr]

  /**
   * TypeVar represents type variables used during type inference.  It relies
   * on the fact that the parser for ulang does not accept space in
   * identidiers.  This ensures that the generated variables are distinct from
   * all user generated identidiers.
   */
  object TypeVar extends (() => Id) {
    // a backspace makes these variables look nice in the output
    private val name = "ty \u0008"
    def apply() = Expr.fresh(Id(name))
    def unapply(id: Expr) = id match {
      case Id(`name`, index) => index
      case _ => None
    }
  }

  def apply(ctx: Ctx, term: Expr) = simple(ctx, term)

  case class InferenceError(error: String) extends Throwable {
    override def toString = error
  }

  def simple(ctx: Ctx, term: Expr): Either[String, Expr] =
    Try(simple_(ctx, term)).toEither.left.map(_.toString)
  def simple_(ctx: Ctx, term: Expr): Expr =
    term match {
      case id: Id =>
        ctx get id getOrElse(throw InferenceError(
          s"Not in current type inference context: $id"))
      case Pair(a, b) =>
        And(simple_(ctx, a), simple_(ctx, b))
      case LeftE(a) =>
        Or(simple_(ctx, a), ulang.Wildcard)
      case RightE(a) =>
        Or(ulang.Wildcard, simple_(ctx, a))
      case LamId(v, body) =>
        val v_ = Expr.fresh(v)
        // FIXME: Gidon uses "All(v_ ..." here?
        All(v, Imp(v, simple_(ctx + (v -> v), body)))
      case Lam(List(Case(List(pat), body))) =>
        val xs = pat.free.toList
        val as = xs map Expr.fresh
        val re = xs zip as
        val ctx_ = ctx ++ re
        val patT = simple_(ctx, pat)
        val bodyT = simple_(ctx, body)
        All(as, Imp(patT, bodyT))
      case App(fun, arg) =>
        val t1 = simple_(ctx, fun)
        val t2 = simple_(ctx, arg)
        t1 match {
          case Imp(`t2`, result) => result
          case All(x, matrix) => (matrix.subst(Map(x -> arg)))
          case _ =>  throw InferenceError("Don't know how to apply to a " + t1)
        }
      case _ =>
        throw InferenceError("Type inference for " + term + " is not yet implemented.")
    }
  def full(ctx: Ctx, term: Expr) = {
    val tvar = TypeVar()
    try {
      val eqs = solve(build(ctx, term, tvar) toList)
      val ty1 = eqs(tvar)
      Right(ty1.free.filter {
        case TypeVar(_) => true
        case _ => false
      }.foldLeft(ty1)((term: Expr, v: Id) => term.subst(Map(v -> Wildcard))))
    } catch {
      case InferenceError(err) => Left(err)
    }
  }

  def build(ctx: Ctx, term: Expr, tvar: Id): Map[Expr, Expr] = term match {
    case id: Id =>
      val t: Expr = tvar
      ctx get id map ((e: Expr) => Map(t -> e)) getOrElse
        (throw InferenceError(s"Not in current type inference context: $id"))
    case Pair(a, b) =>
      val ta = TypeVar()
      val tb = TypeVar()
      build(ctx, a, ta) ++ build(ctx, b, tb) + (tvar -> And(ta, tb))
      // TODO should I try to construct this as exists if what happens?
    case LeftE(a) =>
      val ta = TypeVar()
      val tb = TypeVar()
      build(ctx, a, ta) + (tvar -> Or(ta, tb))
    case RightE(b) =>
      val ta = TypeVar()
      val tb = TypeVar()
      build(ctx, b, tb) + (tvar -> Or(ta, tb))

    case Lam(List(Case(List(pat), body))) =>
      // this is let-polimorphism?
      val ta = TypeVar()
      val tb = TypeVar()
      val eqs1 = build(ctx, pat, ta)
      val eqs2 = build(ctx, pat, tb)
      //  eqs <- solve(eqs1 ++ eqs2 toList)
      //  ty = eqs(tvar)
      //  xs = ty.free.toList
      //  ts = xs map Expr.fresh

      //} yield eqs1 ++ eqs2 + (tvar -> All(ts, ty))
      eqs1 ++ eqs2 + (tvar -> Imp(ta, tb))

    case LamId(arg, body) =>
      val ta = TypeVar()
      val tb = TypeVar()
      val eqs1 = build(ctx, arg, ta)
      val eqs2 = build(ctx + (arg -> ta), body, tb)
      eqs1 ++ eqs2 + (tvar -> Imp(ta, tb))
      // forall free(p). p ==> e
    //case Lam(List(Case(List(arg), body))) =>
      //val ta = TypeVar()
      //val tb = TypeVar()
      //for {
      //  eqs1 <- build(ctx, arg, ta)
      //  // TODO here I need type inference for pattern matching:
      //  //                   v
      //  eqs2 <- build(ctx + (arg -> ta), body, tb)
      //} yield eqs2 => eqs1++eqs2+(tvar -> Imp(ta, tb))
      // TODO should I try to construct this as forall if ta is an Id?
    case App(fun, arg) =>
      val ta = TypeVar()
      val tb = TypeVar()
      val eqs1 = build(ctx, fun, tb)
      val eqs2 = build(ctx, arg, ta)
      eqs1 ++ eqs2 + (tb -> Imp(ta, tvar))
    case _ => throw InferenceError("Type inference for " + term + " is not yet implemented.")
  }

  /**
   * Generate a uifying substitution for a list of type equations
   */
  def solve(equations: List[(Expr, Expr)], subst: Ctx = Map()): Ctx =
    equations match {
      case Nil => subst
      case (a, b)::rest if a == b => solve(rest, subst)
      case (a@TypeVar(_), b)::rest if !b.free.contains(a.asInstanceOf[Id]) =>
        val a_ = a.asInstanceOf[Id]
        val update = Map(a_ -> b)
        val eqs = equations.map(eq => (eq._1 subst update, eq._2 subst update))
        val subst_ = subst.map((kv: (Id, Expr)) => if (a_ == kv._2) (kv._1 -> b) else kv) ++ update
        solve(eqs, subst_)
      case (a: Id, b@TypeVar(_))::rest => solve((b, a)::rest, subst)
      case (Imp(a, b), Imp(c, d))::rest => solve((a, c)::(b, d)::rest, subst)
      case (And(a, b), And(c, d))::rest => solve((a, c)::(b, d)::rest, subst)
      case (Or(a, b), Or(c, d))::rest => solve((a, c)::(b, d)::rest, subst)
      // FIXME do I need to compare the bound variable somehow?
      case (All(x, matrix1), All(y, matrix2))::rest => solve((matrix1, matrix2)::rest, subst)
      case (Ex(x, matrix1), Ex(y, matrix2))::rest => solve((matrix1, matrix2)::rest, subst)
      case _ => throw InferenceError("TODO")
    }

}
