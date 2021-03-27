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
  def check(ctx: Map[Id, Expr], proof: Expr, goal: Expr): Option[String] =
    (proof, goal) match {

      // Proof by assumption has to be the first case, this makes it possible
      // to match against any goal (even "False").  If the given goal is not
      // in the context we fall through to the other cases.
      case (id: Id, _) if ctx contains id =>
        if (ctx(id) == goal) None
        else Some(f"Assumption $id does not match the goal $goal")
      case (id: Id, _) if context.lemmas contains id =>
        if (context.lemmas(id) == goal) None
        else Some(f"Lemma $id does not match the goal $goal")
      case (id: Id, _) if context.funs contains id =>
        check(ctx, Lam(context.funs(id)), goal)
      case (Id("elim", None), _) =>
        Some("The special function name 'elim' can only be used in applications.")
      case (Id("intro", None), _) =>
        Some("The special function name 'intro' can only be used in applications.")

      // special cases
      case (True, True) => None // we use "True" to represent a trivial proof
      case (intro(pred, index), _) => Some("Generation of intro axioms is not yet implemented")
      case (elim(pred), _) => Some("Generation of elim axioms is not yet implemented")

      // propositional logic: introduction rules
      case (Pair(p1, p2), And(f1, f2)) =>
        check(ctx, p1, f1) orElse check(ctx, p2, f2)
      case (LeftE(p), Or(f, _)) => check(ctx, p, f)
      case (RightE(p), Or(_, f)) => check(ctx, p, f)
      // special case for lambdas with one pattern only
      case (Lam1(List(pat), body), Imp(ant, cons)) =>
        check(bind(ctx, pat, ant), body, cons)

      // predicate logic introduction rules
      case (Witness(witness, p), Ex(id, matrix)) =>
        check(ctx, p, matrix.subst(Map(id -> witness)))
      case (All(param, body), All(id, matrix)) =>
        // For all-introduction there is a variable condition: the bound
        // variable must not occur free in any open assumption in body.
        val openFree = Expr free ctx
        if (openFree contains id) Some("Capturing variable " + id)
        else check(ctx, body, matrix.rename(Map(id -> param)))

      // TODO predicate logic elimination rules?

      case (App(All(x, body), arg), _) if body.subst(Map(x -> arg)) == goal =>
        None
      // different cases for modus ponens
      case (App(LamId(id, body), arg), _) =>
        check(ctx, body.subst(Map(id -> arg)), goal)
      // This must have more than one Id because of previous case
      case (App(LamIds(id::ids, body), arg), _) =>
        check(ctx, LamIds(ids, body).subst(Map(id -> arg)), goal)
      case (App(Lam1(pat, body), arg), _) =>
        infer(ctx, arg) match {
          case Left(err) => Some(err)
          case Right(t) =>
            pat match {
              case Nil => Some("This should never happen")
              case List(p) => check(ctx, apply(p, arg, body), goal)
              case p::ps => check(ctx, apply(p, arg, Lam1(ps, body)), goal)
            }
        }
      case (App(Lam(cases), arg), _) =>
        infer(ctx, arg) match {
          case Left(err) => Some(err)
          case Right(t) =>
            val proofs = apply(cases, arg)
            val ctxs = bind(ctx, cases, t)
            ctxs.zip(proofs).map { case (c, p) => check(c, p, goal)
            }.foldLeft( None: Option[String])((a,o) => a orElse o)
        }

      case (App(f: Id, arg), _) if ctx.contains(f) || context.lemmas.contains(f) =>
        val t1 = ctx.getOrElse(f, context.lemmas(f))
        t1 match {
          case All(x, matrix) if matrix.subst(Map(x -> arg)) == goal => None
          case _ =>
            infer(ctx, arg) match {
              case Left(err) => Some(err)
              case Right(t2) =>
                if (t1 == Imp(t2, goal)) None
                else if (t2.isInstanceOf[Id] && t1 == All(t2.asInstanceOf[Id], goal)) None
                else Some(f"Formulas do not match: $t1 should be equal to $t2 ==> $goal or forall $t2. $goal")
            }
        }

      case (App(f: Id, arg), _) if context.funs contains f =>
        // defined functions are checked like lambda terms
        check(ctx, App(Lam(context.funs(f)), arg), goal)

      // general applications need type inference for either the left or the
      // right side.  We use the left side for now.
      case (App(f, arg), _) =>
        infer(ctx, arg) match {
          case Right(ty) if check(ctx, f, Imp(ty, goal)).isEmpty => None
          case Right(ty: Id) => check(ctx, f, All(ty, goal))
          case Left(err1) =>
            infer(ctx, f) match {
              case Right(Imp(a, `goal`)) => check(ctx, a, arg)
              case Right(All(v, matrix)) if matrix.subst(Map(v -> arg)) == goal => None
              case Left(err2) => Some(err1 + "\n" + err2)
            }
        }

      // match expressions can be converted to function applications
      case (Match(args, cases), _) =>
        check(ctx, Apps(Lam(cases), args), goal)

      // False is implicit here
      case _ => Some(f"Proof term $proof does not match the formula $goal.")
    }

  val infer = TypeInference(_, _)

  /**
   * extend a context by binding argument types to parameter variables
   */
  def bind(ctx: Map[Id, Expr], pat: Expr, assm: Expr): Map[Id,Expr] =
    (pat, assm) match {
      case (p: Id, _) => ctx + (p -> assm)
      case (Pair(p1, p2), And(a1, a2)) => bind(bind(ctx, p1, a1), p2, a2)
      case (LeftE(p), Or(f, _)) => bind(ctx, p, f)
      case (RightE(p), Or(_, f)) => bind(ctx, p, f)
      case (Witness(w, p), Ex(x, matrix)) => bind(bind(ctx, w, x), p, matrix.subst(Map(x -> w)))
    }
  def bind(ctx: Map[Id, Expr], cases: List[Case], assm: Expr): List[Map[Id, Expr]] =
    cases.map(c => bind(ctx, c.pats.head, assm))
  /**
   * Bind an argument term to a pattern
   */
  def apply(pat: Expr, arg: Expr, body: Expr): Expr =
    (pat, arg) match {
      case (p: Id, _) => body.subst(Map(p -> arg))
      case (App(id1: Id, term1), App(id2: Id, term2))
        if context.isTag(id1) && id1 == id2 => apply(term1, term2, body)
      case (App(f1, a1), App(f2, a2)) => apply(a1, a2, apply(f1, f2, body))
    }
  def apply(cases: List[Case], arg: Expr): List[Expr] =

    cases.map {
      case Case(List(p), body) => apply(p, arg, body)
      case Case(p::ps, body) => apply(p, arg, Lam1(ps, body))
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
        if (ctx contains id) ctx(id)
        else if (context.lemmas contains id) context.lemmas(id)
        // defined functions are hard infer because they can be recursive
        else throw InferenceError( s"Not in current type inference context: $id")
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
        t1 match {
          case Imp(cond, result) if cond == simple_(ctx, arg) => result
          case All(x, matrix) => (matrix.subst(Map(x -> arg)))
          case _ =>  throw InferenceError("Don't know how to apply to a " + t1)
        }
      case All(x, body) =>
        All(x, simple_(ctx + (x -> Wildcard), body))
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
