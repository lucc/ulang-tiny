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
      // special case for lambdas with one pattern only
      case (Lam(List(Case(List(pat), body))), Imp(ant, cons)) =>
        check(bind(assumptions, pat, ant), body, cons)

      // propositional logic: elimination rules TODO
      // We could also introduce special term constructors that are recognized
      // here in order to eliminate connective: Elim-/\-1, Elim-/\-2, Elim-\/,
      // etc.

      // predicate logic introduction rules
      case (Pair(witness, p), Ex(id, matrix)) =>
        check(assumptions, p, matrix.subst(Map(id -> witness)))
      case (Lam1(param, body), All(id, matrix)) =>
        // For all-introduction there is a variable condition: the bound
        // variable must not occur free in any open assumption in body.
        val openFree = Expr free assumptions
        if (openFree contains id) Some("Capturing variable " + id)
        else check(assumptions, body, matrix.rename(Map(id -> param)))

      // TODO predicate logic elimination rules?

      // Special cases for modus ponens
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
      case (App(Lam1(id, body), arg), _) =>
        check(assumptions, body.subst(Map(id -> arg)), goal)
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

  /**
   * Type inference for the proof checker
   */
  def infer(ctx: Map[Id, Expr], expr: Expr): Either[String, Expr] = expr match {
    case id: Id => ctx get id toRight s"Not in current type inference context: $id"
    case Pair(a, b) => infer(ctx, a).flatMap(a => infer(ctx, b).map(b => And(a, b))) // TODO existential quantifier?
    case LeftE(a) => infer(ctx, a).map(a => Or(a, ulang.Wildcard))
    case RightE(a) => infer(ctx, a).map(a => Or(ulang.Wildcard, a))
    case Lam1(v, body) => infer(ctx, v).flatMap(t1 => infer(ctx + (v -> t1), body).map(t2 => Imp(t1, t2))) // TODO universal quantifier?
    case App(fun, arg) => infer(ctx, fun) match {
      case err@Left(_) => err
      case Right(t1) => infer(ctx, arg) match {
        case err@Left(_) => err
        case Right(t2) => t1 match {
          case Imp(`t2`, result) => Right(result)
          case All(x, matrix) => Right(matrix.subst(Map(x -> arg)))
          case _ => Left("Don't know how to apply to a " + t1)
        }
      }
    }
    case _ => Left("Type inference for " + expr + " is not yet implemented.")
  }

  def bind(ctx: Map[Id, Expr], pat: Expr, assm: Expr): Map[Id,Expr] =
    (pat, assm) match {
      case (p: Id, _) => ctx + (p -> assm)
      case (Pair(p1, p2), And(a1, a2)) => bind(bind(ctx, p1, a1), p2, a2)
      case (LeftE(p), Or(f, _)) => bind(ctx, p, f)
      case (RightE(p), Or(_, f)) => bind(ctx, p, f)
      case (Pair(w, p), Ex(x, matrix)) => bind(bind(ctx, w, x), p, matrix)
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
  //    case (Lam1(v, body), _) => body.subst(Map(v -> arg))
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

  /**
   * TypeVar represents type variables used during type inference.  It relies
   * on the fact that the parser for ulang does not accept space in
   * identidiers.  This ensures that the generated variables are distinct from
   * all user generated identidiers.
   */
  object TypeVar extends (() => Id) {
    private val name = "ty "
    def apply() = Expr.fresh(Id(name))
    def unapply(id: Expr) = id match {
      case Id(`name`, index) => index
      case _ => None
    }
  }

  def apply(ctx: Map[Id, Expr], term: Expr) = {
    val tvar = TypeVar()
    build(ctx, term, tvar) flatMap(eqs => solve(eqs toList) match {
      case Left(e) => Left(e)
      case Right(eqs) => Right(eqs(tvar))
    })
  }

  def build(ctx: Map[Id, Expr], term: Expr, tvar: Id): Either[String, Map[Expr, Expr]] = term match {
    case id: Id =>
      val t: Expr = tvar
      ctx get id map ((e: Expr) => Map(t -> e)) toRight s"Not in current type inference context: $id"
    case Pair(a, b) =>
      val ta = TypeVar()
      val tb = TypeVar()
      build(ctx, a, ta) flatMap (eqs1 => build(ctx, b, tb) map (eqs2 => eqs1++eqs2+(tvar -> And(ta, tb))))
      // TODO should I try to construct this as exists if what happens?
    case LeftE(a) =>
      val ta = TypeVar()
      val tb = TypeVar()
      build(ctx, a, ta) map (_ + (tvar -> Or(ta, tb)))
    case RightE(b) =>
      val ta = TypeVar()
      val tb = TypeVar()
      build(ctx, b, tb) map (_ + (tvar -> Or(ta, tb)))
    case Lam1(arg, body) =>
      val ta = TypeVar()
      val tb = TypeVar()
      build(ctx, arg, ta) flatMap (eqs1 => build(ctx + (arg -> ta), body, tb) map (eqs2 => eqs1++eqs2+(tvar -> Imp(ta, tb))))
    //case Lam(List(Case(List(arg), body))) =>
      //val ta = TypeVar()
      //val tb = TypeVar()
      // TODO here I need type inference for pattern matching:
      //                                                 v
      //build(ctx, arg, ta) flatMap (eqs1 => build(ctx + (arg -> ta), body, tb) map (eqs2 => eqs1++eqs2+(tvar -> Imp(ta, tb))))
      // TODO should I try to construct this as forall if ta is an Id?
    case App(fun, arg) =>
      val ta = TypeVar()
      val tb = TypeVar()
      build(ctx, fun, tb) flatMap (eqs1 => build(ctx, arg, ta) map (eqs2 => eqs1++eqs2+(tb -> Imp(ta, tvar))))
    case _ => Left("Type inference for " + term + " is not yet implemented.")
  }

  def solve(equations: List[(Expr, Expr)], subst: Map[Id, Expr] = Map()): Either[String, Map[Id, Expr]] =
    equations match {
      case Nil => Right(subst)
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
      case _ => Left("TODO")
    }

}
