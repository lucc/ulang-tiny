package ulang

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
        else throw InferenceError(s"Not in current type inference context: $id")
      case Pair(a, b) =>
        And(simple_(ctx, a), simple_(ctx, b))
      case LeftE(a) =>
        Or(simple_(ctx, a), ulang.Wildcard)
      case RightE(a) =>
        Or(ulang.Wildcard, simple_(ctx, a))
      case Witness(x, w, p) =>
        throw  InferenceError("Can not yet infer existential types.")
      //case Witness(x, w, p) =>
      //  val ty = simple_(ctx, p)
      //  Ex(x, ty.subst(Map(w -> x)))
      case Inst(pt, t, pt2) =>
        val All(x, phi) = simple_(ctx, pt)
        val Imp(ant, cons) = simple_(ctx, pt2)
        if (phi.subst(Map(x -> t)) equals ant) cons
        else throw InferenceError("Type mismatch in Inst expression.")
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
