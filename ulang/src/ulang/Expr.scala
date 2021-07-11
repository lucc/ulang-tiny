package ulang

sealed trait Expr extends Expr.term with Pretty {
  def free: Set[Id]

  def <=(that: Expr): Boolean = (this, that) match {
    case (_, Wildcard) =>
      true
    case (App(fun1, arg1), App(fun2, arg2)) =>
      fun1 <= fun2 && arg1 <= arg2
    case _ =>
      this == that
  }

  def replace(su: Map[Expr, Expr]): Expr = this match {
    case _ if su contains this =>
      su(this)
    case _: Id =>
      this
    case App(fun, arg) =>
      App(fun replace su, arg replace su)
    case Ite(test, left, right) =>
      Ite(test replace su, left replace su, right replace su)
    case expr@Lam(cases) =>
      Expr.avoiding(expr.bound, su) {
        (re, su) => Lam(cases map (_ replace (re, su)))
      }
    case expr@Let(eqs, body) =>
      Expr.avoiding(expr.bound, su) {
        (re, su) => Let(eqs map (_ replace (re, su)), body replace su)
      }
    case Match(args, cases) =>
      Match(args map (_ replace su), cases map {
        cs => Expr.avoiding(cs.bound, su)(cs.replace)
      })
    case expr@Bind(quant, arg, body) =>
      Expr.avoiding(expr.bound, su) {
        (re, su) => Bind(quant, arg rename re, body replace su)
      }
  }
}

object Expr extends Alpha[Expr, Id]

sealed trait Val extends Pretty
/** representing weak head normal form of Ulang terms */
sealed trait Norm extends Val
sealed trait Data extends Norm

case object Wildcard extends Expr {
  def free = Set()
  def rename(re: Map[Id, Id]) = this
  def subst(su: Map[Id, Expr]) = this
}

case class Id(name: String, index: Option[Int])
    extends Expr
    with Data
    with Expr.x {
  import context._
  def this(name: String) = this(name, None)
  def free = if (isTag(this) || isFun(this)) Set() else Set(this)
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
  def rename(re: Map[Id, Id]) =
    Ite(test rename re, left rename re, right rename re)
  def subst(su: Map[Id, Expr]) =
    Ite(test subst su, left subst su, right subst su)
}

case class Case(pats: List[Expr], body: Expr)
    extends Expr.bind[Case]
    with Pretty {
  def arity = pats.length
  def free = body.free -- bound
  def bound = pats.free
  def rename(a: Map[Id, Id], re: Map[Id, Id]) =
    Case(pats rename a, body rename re)
  def subst(a: Map[Id, Id], su: Map[Id, Expr]) =
    Case(pats rename a, body subst su)
  def replace(a: Map[Id, Id], su: Map[Expr, Expr]) =
    Case(pats rename a, body replace su)
}

case class Case1(pat: Expr, arg: Expr) extends Pretty {
  def free = arg.free
  def bound = pat.free
  def rename(a: Map[Id, Id], re: Map[Id, Id]) =
    Case1(pat rename a, arg rename re)
  def subst(a: Map[Id, Id], su: Map[Id, Expr]) =
    Case1(pat rename a, arg subst su)
  def replace(a: Map[Id, Id], su: Map[Expr, Expr]) =
    Case1(pat rename a, arg replace su)
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
  def rename(a: Map[Id, Id], re: Map[Id, Id]) =
    Let(eqs rename (a, re), body rename re)
  def subst(a: Map[Id, Id], su: Map[Id, Expr]) =
    Let(eqs subst (a, su), body subst su)
}

sealed trait Quant extends ((List[Id], Expr) => Expr) {
  def apply(args: List[Id], body: Expr): Expr =
    args.foldRight(body)(Bind(this, _, _))
  def apply(arg: Id, body: Expr) = Bind(this, arg, body)

  def unapply(expr: Expr) = expr match {
    case Bind(quant, arg, body) if quant == this =>
      Some((arg, body))
    case _ =>
      None
  }
}

case object Ex extends Quant
case object All extends Quant

case class Bind(quant: Quant, args: Id, body: Expr)
    extends Expr
    with Expr.bind[Bind] {
  def bound = Set(args)
  def free = body.free -- bound
  def rename(a: Map[Id, Id], re: Map[Id, Id]) =
    Bind(quant, args rename a, body rename re)
  def subst(a: Map[Id, Id], su: Map[Id, Expr]) =
    Bind(quant, args rename a, body subst su)
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
