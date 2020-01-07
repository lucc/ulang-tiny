package ulang

import arse._

sealed trait Pat extends Pretty {
  def bound: Set[Var]
  def rename(re: Map[Var, Var]): Pat
}

sealed trait Expr extends Expr.term with Pretty {
  def free: Set[Var]
}

object Expr extends Alpha[Expr, Var] {
}

sealed trait Id extends Expr with Pat {
  def name: String
  def fixity: Fixity
  def rename(re: Map[Var, Var]): Id
}

object Id {
  def unapply(id: Id) = id match {
    case Var(name, fixity, None) => Some((name, fixity))
    case Var(name, fixity, Some(index)) => Some((name + index, fixity))
    case Tag(name, fixity) => Some((name, fixity))
  }
}

sealed trait Val extends Pretty
sealed trait Norm extends Val
sealed trait Data extends Norm

case class Var(name: String, fixity: Fixity = Nilfix, index: Option[Int] = None) extends Id with Expr.x {
  def bound = Set(this)
  def fresh(index: Int) = Var(name, fixity, Some(index))
}

case class Tag(name: String, fixity: Fixity = Nilfix) extends Id with Data {
  def free = Set()
  def bound = Set()
  def rename(re: Map[Var, Var]) = this
  def subst(su: Map[Var, Expr]) = this
}

case object Wildcard extends Pat {
  def free = Set()
  def bound = Set()
  def rename(re: Map[Var, Var]) = this
}

case class Strict(pat: Pat) extends Pat {
  def bound = pat.bound
  def rename(re: Map[Var, Var]) = Strict(pat rename re)
}

case class UnApp(fun: Pat, arg: Pat) extends Pat {
  def bound = fun.bound ++ arg.bound
  def rename(re: Map[Var, Var]) = UnApp(fun rename re, arg rename re)
}

case class App(fun: Expr, arg: Expr) extends Expr {
  def free = fun.free ++ arg.free
  def rename(re: Map[Var, Var]) = App(fun rename re, arg rename re)
  def subst(su: Map[Var, Expr]) = App(fun subst su, arg subst su)
}

case class Ite(test: Expr, left: Expr, right: Expr) extends Expr {
  def free = test.free ++ left.free ++ right.free
  def rename(re: Map[Var, Var]) = Ite(test rename re, left rename re, right rename re)
  def subst(su: Map[Var, Expr]) = Ite(test subst su, left subst su, right subst su)
}

case class Case(pats: List[Pat], body: Expr) extends Expr.bind[Case] with Pretty {
  def arity = pats.length
  def free = body.free -- bound
  def bound = Set(pats flatMap (_.bound): _*)
  def rename(a: Map[Var, Var], re: Map[Var, Var]) = Case(pats map (_ rename a), body rename re)
  def subst(a: Map[Var, Var], su: Map[Var, Expr]) = Case(pats map (_ rename a), body subst su)
}

case class Lam(cases: List[Case]) extends Expr {
  def free = Set(cases flatMap (_.free): _*)
  def bound = Set(cases flatMap (_.bound): _*)
  def rename(re: Map[Var, Var]) = Lam(cases map (_ rename re))
  def subst(su: Map[Var, Expr]) = Lam(cases map (_ subst su))
}

case class Match(args: List[Expr], cases: List[Case]) extends Expr {
  def args_free = Set(args flatMap (_.free): _*)
  def cases_free = Set(cases flatMap (_.free): _*)
  def free = args_free ++ cases_free
  def rename(re: Map[Var, Var]) = Match(args map (_ rename re), cases map (_ rename re))
  def subst(su: Map[Var, Expr]) = Match(args map (_ subst su), cases map (_ subst su))
}

case class Bind(pat: Pat, arg: Expr) extends Pretty {
  def free = arg.free
  def bound = pat.bound
  def rename(a: Map[Var, Var], re: Map[Var, Var]) = Bind(pat rename a, arg rename re)
  def subst(a: Map[Var, Var], su: Map[Var, Expr]) = Bind(pat rename a, arg subst su)
}

case class Let(eqs: List[Bind], body: Expr) extends Expr with Expr.bind[Let] {
  def pats = eqs map (_.pat)
  val args = eqs map (_.arg)
  def bound = Set(eqs flatMap (_.bound): _*)
  def free = Set(eqs flatMap (_.free): _*) -- bound
  def rename(a: Map[Var, Var], re: Map[Var, Var]) = Let(eqs map (_ rename (a, re)), body rename re)
  def subst(a: Map[Var, Var], su: Map[Var, Expr]) = Let(eqs map (_ subst (a, su)), body subst su)
}

case class Obj(fun: Data, arg: Val) extends Data

case class Curry(cases: List[Case], rargs: List[Val], lex: Env) extends Norm {
  assert(!cases.isEmpty)
  assert(cases forall (_.arity == arity))
  assert(rargs.length <= arity)
  def isComplete = arity == rargs.length
  def arity = cases.head.arity
}

case class Defer(expr: Expr, lex: Env, eval: Eval) extends Val {
  override def toString = expr.toString
  lazy val norm = eval.norm(expr, lex)
}
