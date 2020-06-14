package ulang

import arse._

sealed trait Expr extends Expr.term with Pretty {
  def free: Set[Var]
}

object Expr extends Alpha[Expr, Var] {
}

sealed trait Id extends Expr {
  def name: String
  def fixity: Fixity
  def rename(re: Map[Var, Var]): Id
}

object Id {
  def unapply(id: Id) = id match {
    case Var(name, fixity, None) => Some((name, fixity))
    case Var(name, fixity, Some(index)) => Some((name __ index, fixity))
    case Fun(name, fixity) => Some((name, fixity))
    case Tag(name, fixity) => Some((name, fixity))
  }
}

sealed trait Val extends Pretty
sealed trait Norm extends Val
sealed trait Data extends Norm

case class Raw(name: String) extends Expr {
  def free = Set()
  def rename(re: Map[Var, Var]) = this
  def subst(su: Map[Var, Expr]) = this
}

case object Wildcard extends Expr {
  def free = Set()
  def rename(re: Map[Var, Var]) = this
  def subst(su: Map[Var, Expr]) = this
}

case class Var(name: String, fixity: Fixity = Nilfix, index: Option[Int] = None) extends Id with Expr.x {
  def fresh(index: Int) = Var(name, fixity, Some(index))
}

object Var extends (String => Var) {
  def apply(name: String): Var = {
    Var(name, Nilfix, None)
  }
}

case class Fun(name: String, fixity: Fixity = Nilfix) extends Id {
  def free = Set()
  def rename(re: Map[Var, Var]) = this
  def subst(su: Map[Var, Expr]) = this
}

case class Tag(name: String, fixity: Fixity = Nilfix) extends Id with Data {
  def free = Set()
  def rename(re: Map[Var, Var]) = this
  def subst(su: Map[Var, Expr]) = this
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

case class Case(pats: List[Expr], body: Expr) extends Expr.bind[Case] with Pretty {
  def arity = pats.length
  def free = body.free -- bound
  def bound = pats.free
  def rename(a: Map[Var, Var], re: Map[Var, Var]) = Case(pats rename a, body rename re)
  def subst(a: Map[Var, Var], su: Map[Var, Expr]) = Case(pats rename a, body subst su)
}

case class Case1(pat: Expr, arg: Expr) extends Pretty {
  def free = arg.free
  def bound = pat.free
  def rename(a: Map[Var, Var], re: Map[Var, Var]) = Case1(pat rename a, arg rename re)
  def subst(a: Map[Var, Var], su: Map[Var, Expr]) = Case1(pat rename a, arg subst su)
}

case class Lam(cases: List[Case]) extends Expr {
  def free = cases.free
  def bound = cases.bound
  def rename(re: Map[Var, Var]) = Lam(cases rename re)
  def subst(su: Map[Var, Expr]) = Lam(cases subst su)
}

case class Match(args: List[Expr], cases: List[Case]) extends Expr {
  def free = args.free ++ cases.free
  def rename(re: Map[Var, Var]) = Match(args rename re, cases rename re)
  def subst(su: Map[Var, Expr]) = Match(args subst su, cases subst su)
}

case class Let(eqs: List[Case1], body: Expr) extends Expr with Expr.bind[Let] {
  def pats = eqs.pats
  def args = eqs.args
  def bound = eqs.bound
  def free = eqs.free -- bound
  def rename(a: Map[Var, Var], re: Map[Var, Var]) = Let(eqs rename (a, re), body rename re)
  def subst(a: Map[Var, Var], su: Map[Var, Expr]) = Let(eqs subst (a, su), body subst su)
}

sealed trait Quant extends ((List[Var], Expr) => Expr) {
  def apply(args: List[Var], body: Expr) = args match {
    case Nil => body
    case _ => Bind(this, args, body)
  }

  def unapply(expr: Expr) = expr match {
    case Bind(quant, args, body) if quant == this =>
      Some((args, body))
    case _ =>
      None
  }
}

case object Ex extends Quant
case object All extends Quant

case class Bind(quant: Quant, args: List[Var], body: Expr) extends Expr with Expr.bind[Bind] {
  def bound = args.toSet
  def free = body.free -- bound
  def rename(a: Map[Var, Var], re: Map[Var, Var]) = Bind(quant, args rename a, body rename re)
  def subst(a: Map[Var, Var], su: Map[Var, Expr]) = Bind(quant, args rename a, body subst su)
}

case class Obj(fun: Data, arg: Val) extends Data

case class Curry(cases: List[Case], rargs: List[Val], lex: Env) extends Norm {
  assert(cases.nonEmpty)
  assert(cases forall (_.arity == arity))
  assert(rargs.length <= arity)
  def isComplete = arity == rargs.length
  def arity = cases.head.arity
}

case class Defer(expr: Expr, lex: Env, eval: Eval) extends Val {
  override def toString = expr.toString
  lazy val norm = eval.norm(expr, lex)
}
