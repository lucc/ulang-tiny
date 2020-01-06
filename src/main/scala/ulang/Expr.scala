package ulang

sealed trait Pat {
  def bound: Set[Id]
  def rename(re: Map[Id, Id]): Pat
}

sealed trait Expr extends Expr.term {
  def free: Set[Id]
}

object Expr extends Alpha[Expr, Id] {

}

sealed trait Val
sealed trait Norm extends Val
sealed trait Data extends Norm

case class Id(name: String, index: Option[Int]) extends Expr with Pat with Expr.x {
  def bound = Set(this)
  def fresh(index: Int) = Id(name, Some(index))
}

object Id extends (String => Id) {
  def apply(name: String): Id = {
    Id(name, None)
  }
}

case class Tag(name: String) extends Expr with Pat with Data {
  def free = Set()
  def bound = Set()
  def rename(re: Map[Id, Id]) = this
  def subst(su: Map[Id, Expr]) = this
}

case object Wildcard extends Pat {
  def free = Set()
  def bound = Set()
  def rename(re: Map[Id, Id]) = this
}

case class Strict(pat: Pat) extends Pat {
  def bound = pat.bound
  def rename(re: Map[Id, Id]) = Strict(pat rename re)
}

case class UnApp(fun: Pat, arg: Pat) extends Pat {
  def bound = fun.bound ++ arg.bound
  def rename(re: Map[Id, Id]) = UnApp(fun rename re, arg rename re)
}

case class App(fun: Expr, arg: Expr) extends Expr {
  def free = fun.free ++ arg.free
  def rename(re: Map[Id, Id]) = App(fun rename re, arg rename re)
  def subst(su: Map[Id, Expr]) = App(fun subst su, arg subst su)
}

object Apps extends (List[Expr] => Expr) {
  def apply(exprs: List[Expr]): Expr = exprs match {
    case expr :: Nil => expr
    case fun :: args => args.foldLeft(fun)(App)
  }
}

case class Case(pats: List[Pat], body: Expr) extends Expr.bind[Case] {
  def arity = pats.length
  def free = body.free -- bound
  def bound = Set(pats flatMap (_.bound): _*)
  def rename(a: Map[Id, Id], re: Map[Id, Id]) = Case(pats map (_ rename a), body rename re)
  def subst(a: Map[Id, Id], su: Map[Id, Expr]) = Case(pats map (_ rename a), body subst su)
}

case class Lam(cases: List[Case]) extends Expr {
  def free = Set(cases flatMap (_.free): _*)
  def bound = Set(cases flatMap (_.bound): _*)
  def rename(re: Map[Id, Id]) = Lam(cases map (_ rename re))
  def subst(su: Map[Id, Expr]) = Lam(cases map (_ subst su))
}

case class Match(expr: Expr, cases: List[Case]) extends Expr {
  def free = expr.free ++ (cases flatMap (_.free))
  def rename(re: Map[Id, Id]) = Match(expr rename re, cases map (_ rename re))
  def subst(su: Map[Id, Expr]) = Match(expr subst su, cases map (_ subst su))
}

case class Eq(x: Id, e: Expr) {
  def free = e.free
  def rename(a: Map[Id, Id], re: Map[Id, Id]) = Eq(x rename a, e rename re)
  def subst(a: Map[Id, Id], su: Map[Id, Expr]) = Eq(x rename a, e subst su)
}

case class Let(eqs: List[Eq], body: Expr) extends Expr with Expr.bind[Let] {
  def bound = Set(eqs map (_.x): _*)
  def free = Set(eqs flatMap (_.free): _*) -- bound
  def rename(a: Map[Id, Id], re: Map[Id, Id]) = Let(eqs map (_ rename (a, re)), body rename re)
  def subst(a: Map[Id, Id], su: Map[Id, Expr]) = Let(eqs map (_ subst (a, su)), body subst su)
}

case class Obj(fun: Data, arg: Val) extends Data

case class Curry(cases: List[Case], rargs: List[Val], lex: Env) extends Norm {
  assert(!cases.isEmpty)
  assert(cases forall (_.arity == arity))
  assert(rargs.length <= arity)
  def isComplete = arity == rargs.length
  def arity = cases.head.arity
}

case class Defer(expr: Expr, lex: Env) extends Val {
  lazy val norm = Eval.norm(expr, lex)
}
