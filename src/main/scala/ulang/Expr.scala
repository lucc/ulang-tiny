package ulang

sealed trait Pat
sealed trait Expr
sealed trait Val
sealed trait Norm extends Val
sealed trait Data extends Norm

case class Id(name: String) extends Expr with Pat
case class Tag(name: String) extends Expr with Pat with Data

case object Wildcard extends Pat
case class Strict(pat: Pat) extends Pat
case class UnApp(fun: Pat, arg: Pat) extends Pat

case class App(fun: Expr, arg: Expr) extends Expr

case class Case(pats: List[Pat], body: Expr) {
  def arity = pats.length
}
case class Lam(cases: List[Case]) extends Expr

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
