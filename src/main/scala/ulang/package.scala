import scala.language.implicitConversions

package object ulang {
  type Env = Map[Id, Val]
  var dyn: Env = Map()

  def backtrack = {
    throw Backtrack
  }

  implicit class Control[A](first: => A) {
    def or[B <: A](second: => B) = {
      try {
        first
      } catch {
        case Backtrack =>
          second
      }
    }
  }

  case object Backtrack extends Throwable {
    override def fillInStackTrace = this
    override val getStackTrace = Array[StackTraceElement]()
  }

  sealed trait Pat
  sealed trait Expr
  sealed trait Val
  sealed trait Norm extends Val

  case class Id(name: String) extends Expr with Pat
  case class Tag(name: String) extends Norm with Pat

  case object Wildcard extends Pat
  case class UnApp(tag: Tag, args: List[Pat]) extends Pat

  case class App(fun: Expr, args: List[Expr]) extends Expr
  case class Case(pats: List[Pat], body: Expr)
  case class Lam(cases: List[Case]) extends Expr

  case class Obj(tag: Tag, args: List[Val]) extends Norm
  case class Fun(cases: List[Case], lex: Env) extends Norm
  case class Lazy(expr: Expr, lex: Env) extends Val {
    lazy val norm = eval(expr, lex)
  }

  def equal(v1: Val, v2: Val): Boolean = {
    const(v1) == const(v2)
  }

  def bind(pat: Pat, arg: Val, env: Env): Env = pat match {
    case Wildcard => env
    case id: Id if env contains id =>
      if (equal(env(id), arg)) env
      else backtrack
    case id: Id => env + (id -> arg)
    case UnApp(tag, pats) =>
      norm(arg) match {
        case Obj(`tag`, args) => bind(pats, args, env)
        case _ => backtrack
      }
    case _ => backtrack
  }

  def bind(pats: List[Pat], args: List[Val], env: Env): Env = (pats, args) match {
    case (Nil, Nil) => env
    case (pat :: pats, arg :: args) => bind(pats, args, bind(pat, arg, env))
    case _ => sys.error("argument length mismatch: " + pats.mkString(" ") + " and " + args.mkString(" "))
  }

  def apply(cs: Case, args: List[Val], lex: Env): Norm = cs match {
    case Case(pats, body) =>
      eval(body, bind(pats, args, lex))
  }

  def apply(fun: Norm, cases: List[Case], args: List[Val], lex: Env): Norm = cases match {
    case Nil =>
      sys.error("cannot apply " + fun + " to " + args.mkString(" "))
    case cs :: rest =>
      { apply(cs, args, lex) } or { apply(fun, rest, args, lex) }
  }

  def apply(fun: Norm, args: List[Val]): Norm = fun match {
    case tag: Tag => Obj(tag, args)
    case Fun(cases, lex) => apply(fun, cases, args, lex)
    case _ => sys.error("not a function: " + fun)
  }

  def norm(arg: Val): Norm = arg match {
    case lzy: Lazy => lzy.norm
    case arg: Norm => arg
  }

  def defer(expr: Expr, lex: Env): Val = {
    Lazy(expr, lex)
  }

  def const(arg: Val): Norm = arg match {
    case lzy: Lazy => const(lzy.norm)
    case tag: Tag => tag
    case Obj(tag, args) => Obj(tag, args map const)
    case _ => sys.error("not constant: " + arg)
  }

  def eval(expr: Expr, lex: Env): Norm = expr match {
    case id: Id if lex contains id => norm(lex(id))
    case id: Id if dyn contains id => norm(dyn(id))
    case id: Id => sys.error("unbound variable: " + id + " in " + lex + " and " + dyn)
    case Lam(cases) => Fun(cases, lex)
    case App(fun, args) => apply(eval(fun, lex), args map (defer(_, lex)))
  }
}