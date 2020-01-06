package ulang

object Parser {
  import arse._
  import arse.implicits._

  object operators extends Syntax[Id] {
    var data: Set[Id] = Set()
    var prefix_ops: Map[Id, Int] = Map()
    var postfix_ops: Map[Id, Int] = Map()
    var infix_ops: Map[Id, (Assoc, Int)] = Map()
    var bind_ops: Set[Id] = Set()

    def isMixfix(id: Id): Boolean = {
      contains(id) || isBind(id)
    }

    def isBind(id: Id) = {
      bind_ops contains id
    }
  }

  implicit object whitespace
    extends Whitespace("(\\s|(//.*\\n))*")

  def parens[A](p: Parser[A]) = {
    "(" ~ p ~ ")"
  }

  val name = S("""[^ \r\n\t\f()\[\],;\'\"]+""")

  val keywords = Set(
    "define", "data", "notation", "assume", "show", "proof",
    ",", ";", "(", ")", "{", "}", "[", "]", "->",  "|", "\\", "_",
    "if", "then", "else",
    "let", "in")

  val id = Id(name filterNot keywords)
  val id_nonmixfix = id filterNot operators.isMixfix
  val id_bind = id filter operators.isBind

  val pat: Mixfix[Id, Pat] = M(unapp, id, UnApps, operators)
  val pat_arg: Parser[Pat] = P(parens(pat_open) | wildcard | strict | id_nonmixfix)
  val pat_open = pat | id

  val expr: Mixfix[Id, Expr] = M(app, id, Apps, operators)
  val expr_arg: Parser[Expr] = P(parens(expr_open) | ite | let | lam | bind | id_nonmixfix)
  val expr_open = expr | id

  val wildcard = Wildcard("_")
  val unapp = UnApps(pat ~ pat.*)
  val strict = Strict("!" ~ pat_arg)

  val app = Apps(expr ~ expr.*)
  val ite = Ite("if" ~ expr ~ "then" ~ expr ~ "else" ~ expr)

  val eq = Bind(pat_arg ~ "=" ~ expr)
  val eqs = eq ~+ ","
  val let = Let("let" ~ eqs ~ "in" ~ expr)

  val cs = Case(pat_arg.+ ~ "->" ~ expr)
  val css = cs ~+ "|"
  val lam = Lam("\\" ~ css)
  val bind = Binder(id_bind ~ cs)

}