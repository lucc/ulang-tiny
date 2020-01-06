package ulang

object Parser {
  import arse._
  import arse.implicits._

  implicit object whitespace
    extends Whitespace("(\\s|(//.*\\n))*")

  val name = S("[A-Za-z_][A-Za-z0-9_\\-]*")

  val keywords = Set(
    "define", "data", "notation", "assume", "show", "proof",
    "if", "then", "else")


  val expr: Parser[Expr] = ???

  val id = Id(name filterNot keywords)
  val app = P(Apps(expr.+))
}