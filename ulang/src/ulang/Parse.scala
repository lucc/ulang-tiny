package ulang

import arse._
import arse.implicits._

object Parse {
  import context._

  implicit object whitespace
    extends Whitespace("(\\s|(//.*\\n))*")

  def parens[A](p: Parser[A]) = "(" ~ p ~ ")"
  def bracks[A](p: Parser[A]) = "[" ~ p ~ "]"

  val keywords = Set(
    "define", "data", "notation", "eval", "test", "assume", "show", "proof", "inductive", "coinductive",
    ",", ";", "(", ")", "{", "}", "[", "]", "->", "|",
    "if", "then", "else",
    "let", "in", "match", "with",
    "lambda", "exists", "forall")

  val s = S("""[^ \r\n\t\f()\[\],;:\'\"]+""")
  val c = L("::", ":", "[]")
  val n = s | c
  val name = n filterNot keywords
  val name_nonmixfix = name filterNot isMixfix

  val apps = (name: String, args: List[Expr]) =>
    Apps(Id(name), args)

  def id = P(Id(name))
  val id_nonmixfix = P(Id(name_nonmixfix))

  val expr: Mixfix[String, Expr] = M(app, name, apps, context)
  val expr_arg: Parser[Expr] = P(parens(expr_open) | ite | let | lam | ex | all | mtch | id_nonmixfix)
  val expr_open = expr | id

  val app = Apps(expr_arg ~ expr_arg.*)
  val ite = Ite("if" ~ expr ~ "then" ~ expr ~ "else" ~ expr)

  val eq = Case1(expr_arg ~ "=" ~ expr)
  val eqs = eq ~+ ","
  val let = Let("let" ~ eqs ~ "in" ~ expr)

  val cs = Case(expr_arg.+ ~ "->" ~ expr)
  val css = cs ~+ "|"
  val lam = Lam("lambda " ~ css)
  // val bind = Binder(id_bind ~ cs)

  val quant = id.+ ~ "->" ~ expr
  val ex = Ex("exists" ~ quant)
  val all = All("forall" ~ quant)

  val mtch = Match("match" ~ expr_arg.+ ~ "with" ~ css)

  val tactic: Parser[Tactic] = P(ind | coind | split | have)
  val ind = Ind("induction" ~ expr ~ ret(Least))
  val coind = Ind("induction" ~ expr ~ ret(Greatest))
  val split = Split("cases" ~ expr)
  val have = Have("have" ~ expr)

  val attr = L("rewrite")
  val attrs = bracks(attr.*) | ret(Nil)
  val df = Def(expr ~ attrs)

  def section[A](keyword: String, p: Parser[A]): Parser[List[A]] = {
    keyword ~ (p ~ ";").*
  }

  val assoc = Left("infixl") | Right("infixr") | Non("infix")
  val prefix = Prefix("prefix" ~ int)
  val postfix = Postfix("postfix" ~ int)
  val infix = Infix(assoc ~ int)

  val fixity: Parser[Fixity] = prefix | postfix | infix
  def fix = name.+ ~ bracks(fixity)

  val assume = section("assume", expr)
  val show = "show" ~ expr ~ ";"

  def data_declare = name.+ map {
    names =>
      data ++= names
      names
  }

  val notation_declare = fix map {
    case (names, fixity) =>
      context notation (names, fixity)
      (names, fixity)
  }

  val cmd: Parser[Cmd] = P(defs | evals | tests | datas | notation | thm | least | greatest)

  val defs = Defs(section("define", df))
  val evals = Evals(section("eval", expr))
  val tests = Tests(section("test", expr))
  val datas = Datas(section("data", data_declare) map (_.flatten))
  val notation = Notation(section("notation", notation_declare))
  val least = Intros(section("inductive", expr) ~ ret(Least))
  val greatest = Intros(section("coinductive", expr) ~ ret(Greatest))

  val proof = "proof" ~ tactic ~ ";"
  val thm = Thm(assume ~ show ~ proof.?) | Thm0(show ~ proof.?)

  val script = cmd.*
}