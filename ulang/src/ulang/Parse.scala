package ulang

import arse._
import arse.implicits._

object Parse {

  /**
   * Any whitespace separates tokens, two slashes start a "whitespace token"
   * that extends to the next newline, effectively implementing comments.
   */
  implicit object whitespace
    extends Whitespace("(\\s|(//.*\\n))*")

  def parens[A](p: Parser[A]) = "(" ~ p ~ ")"
  def bracks[A](p: Parser[A]) = "[" ~ p ~ "]"

  val keywords = Set(
    "define", "data", "notation", "eval", "test", "assume", "show", "proof",
    "inductive", "coinductive",
    ";", "(", ")", "{", "}", "[", "]", "->", "|", ":=",
    "if", "then", "else",
    "let", "in", "match", "with",
    "lambda", "exists", "forall")

  val s = S("""[^ \r\n\t\f()\[\].,;:\'\"]+""")
  /**
   * These special symbols do not need to be surrounded by whitespace in
   * order to be recognized as individual tokens.
   */
  val c = L(":=", "::", ":", "[]", ",")
  val n = s | c
  val name = n filterNot keywords
  // isMixfix depends on the current context!
  val name_nonmixfix = name filterNot context.isMixfix

  val apps = (name: String, args: List[Expr]) =>
    Apps(Id(name), args)

  def id = P(Id(name))
  val id_nonmixfix = P(Id(name_nonmixfix))

  val wild = Wildcard("_")

  val expr: Mixfix[String, Expr] = M(app, name, apps, context)
  val expr_arg: Parser[Expr] = P(parens(expr_open) | ite | let | lam | ex | all | mtch | wild | id_nonmixfix)
  val expr_open = expr | id

  val app = Apps(expr_arg ~ expr_arg.*)
  val ite = Ite("if" ~ expr ~ "then" ~ expr ~ "else" ~ expr)

  val eq = Case1(expr_arg ~ ":=" ~ expr)
  val eqs = eq ~+ ";"
  val let = Let("let" ~ eqs ~ "in" ~ expr)

  val cs = Case(expr_arg.+ ~ "->" ~ expr)
  val css = cs ~+ "|"
  val lam = Lam("lambda " ~ css)
  // val bind = Binder(id_bind ~ cs)

  val quant: Parser[List[Id] ~ Expr] = id.+ ~ "." ~ expr
  val ex: Parser[Expr] = Ex("exists" ~ quant)
  val all: Parser[Expr] = All("forall" ~ quant)

  val mtch = Match("match" ~ expr_arg.+ ~ "with" ~ css)

  val tactic: Parser[Tactic] = P(ind | coind | split | have | term)
  val ind = Induct("induction" ~ expr ~ ret(Least))
  val coind = Induct("induction" ~ expr ~ ret(Greatest))
  val split = Split("cases" ~ expr)
  val have = Have("have" ~ expr)
  val term = Term("term" ~ expr)

  // FIXME we need to ensure that there will be no arbitrary expression on the
  // left but only a function definition pattern.
  val df = Def(expr ~ ":=" ~ expr)

  /**
   * Generate a parser for a section from a parser for the individual
   * statements in the section.
   *
   * Each section will hold a list of statements (of type A).  The statements
   * are terminated by semicolons.  The section is started by a keyword.
   *
   * @param keyword the keyword from keywords above that starts this section
   * @param p a parser for an individual statement in the section (terminating
   * ";" is handled here and not in the p.
   */
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

  /**
   * The parser for data blocks has the side effect of storing the defined
   * data in the global context.  The mapped function is just the identity
   * with the intended side effect.
   */
  def data_declare = name.+ map {
    names =>
      context.data ++= names
      names
  }

  /**
   * The parser for notation blocks has the side effect of storing the defined
   * fixity in the global context.  The mapped function is just the identity
   * with the intended side effect.
   */
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
  val least = Ind(section("inductive", expr) ~ ret(Least))
  val greatest = Ind(section("coinductive", expr) ~ ret(Greatest))

  val proof = "proof" ~ tactic ~ ";"
  val thm = Thm(assume ~ show ~ proof.?) | Thm0(show ~ proof.?)

  val script = cmd.*
}
