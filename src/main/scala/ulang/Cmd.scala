package ulang

import arse.Fixity

sealed trait Cmd {

}

case class Def(fun: Var, args: List[Pat], body: Expr)

object Def extends ((Pat, Expr) => Def) {
  def apply(lhs: Pat, rhs: Expr) = lhs match {
    case id: Var => Def(id, Nil, rhs)
    case UnApps(id: Var, args) => Def(id, args, rhs)
  }
}

case class Defs(defs: List[Def]) extends Cmd

case class Datas(names: List[String]) extends Cmd
case class Notation(fixs: List[(List[String], Fixity)]) extends Cmd
// case class Tests(tests: List[Test]) extends Cmd
case class Evals(exprs: List[Expr]) extends Cmd
// case class Thms(props: List[Thm]) extends Cmd
// case class Ind(cases: List[Expr]) extends Cmd

case class Thm(assume: List[Expr], show: Expr) extends Cmd

object Thm0 extends (Expr => Thm) {
  def apply(show: Expr) = Thm(Nil, show)
}