package ulang

import arse.Fixity

sealed trait Cmd /* extends Pretty */ {

}

case class Def(fun: Var, args: List[Pat], body: Expr, attr: List[String])

object Def extends ((Pat, Expr, List[String]) => Def) {
  def apply(lhs: Pat, rhs: Expr, attr: List[String]) = lhs match {
    case id: Var => Def(id, Nil, rhs, attr)
    case UnApps(id: Var, args) => Def(id, args, rhs, attr)
  }
}

case class Defs(defs: List[Def]) extends Cmd

case class Datas(names: List[String]) extends Cmd
case class Notation(fixs: List[(List[String], Fixity)]) extends Cmd
// case class Tests(tests: List[Test]) extends Cmd
case class Evals(exprs: List[Expr]) extends Cmd
case class Ind(cases: List[Expr]) extends Cmd

case class Thm(assume: List[Expr], show: Expr) extends Cmd

object Thm0 extends (Expr => Thm) {
  def apply(show: Expr) = Thm(Nil, show)
}