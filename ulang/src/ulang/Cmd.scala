package ulang

import arse.Fixity

sealed trait Cmd extends Pretty {

}

case class Def(expr: Expr)
case class Defs(defs: List[Def]) extends Cmd

case class Datas(names: List[String]) extends Cmd
case class Notation(fixs: List[(List[String], Fixity)]) extends Cmd

case class Tests(tests: List[Expr]) extends Cmd
case class Evals(exprs: List[Expr]) extends Cmd

sealed trait Fix
case object Least extends Fix
case object Greatest extends Fix

case class Ind(cases: List[Expr], kind: Fix) extends Cmd
case class Thm(assume: List[Expr], show: Expr, proof: Option[Tactic]) extends Cmd

object Thm0 extends ((Expr, Option[Tactic]) => Thm) {
  def apply(show: Expr, proof: Option[Tactic]) = Thm(Nil, show, proof)
}
