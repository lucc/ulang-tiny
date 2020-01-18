package ulang

import arse.Fixity

sealed trait Cmd extends Pretty {

}

case class Def(fun: Var, args: List[Pat], body: Expr, attr: List[String])

object Def extends ((Pat, Expr, List[String]) => Def) {
  def apply(lhs: Pat, rhs: Expr, attr: List[String]) = lhs match {
    case id: Var => Def(id, Nil, rhs, attr)
    case UnApps(id: Var, args) => Def(id, args, rhs, attr)
    case _ => sys.error("invalid definition: " + lhs + " == ...")
  }
}

case class Defs(defs: List[Def]) extends Cmd

case class Datas(names: List[String]) extends Cmd
case class Notation(fixs: List[(List[String], Fixity)]) extends Cmd
// case class Tests(tests: List[Test]) extends Cmd
case class Evals(exprs: List[Expr]) extends Cmd

sealed trait FixKind
case object Least extends FixKind
case object Greatest extends FixKind
case class Fix(cases: List[Expr], kind: FixKind) extends Cmd

case class Thm(assume: List[Expr], show: Expr, proof: Option[Tactic]) extends Cmd

object Thm0 extends ((Expr, Option[Tactic]) => Thm) {
  def apply(show: Expr, proof: Option[Tactic]) = Thm(Nil, show, proof)
}