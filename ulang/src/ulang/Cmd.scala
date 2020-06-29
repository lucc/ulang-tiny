package ulang

import arse.Fixity

sealed trait Cmd extends Pretty {

}

case class Def(expr: Expr, attr: List[String])
case class Defs(defs: List[Def]) extends Cmd

case class Datas(names: List[String]) extends Cmd
case class Notation(fixs: List[(List[String], Fixity)]) extends Cmd

case class Tests(tests: List[Expr]) extends Cmd
case class Evals(exprs: List[Expr]) extends Cmd

// DUMMY
sealed trait Intro

/* case class Intro(pre: List[Expr], post: Expr) {
  def free = pre.free ++ post.free
  def rename(re: Map[Var, Var]) = Intro(pre rename re, post rename re)
  def subst(su: Map[Var, Expr]) = Intro(pre subst su, post subst su)
}

object Intro extends (Expr => Intro) {
  def apply(expr: Expr): Intro = expr match {
    case Imp(Apps(And.op, ant), suc) =>
      Intro(ant, suc)
    case Imp(ant, suc) =>
      Intro(List(ant), suc)
    case suc =>
      Intro(Nil, suc)
  }
} */

sealed trait Fix
case object Least extends Fix
case object Greatest extends Fix

case class Intros(cases: List[Expr], kind: Fix) extends Cmd {
  def pat: Expr = {
    ???
  }
}

case class Thm(assume: List[Expr], show: Expr, proof: Option[Tactic]) extends Cmd

object Thm0 extends ((Expr, Option[Tactic]) => Thm) {
  def apply(show: Expr, proof: Option[Tactic]) = Thm(Nil, show, proof)
}