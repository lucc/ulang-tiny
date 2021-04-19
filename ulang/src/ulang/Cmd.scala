package ulang

import arse.Fixity

/**
 * The syntactical top level elements for an ulang source file.
 */
sealed trait Cmd extends Pretty

case class Def(left: Expr, right: Expr) {
  private def check(pattern: Expr): Unit = pattern match {
    case _: Id | Wildcard =>
    case App(left, right) => check(left); check(right)
    case _ => fail("A " + pattern +
      " can not appear on the left hand side of a define statement.")
  }
  left match {
    case Id("elim", None) =>
      fail("elim is a reserved function name that can not be defined manually")
    case Id("intro", None) =>
      fail("intro is a reserved function name that can not be defined manually")
    case id: Id if context isTag id =>
      fail("A define left hand side can not be a tag")
    case App(id: Id, _) if context isTag id =>
      fail("A define left hand side can not start with a tag")
    case Wildcard =>
      fail("A define left hand side can not be a wildcard")
    case App(Wildcard, _) =>
      fail("A define left hand side can not start with a wildcard")
    case _ => check(left)
  }
}
case class Defs(defs: List[Def]) extends Cmd

case class Datas(names: List[String]) extends Cmd
case class Notation(fixs: List[(List[String], Fixity)]) extends Cmd

case class Tests(tests: List[Expr]) extends Cmd
case class Evals(exprs: List[Expr]) extends Cmd

/**
 * Types of fixpoints, [[Least]] for induction and [[Greatest]] for
 * coinduction
 */
sealed trait Fix
case object Least extends Fix
case object Greatest extends Fix

case class Ind(cases: List[Expr], kind: Fix) extends Cmd
case class Thm(name: Option[Id], assume: List[Expr], show: Expr, proof: Option[Tactic]) extends Cmd
object Thm {
  object show0 extends ((Expr, Option[Tactic]) => Thm) {
    def apply(show: Expr, proof: Option[Tactic]): Thm =
      Thm(None, Nil, show, proof)
  }
  object show extends ((List[Expr], Expr, Option[Tactic]) => Thm) {
    def apply(assume: List[Expr], show: Expr, proof: Option[Tactic]): Thm =
      Thm(None, assume, show, proof)
  }
  object lem extends ((Id, Option[List[Expr]], Expr, Option[Tactic]) => Thm) {
    def apply(name: Id, assume: Option[List[Expr]], show: Expr, proof: Option[Tactic]): Thm =
      Thm(Some(name), assume getOrElse Nil, show, proof)
  }
}
