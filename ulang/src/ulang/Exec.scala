package ulang

import scala.io.Source
import java.io.File

object Exec {
  import context._

  def split(df: Def) = {
    val (lhs, rhs) = Eq.split(df.expr)
    // TODO: complain properly if fun is not Id
    val Apps(fun: Id, args) = lhs
    (fun, args, rhs)
  }

  def intro(expr: Expr) = {
    val (ant, suc) = Imp.split(expr)
    // TODO: complain properly if fun is not Id
    val Apps(fun: Id, args) = suc
    (ant, fun, args)
  }

  def anon(expr: Expr): Expr = expr match {
    case id: Id if isTag(id) =>
      id
    case _: Id =>
      Wildcard
    case App(fun, arg) =>
      def app(fun: Expr, arg: Expr) = (fun, arg) match {
        case (Wildcard, Wildcard) => Wildcard
        case _ => App(fun, arg)
      }
      app(anon(fun), anon(arg))
    case _ =>
      fail("not a pattern: " + expr)
  }

  def anon(exprs: List[Expr]): List[Expr] = {
    exprs map anon
  }

  def merge(expr1: Expr, expr2: Expr): Expr = (expr1, expr2) match {
    case (App(fun1, arg1), App(fun2, arg2)) =>
      App(merge(fun1, fun2), merge(arg1, arg2))
    case _ if expr1 == expr2 =>
      expr1
    case _ =>
      Wildcard
  }

  def merge(exprs: List[Expr]): Expr = {
    assert(exprs.nonEmpty)
    exprs reduce merge
  }

  def split(ind: Ind) = {
    val Ind(exprs, fix) = ind
    val rules = exprs map Imp.split

    val heads = for ((_, suc) <- rules) yield {
      val Apps(fun: Id, args) = suc
      Apps(fun, anon(args))
    }

    val pat = merge(heads)

    val intros = for ((ant, suc) <- rules) yield {
      val (rec, cond) = ant partition (_ <= pat)
      Intro(rec, cond, suc)
    }

    (pat, fix, intros)
  }

  def exec(cmd: Cmd) = cmd match {
    case Defs(defs) =>
      val eqs = defs map split

      for ((id, args, rhs) <- eqs) {
        declare(id)

        if (args.isEmpty) {
          val res = Eval.norm(rhs, Env.empty)
          define(id, res)
        } else {
          val cs = Case(args, rhs)
          define(id, cs)
        }

        if (args.isEmpty) {
          if (Simp.isSafe(id, rhs))
            rule(id, Nil, rhs)
        } else {
          if (Simp.isSafe(id, args, rhs))
            rule(id, args, rhs)
        }
      }

    case Evals(exprs) =>
      for (expr <- exprs) {
        val res = Eval.strict(expr, Env.empty)
        println(expr)
        println("  == " + res)
      }

    case Tests(tests) =>
      for (expr <- tests) {
        // TODO non equalities should also be testable, debug this
        val (lhs, rhs) = Eq.split(expr)
        val actual = Eval.strict(lhs, Env.empty)
        val expected = Eval.strict(rhs, Env.empty)
        ensure(actual == expected, "test failed, actual: " + actual + ", expected: " + expected)
      }

    case ind: Ind =>
      val (pat, fix, intros) = split(ind)
      val Apps(id: Id, _) = pat
      declare(id)
      fixpoint(pat, fix, intros)
      println("declaring fixpoint for " + pat + " (" + fix + ")")
      for (intro <- intros)
        println("  " + intro)
      println()

    case Thm(Nil, show, Some(Term(proofterm))) =>
      if (ProofTermChecker.check(proofterm, show))
        println(proofterm + " proves " + show)
      else
        fail("The term " + proofterm + " does not prove " + show)

    case Thm(assume, show, tactic) =>
      val proof = Prove.prove(assume, show, tactic)
      for (line <- Print.format(proof))
        println(line)

    case _ =>
  }

  def exec(cmds: List[Cmd]) {
    for (cmd <- cmds) {
      exec(cmd)
    }
  }

  def parse(file: File): List[Cmd] = {
    val source = Source.fromFile(file)
    parse(source.mkString)
  }

  def parse(string: String): List[Cmd] = {
    import Parse._
    script parseAll string
  }

  def run(name: String) {
    val file = new File(name)
    val cmds = parse(file)
    exec(cmds)
  }
}
