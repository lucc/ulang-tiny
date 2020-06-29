package ulang

import scala.io.Source
import java.io.File

object Exec {
  import context._
  
  def split(df: Def) = {
    val (lhs, rhs) = Eq.split(df.expr)
    val Apps(fun: Id, args) = lhs
    (fun, args, rhs)
  }

  def exec(cmd: Cmd) = cmd match {
    case Defs(defs) =>
      val eqs = defs map split

      for ((id, args, rhs) <- eqs) {
        declare(id.name)
        
        if (args.isEmpty) {
          val res = Eval.norm(rhs, Env.empty)
          define(id, res)
        } else {
          val cs = Case(args, rhs)
          define(id, cs)
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
        val (lhs, rhs) = Eq.split(expr)
        val actual = Eval.strict(lhs, Env.empty)
        val expected = Eval.strict(rhs, Env.empty)
        ensure(actual == expected, "test failed, actual: " + actual + ", expected: " + expected)
      }

    /* case Intros(cases, kind) =>
      val pat = ??? // merge(cases map (_.patx))
      pat match {
        case Apps(fun: Var, args) =>
          fix(fun, pat, kind, cases)
        case _ =>
          fail("not an inductive definition: " + pat)
      }

    case Thm(assume, show, tactic) =>
      val proof = prove.prove(assume, show, tactic)
      for (line <- Print.format(proof))
        println(line) */

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