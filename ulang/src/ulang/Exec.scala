package ulang

import scala.io.Source
import java.io.File

class Exec(context: Context) {
  import context._

  def exec(cmd: Cmd) = cmd match {
    /* case Defs(defs) =>
      for (Def(Head(id, args), rhs, attr) <- defs) {
        if (args.isEmpty) {
          val res = eval.norm(rhs, Env.empty)
          const(id, res)
        } else {
          fun(id, Case(args, rhs))
        }

        if (attr contains "rewrite") {
          rewrite(id, args, rhs)
        } else {
          safeRewrite(id, args, rhs)
        }
      } */

    case Evals(exprs) =>
      for (expr <- exprs) {
        val res = eval.strict(expr, Env.empty)
        println(expr)
        println("  == " + res)
      }

    case Tests(tests) =>
      for (expr <- tests) {
        /*
        val actual = eval.strict(lhs, Env.empty)
        val expected = eval.strict(rhs, Env.empty)
        assert(actual == expected) */
      }

    case Intros(cases, kind) =>
      val pat = ??? // merge(cases map (_.patx))
      pat match {
        case Apps(fun: Var, args) =>
          fix(fun, pat, kind, cases)
        case _ =>
          sys.error("not an inductive definition: " + pat)
      }

    case Thm(assume, show, tactic) =>
      val proof = prove.prove(assume, show, tactic)
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
    import parser._
    script parseAll string
  }

  def run(name: String) {
    val file = new File(name)
    val cmds = parse(file)
    exec(cmds)
  }
}