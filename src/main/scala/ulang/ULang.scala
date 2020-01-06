package ulang

import java.io.File

import scala.io.Source

import arse._

class Context extends Syntax[String] {
  var data: Set[String] = Set()

  var prefix_ops: Map[String, Int] = Map()
  var postfix_ops: Map[String, Int] = Map()
  var infix_ops: Map[String, (Assoc, Int)] = Map()
  var bind_ops: Set[String] = Set()

  var funs: Map[Var, List[Case]] = Map()
  var consts: Map[Var, Norm] = Map()
  
  var rewrites: Map[Var, List[Case]] = Map()
  
  object parser extends ULangParser(this)
  object eval extends Eval(this)
  object prove extends Prove(this)

  def isMixfix(id: Id): Boolean = {
    contains(id.name) || isBind(id)
  }

  def isBind(id: Id) = {
    bind_ops contains id.name
  }

  def declare(names: List[String], fixity: Fixity) {
    for (name <- names) fixity match {
      case Bindfix => bind_ops += name
      case Prefix(prec) => prefix_ops += name -> prec
      case Postfix(prec) => postfix_ops += name -> prec
      case Infix(assoc, prec) => infix_ops += name -> (assoc, prec)
    }
  }

  def exec(cmd: Cmd) = cmd match {
    case Defs(defs) =>
      for (Def(id, args, rhs) <- defs) {
        if (args.isEmpty) {
          if (consts contains id)
            sys.error("already defined: " + id)
          consts += id -> eval.norm(rhs, Env.empty)
        } else {
          val cs = Case(args, rhs)
          if (funs contains id) {
            val cases = funs(id) ++ List(cs)
            funs += id -> cases
          } else {
            funs += id -> List(cs)
          }
        }
      }

    case Evals(exprs) =>
      for (expr <- exprs) {
        val res = eval.strict(expr, Env.empty)
        println(expr)
        println("  == " + res)
      }

    case Thm(assume, show) =>
      val rest = prove.prove(assume, show)
      println(rest)

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

object ULang {
  def main(args: Array[String]) = {
    for (name <- args) {
      val context = new Context
      context run name
    }
  }
}