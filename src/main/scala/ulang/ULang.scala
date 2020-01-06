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

  object parser extends ULangParser(this)
  object eval extends Eval(this)

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

  def parse(file: File): List[Cmd] = {
    val source = Source.fromFile(file)
    parse(source.mkString)
  }

  def parse(string: String): List[Cmd] = {
    import parser._
    script parse string
  }

  def run(name: String) {
    val file = new File(name)
    val cmds = parse(file)
    eval.exec(cmds)
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