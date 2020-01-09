package ulang

import java.io.File

import scala.io.Source

import arse._

class Context extends Syntax[String] {
  var data: Set[String] = Set()

  var mixfix: Map[String, Fixity] = Map()

  var prefix_ops: Map[String, Int] = Map()
  var postfix_ops: Map[String, Int] = Map()
  var infix_ops: Map[String, (Assoc, Int)] = Map()
  var bind_ops: Set[String] = Set()

  var funs: Map[Var, List[Case]] = Map()
  var consts: Map[Var, Norm] = Map()

  var inds: Map[Pat, List[(List[Expr], Expr)]] = Map()
  var coinds: Map[Pat, List[(List[Expr], Expr)]] = Map()
  var rewrites: Map[Var, List[Case]] = Map()

  object parser extends Parse(this)
  object eval extends Eval(this)
  object prove extends Prove(this)

  def isMixfix(id: Id): Boolean = {
    contains(id.name) || isBind(id)
  }

  def isBind(id: Id) = {
    bind_ops contains id.name
  }

  def declare(names: List[String], fixity: Fixity) {
    for (name <- names) {
      mixfix += name -> fixity
    }

    for (name <- names) fixity match {
      case Bindfix => bind_ops += name
      case Prefix(prec) => prefix_ops += name -> prec
      case Postfix(prec) => postfix_ops += name -> prec
      case Infix(assoc, prec) => infix_ops += name -> (assoc, prec)
    }
  }

  def const(id: Var, rhs: Norm) {
    if (consts contains id)
      sys.error("constant already defined: " + id)
    consts += id -> rhs
  }

  def fun(id: Var, cs: Case) {
    if (funs contains id) {
      funs += id -> (funs(id) ++ List(cs))
    } else {
      funs += id -> List(cs)
    }
  }

  def rewrite(id: Var, cs: Case) {
    if (rewrites contains id) {
      rewrites += id -> (rewrites(id) ++ List(cs))
    } else {
      rewrites += id -> List(cs)
    }
  }

  def ind(pat: Pat, cases: List[(List[Expr], Expr)]) {
    if (inds contains pat)
      sys.error("induction already defined: " + pat)
    inds += pat -> cases
  }

  def coind(pat: Pat, cases: List[(List[Expr], Expr)]) {
    if (coinds contains pat)
      sys.error("coinduction already defined: " + pat)
    coinds += pat -> cases
  }

  def exec(cmd: Cmd) = cmd match {
    case Defs(defs) =>
      for (Def(id, args, rhs, attr) <- defs) {
        if (args.isEmpty) {
          val res = eval.norm(rhs, Env.empty)
          const(id, res)
        } else {
          fun(id, Case(args, rhs))
        }

        if (attr contains "rewrite") {
          rewrite(id, Case(args, rhs))
        }
      }

    case Evals(exprs) =>
      for (expr <- exprs) {
        val res = eval.strict(expr, Env.empty)
        println(expr)
        println("  == " + res)
      }

    case Fix(cases, kind) =>
      val imps = cases map {
        case Imp(Apps(And.op, ant), suc) =>
          (ant, suc)
        case Imp(ant, suc) =>
          (List(ant), suc)
        case suc =>
          (Nil, suc)
      }

      val sucs = imps map {
        case (_, suc) =>
          suc.toPat
      }

      val pat = Prove.merge(sucs)

      println("fixpoint for " + pat)

      kind match {
        case Least => ind(pat, imps)
        case Greatest => coind(pat, imps)
      }

    case Thm(assume, show) =>
      println(cmd)
      prove(assume, show) match {
        case None => println("  qed")
        case Some(rest) => println("  if " + rest)
      }

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