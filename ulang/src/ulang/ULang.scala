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

  var sig: Set[Var] = Set(
    Eq.op, Not.op, Or.op, And.op, Imp.op, Eqv.op)

  var funs: Map[Var, List[Case]] = Map()
  var consts: Map[Var, Norm] = Map()

  var fixs: List[(Pat, FixKind, List[Intro])] = List()
  var rewrites: Map[Var, List[Case]] = Map()

  object parser extends Parse(this)
  object eval extends Eval(this)
  object prove extends Prove(this)

  def isMixfix(id: Id): Boolean = {
    contains(id.name)
  }

  def declare(names: List[String], fixity: Fixity) {
    for (name <- names) {
      mixfix += name -> fixity
    }

    for (name <- names) fixity match {
      case Prefix(prec) => prefix_ops += name -> prec
      case Postfix(prec) => postfix_ops += name -> prec
      case Infix(assoc, prec) => infix_ops += name -> (assoc, prec)
    }
  }

  def const(id: Var, rhs: Norm) {
    if (consts contains id)
      sys.error("constant already defined: " + id)
    sig += id
    consts += id -> rhs
  }

  def fun(id: Var, cs: Case) {
    if (funs contains id) {
      sig += id
      funs += id -> (funs(id) ++ List(cs))
    } else {
      sig += id
      funs += id -> List(cs)
    }
  }

  def calls(id: Var, cs: Case): List[(Id, List[Expr])] = {
    if (cs.bound contains id) List()
    else calls(id, cs.body)
  }

  def calls_(id: Var, cases: List[Case]): List[(Id, List[Expr])] = {
    cases flatMap (calls(id, _))
  }

  def calls(id: Var, exprs: List[Expr]): List[(Id, List[Expr])] = {
    exprs flatMap (calls(id, _))
  }

  def calls(id: Var, expr: Expr): List[(Id, List[Expr])] = expr match {
    case Apps(`id`, args) => List((id, args)) ++ calls(id, args)
    case Apps(_, args) => calls(id, args)
    case Lam(cases) => calls_(id, cases)
    case Match(args, cases) => calls(id, args) ++ calls_(id, cases)
    case let: Let if !(let.bound contains id) => calls(id, let.body)
    case _ => List()
  }

  def lex(expr: Expr, pat: Pat): Boolean = (expr, pat) match {
    case (_, UnApps(_: Tag, args)) if (args contains expr) || (args exists (lex(expr, _))) => true
    case _ => false
  }

  def lex(exprs: List[Expr], pats: List[Pat]): Boolean = {
    (exprs zip pats) exists { case (expr, pat) => lex(expr, pat) }
  }

  def safeRewrite(id: Var, pats: List[Pat], rhs: Expr) {
    if (pats.isEmpty) {
      if (!(rhs.free contains id))
        rewrite(id, pats, rhs)
    } else {
      val rec = calls(id, rhs)
      val args = rec map (_._2)
      if (args forall (lex(_, pats)))
        rewrite(id, pats, rhs)
    }
  }

  def rewrite(id: Var, args: List[Pat], rhs: Expr) {
    val cs = Case(args, rhs)
    if (rewrites contains id) {
      sig += id
      rewrites += id -> (rewrites(id) ++ List(cs))
    } else {
      sig += id
      rewrites += id -> List(cs)
    }
  }

  def fix(id: Var, pat: Pat, kind: FixKind, cases: List[Intro]) {
    if (fixs exists (pat <= _._1))
      sys.error("fixpoint already defined: " + pat)
    sig += id
    fixs ++= List((pat, kind, cases))
  }

  def fix(pat: Pat) = {
    val Some((gen, kind, intros)) = fixs find (pat <= _._1)
    (gen, kind, intros)
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
          rewrite(id, args, rhs)
        } else {
          safeRewrite(id, args, rhs)
        }
      }

    case Evals(exprs) =>
      for (expr <- exprs) {
        val res = eval.strict(expr, Env.empty)
        println(expr)
        println("  == " + res)
      }

    case Fix(cases, kind) =>
      val intros = cases map {
        case Imp(Apps(And.op, ant), suc) =>
          Intro(ant, suc)
        case Imp(ant, suc) =>
          Intro(List(ant), suc)
        case suc =>
          Intro(Nil, suc)
      }

      val pat = Prove.merge(intros map (_.pat.anon))
      pat match {
        case UnApps(fun: Var, args) =>
          fix(fun, pat, kind, intros)
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

object ULang {
  def main(args: Array[String]) = {
    for (name <- args) {
      val context = new Context
      context run name
    }
  }
}