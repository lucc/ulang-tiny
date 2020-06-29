package ulang

import java.io.File

import scala.io.Source

import arse._

class Context extends Syntax[String] {
  var data: Set[String] = Set()
  var sig: Set[String] = Set("==", "not", "\\/", "/\\", "==>", "<=>")

  var mixfix: Map[String, Fixity] = Map()

  var prefix_ops: Map[String, Int] = Map()
  var postfix_ops: Map[String, Int] = Map()
  var infix_ops: Map[String, (Assoc, Int)] = Map()

  var funs: Map[Id, List[Case]] = Map()
  var consts: Map[Id, Norm] = Map()

  var fixs: List[(Expr, Fix, List[Intro])] = List()
  var rewrites: Map[Id, List[Case]] = Map()

  def isTag(id: Id): Boolean = {
    val name = id.name
    name.head.isUpper || (data contains name)
  }

  def isMixfix(name: String): Boolean = {
    mixfix contains name
  }

  def declare(name: String) {
    sig += name
  }

  def declare(names: List[String]) {
    sig ++= names
  }

  def notation(names: List[String], fixity: Fixity) {
    for (name <- names) {
      mixfix += name -> fixity
    }

    for (name <- names) fixity match {
      case Prefix(prec) => prefix_ops += name -> prec
      case Postfix(prec) => postfix_ops += name -> prec
      case Infix(assoc, prec) => infix_ops += name -> (assoc, prec)
    }
  }

  def define(fun: Id, rhs: Norm) {
    ensure(
      sig contains fun.name,
      "constant not decalred: " + fun)
    prevent(
      consts contains fun,
      "constant already defined: " + fun)

    consts += fun -> rhs
  }

  def define(fun: Id, cs: Case) {
    ensure(
      sig contains fun.name,
      "function not decalred: " + fun)

    if (funs contains fun) {
      funs += fun -> (funs(fun) ++ List(cs))
    } else {
      funs += fun -> List(cs)
    }
  }

  /* def calls(fun: Id, cs: Case): List[(Id, List[Expr])] = {
    calls(fun, cs.body)
  }

  def calls_(fun: Id, cases: List[Case]): List[(Id, List[Expr])] = {
    cases flatMap (calls(fun, _))
  }

  def calls(fun: Id, exprs: List[Expr]): List[(Id, List[Expr])] = {
    exprs flatMap (calls(fun, _))
  }

  def calls(fun: Id, expr: Expr): List[(Id, List[Expr])] = expr match {
    case Apps(`fun`, args) => List((fun, args)) ++ calls(fun, args)
    case Apps(_, args) => calls(fun, args)
    case Lam(cases) => calls_(fun, cases)
    case Match(args, cases) => calls(fun, args) ++ calls_(fun, cases)
    // case let: Let if !(let.bound contains fun) => calls(fun, let.body)
    case _ => List()
  }

  def lex(expr: Expr, pat: Expr): Boolean = (expr, pat) match {
    case (_, Apps(_: Tag, args)) if (args contains expr) || (args exists (lex(expr, _))) => true
    case _ => false
  }

  def lex(exprs: List[Expr], pats: List[Expr]): Boolean = {
    (exprs zip pats) exists { case (expr, pat) => lex(expr, pat) }
  }

  def safeRewrite(fun: Id, pats: List[Expr], rhs: Expr) {
    if (pats.isEmpty) {
      if (!(rhs.funs contains fun))
        rewrite(fun, pats, rhs)
    } else {
      val rec = calls(fun, rhs)
      val args = rec map (_._2)
      if (args forall (lex(_, pats)))
        rewrite(fun, pats, rhs)
    }
  } */

  def rewrite(fun: Id, args: List[Expr], rhs: Expr) {
    ensure(
      sig contains fun.name,
      "function not decalred: " + fun)

    val cs = Case(args, rhs)
    if (rewrites contains fun) {
      rewrites += fun -> (rewrites(fun) ++ List(cs))
    } else {
      rewrites += fun -> List(cs)
    }
  }

  def fix(id: Id, pat: Expr, kind: Fix, cases: List[Expr]) {
    ???
    /*
    if (fixs exists (pat <= _._1))
      sys.error("fixpoint already defined: " + pat)
    sig += id
    fixs ++= List((pat, kind, cases)) */
  }

  def fix(pat: Expr) = {
    ???
    /*
    val Some((gen, kind, intros)) = fixs find (pat <= _._1)
    (gen, kind, intros) */
  }
}
