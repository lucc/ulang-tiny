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

  var inds: List[(Expr, Fix, List[Intro])] = List()
  var rewrites: Map[Id, List[Case]] = Map()

  def isTag(id: Id): Boolean = {
    val name = id.name
    name.head.isUpper || (data contains name)
  }

  def isVar(id: Id): Boolean = {
    val name = id.name
    !(sig contains name)
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

  def rule(fun: Id, args: List[Expr], rhs: Expr) {
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

  def fixpoint(pat: Expr, kind: Fix, intros: List[Intro]) {
    prevent(inds exists (pat <= _._1), "fixpoint already defined: " + pat)
    inds ++= List((pat, kind, intros))
  }

  def fix(pat: Expr) = {
    ???
    /*
    val Some((gen, kind, intros)) = fixs find (pat <= _._1)
    (gen, kind, intros) */
  }

}
