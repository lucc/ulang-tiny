package ulang

import java.io.File

import scala.io.Source

import arse._

/**
 * The current execution context of the ulang interpreter
 *
 * This class captures the execution context when the ulang interpreter is
 * run.  It holds several mutable variables as the context can evolve over
 * time.
 */
class Context extends Syntax[String] {
  var data: Set[String] = Set()
  var sig: Set[Id] = Set(
    Eq.op, Not.op, And.op, Or.op, Imp.op, Eqv.op)

  /**
   * mixfix is the union of prefix_ops, postfix_ops and infix_ops but is
   * managed seperatly (for pperformance reasons?)
   */
  var mixfix: Map[String, Fixity] = Map()

  var prefix_ops: Map[String, Int] = Map()
  var postfix_ops: Map[String, Int] = Map()
  var infix_ops: Map[String, (Assoc, Int)] = Map()

  var funs: Map[Id, List[Case]] = Map()
  var consts: Map[Id, Norm] = Map()

  var inds: List[(Expr, Fix, List[Intro])] = List()
  var rewrites: Map[Id, List[Case]] = Map()

  /**
   * Test if an identifier is a tag
   *
   * Tags are the "pseudo types" we use inside the unitpe of ulang
   */
  def isTag(id: Id): Boolean = {
    val name = id.name
    name.head.isUpper || (data contains name)
  }

  def isFun(id: Id): Boolean = {
    (sig contains id)
  }

  /**
   * Every identifier that is not in the currently defined signature is
   * considered a variable
   */
  def isVar(id: Id): Boolean = {
     !isTag(id) && !isFun(id)
  }

  def isMixfix(name: String): Boolean = {
    mixfix contains name
  }

  def declare(id: Id) {
    sig += id
  }

  def declare(ids: Iterable[Id]) {
    sig ++= ids
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
      sig contains fun,
      "constant not decalred: " + fun)
    prevent(
      consts contains fun,
      "constant already defined: " + fun)

    consts += fun -> rhs
  }

  def define(fun: Id, cs: Case) {
    ensure(
      sig contains fun,
      "function not decalred: " + fun)

    if (funs contains fun) {
      funs += fun -> (funs(fun) ++ List(cs))
    } else {
      funs += fun -> List(cs)
    }
  }

  def rule(fun: Id, args: List[Expr], rhs: Expr) {
    ensure(
      sig contains fun,
      "function not decalred: " + fun)

    // println("declaring rewrite rule")
    // println("  " + Apps(fun, args) + " == " + rhs)
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
}
