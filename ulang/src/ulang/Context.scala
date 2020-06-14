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

  var funs: Map[Fun, List[Case]] = Map()
  var consts: Map[Fun, Norm] = Map()

  var fixs: List[(Expr, Fix, List[Intro])] = List()
  var rewrites: Map[Fun, List[Case]] = Map()

  object parser extends Parse(this)
  object eval extends Eval(this)
  object exec extends Exec(this)
  object prove extends Prove(this)

  def isMixfix(name: String): Boolean = {
    mixfix contains name
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

  def define(fun: Fun, rhs: Norm) {
    if (consts contains fun)
      sys.error("constant already defined: " + fun)
    sig += fun.name
    consts += fun -> rhs
  }

  def define(fun: Fun, cs: Case) {
    if (funs contains fun) {
      sig += fun.name
      funs += fun -> (funs(fun) ++ List(cs))
    } else {
      sig += fun.name
      funs += fun -> List(cs)
    }
  }

  def resolve(bound: List[Var], name: String): Id = {
    val fixity = mixfix.getOrElse(name, Nilfix)

    if (bound exists (_.name == name))
      Var(name, fixity)
    else if (data contains name)
      Tag(name, fixity)
    else if (name.head.isUpper)
      Tag(name, fixity)
    else if (sig contains name)
      Fun(name, fixity)
    else
      Var(name, fixity)
  }

  def resolve(bound: List[Var], expr: Expr): Expr = expr match {
    case Wildcard => Wildcard
    case id: Id => id
    case Raw(name) => resolve(bound, name)
    case App(fun, arg) => App(resolve(bound, fun), resolve(bound, arg))
    case Bind(quant, args, body) => Bind(quant, args, resolve(bound ++ args, body))
    case Ite(test, left, right) => Ite(resolve(bound, test), resolve(bound, left), resolve(bound, right))
    // case lam
    // case let
    // case Match
  }

  def calls(fun: Fun, cs: Case): List[(Fun, List[Expr])] = {
    if (cs.bound contains fun) List()
    else calls(fun, cs.body)
  }

  def calls_(fun: Fun, cases: List[Case]): List[(Fun, List[Expr])] = {
    cases flatMap (calls(fun, _))
  }

  def calls(fun: Fun, exprs: List[Expr]): List[(Fun, List[Expr])] = {
    exprs flatMap (calls(fun, _))
  }

  def calls(fun: Fun, expr: Expr): List[(Fun, List[Expr])] = expr match {
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

  def safeRewrite(fun: Fun, pats: List[Expr], rhs: Expr) {
    if (pats.isEmpty) {
      if (!(rhs.funs contains fun))
        rewrite(fun, pats, rhs)
    } else {
      val rec = calls(fun, rhs)
      val args = rec map (_._2)
      if (args forall (lex(_, pats)))
        rewrite(fun, pats, rhs)
    }
  }

  def rewrite(fun: Fun, args: List[Expr], rhs: Expr) {
    val cs = Case(args, rhs)
    if (rewrites contains fun) {
      sig += fun.name
      rewrites += fun -> (rewrites(fun) ++ List(cs))
    } else {
      sig += fun.name
      rewrites += fun -> List(cs)
    }
  }

  def fix(id: Var, pat: Expr, kind: Fix, cases: List[Intro]) {
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
