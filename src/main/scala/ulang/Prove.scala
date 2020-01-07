package ulang

import arse._

case class Ant(path: List[Expr], eqs: Subst) {
  def ::(phi: Expr) = Ant(phi :: path, eqs)
  def +(xe: (Var, Expr)) = Ant(path, eqs + xe)
  def maps(x: Var) = eqs contains x
  def apply(x: Var) = eqs(x)
  def contains(expr: Expr) = path contains expr
}

object Ant {
  val empty = Ant(Nil, Subst.empty)
}

class Prove(context: Context) {
  import context._

  def prove(pre: List[Expr], show: Expr): Expr = {
    val ant = assume(pre, Ant.empty)
    prove(ant, show)
  }

  def prove(ant: Ant, show: Expr): Expr = show match {
    case True | False =>
      show
    case _ if ant contains False =>
      True
    case _ if ant contains show =>
      True
    case Eq(left, right) if left == right =>
      True
    case Not(expr) =>
      not(prove(ant, expr))
    case And(left, right) =>
      and(prove(ant, left), prove(assume(left, ant), right))
    case Or(left, right) =>
      or(prove(ant, left), prove(assert(left, ant), right))
    case Imp(left, right) =>
      imp(prove(ant, left), prove(assume(left, ant), right))
    case Eqv(left, right) =>
      val expr = And(Imp(left, right), Imp(right, left))
      prove(ant, expr)
    case _ =>
      show
  }

  def apply(cs: Case, args: List[Expr]): Expr = cs match {
    case Case(pats, body) =>
      val env = bind(pats, args, Subst.empty)
      body subst env
  }

  def apply(fun: Expr, cases: List[Case], args: List[Expr]): Expr = cases match {
    case Nil =>
      Apps(fun, args)
    case cs :: rest =>
      { apply(cs, args) } or { apply(fun, rest, args) }
  }

  def apply(fun: Expr, args: List[Expr]): Expr = fun match {
    case id: Var if rewrites contains id =>
      apply(fun, rewrites(id), args map rewrite)
    case _ =>
      Apps(fun, args)
  }

  def rewrite(expr: Expr): Expr = expr match {
    case id: Id => // avoid immediate recursion on fun in the next case as args.isEmpty
      apply(id, Nil)
    case Apps(fun, args) =>
      apply(rewrite(fun), args map rewrite)
    case _ =>
      expr
  }

  def bind(pat: Pat, arg: Expr, env: Subst): Subst = pat match {
    case Wildcard =>
      env
    case Strict(pat) =>
      bind(pat, arg, env)
    case x: Var if env contains x =>
      if (env(x) == arg) env
      else backtrack
    case x: Var =>
      println("bind " + x + " to " + arg + " in " + env)
      env + (x -> arg)
    case tag: Tag =>
      if (tag == arg) env
      else backtrack
    case UnApp(pfun, parg) =>
      arg match {
        case App(vfun, varg) => bind(parg, varg, bind(pfun, vfun, env))
        case _ => backtrack
      }
    case _ =>
      backtrack
  }

  def bind(pats: List[Pat], args: List[Expr], env: Subst): Subst = (pats, args) match {
    case (Nil, Nil) => env
    case (pat :: pats, arg :: args) => bind(pats, args, bind(pat, arg, env))
    case _ => sys.error("argument length mismatch: " + pats.mkString(" ") + " and " + args.mkString(" "))
  }

  def assume(args: List[Expr], ant: Ant): Ant = {
    args.foldRight(ant)(assume)
  }

  def assert(args: List[Expr], ant: Ant): Ant = {
    args.foldRight(ant)(assert)
  }

  def assume(phi: Expr, ant: Ant): Ant = phi match {
    case True =>
      ant
    case Not(psi) =>
      assert(psi, ant)
    case And(phi, psi) =>
      assume(phi, assume(psi, ant))
    case Eq(x: Var, e) if !(e.free contains x) =>
      ant + (x -> e)
    case Eq(e, x: Var) if !(e.free contains x) =>
      ant + (x -> e)
    case _ =>
      phi :: ant
  }

  def assert(phi: Expr, ant: Ant): Ant = phi match {
    case False =>
      ant
    case Not(psi) =>
      assume(psi, ant)
    case Imp(phi, psi) =>
      assert(phi, assume(psi, ant))
    case Or(phi, psi) =>
      assert(phi, assert(psi, ant))
    case _ =>
      not(phi) :: ant
  }

  def not(expr: Expr) = expr match {
    case True => False
    case False => True
    case Not(expr) => expr
    case _ => Not(expr)
  }

  def and(left: Expr, right: Expr) = (left, right) match {
    case (True, _) => right
    case (False, _) => False
    case (_, True) => left
    case (_, False) => False
    case _ => And(left, right)
  }

  def or(left: Expr, right: Expr) = (left, right) match {
    case (True, _) => True
    case (False, _) => right
    case (_, True) => True
    case (_, False) => left
    case _ => Or(left, right)
  }

  def imp(left: Expr, right: Expr) = (left, right) match {
    case (True, _) => right
    case (False, _) => True
    case (_, True) => True
    case (_, False) => not(left)
    case _ => Imp(left, right)
  }

  def eqv(left: Expr, right: Expr) = (left, right) match {
    case _ if left == right => True
    case (True, _) => right
    case (False, _) => not(right)
    case (_, True) => left
    case (_, False) => not(left)
    case _ => Eqv(left, right)
  }
}