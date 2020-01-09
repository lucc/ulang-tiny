package ulang

import arse._

sealed trait Pos { def unary_!(): Pos }
case object Ant extends Pos { def unary_! = Suc }
case object Suc extends Pos { def unary_! = Ant }

sealed trait Proof {
  def isClosed: Boolean
}

sealed trait Goal extends Proof {
  def assume(phi: Expr): Goal
  def assert(phi: Expr): Goal

  def assume(args: List[Expr]): Goal = {
    args.foldLeft(this)(_ assume _)
  }

  def assert(args: List[Expr]): Goal = {
    args.foldLeft(this)(_ assert _)
  }
}

case object Closed extends Goal {
  def isClosed = true
  def assume(phi: Expr) = this
  def assert(phi: Expr) = this
}

case class Step(prems: List[Proof], concl: Open, tactic: Tactic) extends Proof {
  def isClosed = prems forall (_.isClosed)
}

case class Open(eqs: Subst, rant: List[Expr], rsuc: List[Expr]) extends Goal with Pretty {
  def ant = rant.reverse
  def suc = rsuc.reverse

  def isClosed = false

  import Prove._

  def contains(phi: Expr) = {
    (rant contains phi) || (rsuc contains not(phi))
  }

  def assume(phi: Expr): Goal = phi match {
    case True => this
    case False => Closed
    case _ if this contains not(phi) => Closed
    case Not(phi) => this assert phi
    case And(phi, psi) => this assume phi assume psi
    case Eq(x: Var, e) if !(e.free contains x) => copy(eqs = eqs + (x -> e))
    case Eq(e, x: Var) if !(e.free contains x) => copy(eqs = eqs + (x -> e))
    case _ => copy(rant = phi :: rant)
  }

  def assert(phi: Expr): Goal = phi match {
    case False => this
    case True => Closed
    case _ if this contains phi => Closed
    case Not(phi) => this assume phi
    case Imp(phi, psi) => this assume phi assert psi
    case Or(phi, psi) => this assert phi assert psi
    case _ => copy(rsuc = phi :: rsuc)
  }
}

object Goal {
  val empty = Open(Subst.empty, Nil, Nil)
}

class Prove(context: Context) {
  import Prove._
  import context._

  def prove(ant: List[Expr], suc: Expr, proof: Option[Tactic]): Proof = {
    val goal = init(ant, suc, Goal.empty)

    (goal, proof) match {
      case (open: Open, Some(tactic)) =>
        prove(open, tactic)
      case (_, Some(tactic)) =>
        sys.error("cannot apply: " + tactic + " (goal is closed)")
      case (goal, _) =>
        goal
    }
  }

  def prove(goal: Open, tactic: Tactic): Proof = tactic match {
    case Ind(pat, Least) =>
      ???
    case Split(pat) =>
      val Open(eqs, ant, suc) = goal
      val (found, env, rest) = { search(pat, ant) } or { sys.error("no formula: " + pat) }
      val cases = context fixs pat
      val prems = cases map {
        case (pre, cs) =>
          val _pre = pre map (_ subst env)
          val _cs = cs subst env
          val _ant = _cs :: _pre ::: ant
          init(_ant, Or(suc), Open(eqs, Nil, Nil))
      }
      Step(prems, goal, tactic)
    case _ =>
      ???
  }

  def init(ant: List[Expr], suc: Expr, goal: Goal): Goal = ant match {
    case Nil =>
      val _suc = simp(suc, goal, Suc)
      goal assert _suc
    case phi :: rest =>
      val _phi = simp(phi, goal, Ant)
      init(rest, suc, goal assume _phi)
  }

  def simp(goal: Goal): Goal = goal match {
    case Closed =>
      Closed

    case Open(eqs, ant, suc) =>
      init(ant, Or(suc), Open(eqs, Nil, Nil))
  }

  def simp(phi: Expr, goal: Goal, pos: Pos): Expr = goal match {
    case Closed => True
    case open: Open => simp(phi, open, pos)
  }

  def simp(phi: Expr, goal: Open, pos: Pos): Expr = phi match {
    case True | False => phi
    case _ if goal contains phi =>
      True
    case _ if goal contains not(phi) =>
      False
    case Eq(left, right) =>
      eqn(rewrite(left, goal), rewrite(right, goal))
    case Not(phi) =>
      val _phi = simp(phi, goal, !pos)
      not(_phi)
    case And(left, right) =>
      val _left = simp(left, goal, pos)
      val _right = simp(right, goal assume _left, pos)
      and(_left, _right)
    case Or(left, right) =>
      val _left = simp(left, goal, pos)
      val _right = simp(right, goal assert _left, pos)
      or(_left, _right)
    case Imp(left, right) =>
      val _left = simp(left, goal, !pos)
      val _right = simp(right, goal assume _left, pos)
      imp(_left, _right)
    case Eqv(left, right) =>
      val phi = And(Imp(left, right), Imp(right, left))
      simp(phi, goal, pos)
    case _ =>
      rewrite(phi, goal)
  }

  def rewrite(expr: Expr, goal: Open): Expr = {
    rewrite(expr, goal.eqs)
  }

  def rewrite(exprs: List[Expr], eqs: Subst): List[Expr] = {
    exprs map (rewrite(_, eqs))
  }

  def rewrite(expr: Expr, eqs: Subst): Expr = expr match {
    case id: Var if eqs contains id =>
      rewrite(eqs(id), eqs)
    case id: Var => // avoid immediate recursion on fun in the next case as args.isEmpty
      apply(id, Nil)
    case Apps(fun, Nil) =>
      expr
    case Apps(fun, args) =>
      apply(rewrite(fun, eqs), rewrite(args, eqs))
    case _ =>
      expr
  }

  def apply(fun: Expr, args: List[Expr]): Expr = fun match {
    case id: Var if rewrites contains id =>
      apply(fun, rewrites(id), args)
    case _ =>
      Apps(fun, args)
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

  def search(pat: Pat, exprs: List[Expr]): (Expr, Subst, List[Expr]) = exprs match {
    case Nil =>
      backtrack
    case expr :: exprs =>
      {
        (expr, bind(pat, expr, Subst.empty), exprs)
      } or {
        val (found, env, rest) = search(pat, exprs)
        (found, env, expr :: rest)
      }
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
}

object Prove {
  def eqn(left: Expr, right: Expr) = (left, right) match {
    case _ if left == right => True
    case (Apps(tag1: Tag, _), Apps(tag2: Tag, _)) if tag1 != tag2 => False
    case _ => Eq(left, right)
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

  def merge(pats: List[Pat]): Pat = {
    pats reduce merge
  }

  def merge(pat1: Pat, pat2: Pat): Pat = (pat1, pat2) match {
    case _ if pat1 == pat2 => pat1
    case (UnApp(fun1, arg1), UnApp(fun2, arg2)) => UnApp(merge(fun1, fun2), merge(arg1, arg2))
    case _ => Wildcard
  }
}