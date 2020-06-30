package ulang

import arse._

object Simp {
  import context._

  def simp(phi: Expr, goal: Goal, pos: Pos): Expr = goal match {
    case Closed => True
    case open: Open => simp(phi, open, pos)
  }

  def simp(phi: Expr, goal: Open, pos: Pos): Expr = {
    val res = _simp(phi, goal, pos)
    //    if (phi != res)
    //      println(phi + " ~> " + res)
    res
  }

  def _simp(phi: Expr, goal: Open, pos: Pos): Expr = phi match {
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

  def rewrite(expr: Expr, eqs: Subst): Expr = {
    val res = _rewrite(expr, eqs)
    if (res != expr) {
      // println("rewrite " + expr + " ~> " + (expr subst eqs) + " ~> " + res)
      rewrite(res, eqs)
    } else {
      res
    }
  }

  def _rewrite(expr: Expr, eqs: Subst): Expr = expr match {
    case id: Id if eqs contains id =>
      rewrite(eqs(id), eqs)
    case id: Id => // avoid immediate recursion on fun in the next case as args.isEmpty
      apply(id, Nil)
    case Apps(fun, Nil) =>
      expr
    case Apps(fun, args) =>
      apply(rewrite(fun, eqs), rewrite(args, eqs))
    case _ =>
      expr
  }

  def apply(fun: Expr, args: List[Expr]): Expr = fun match {
    case id: Id if rewrites contains id =>
      apply(fun, rewrites(id), args)
    case _ =>
      Apps(fun, args)
  }

  def apply(cs: Case, args: List[Expr]): Expr = cs match {
    case Case(pats, body) if pats.length == args.length =>
      val env = bind(pats, args, Subst.empty)
      body subst env
    case _ =>
      backtrack // partial application
  }

  def apply(fun: Expr, cases: List[Case], args: List[Expr]): Expr = cases match {
    case Nil =>
      Apps(fun, args)
    case cs :: rest =>
      { apply(cs, args) } or { apply(fun, rest, args) }
  }

  def eqn(left: Expr, right: Expr) = (left, right) match {
    case _ if left == right => True
    case (Apps(tag1: Id, _), Apps(tag2: Id, _)) if isTag(tag1) && isTag(tag2) && tag1 != tag2 => False
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

  def find(pat: Expr, exprs: List[Expr]): (Expr, Subst, List[Expr]) = exprs match {
    case Nil =>
      backtrack
    case expr :: exprs =>
      {
        (expr, bind(pat, expr, Subst.empty), exprs)
      } or {
        val (found, env, rest) = find(pat, exprs)
        (found, env, expr :: rest)
      }
  }

  def findAll(pat: Expr, exprs: List[Expr]): (List[(Expr, Subst)], List[Expr]) = exprs match {
    case Nil =>
      (Nil, Nil)
    case expr :: exprs =>
      val (found, rest) = findAll(pat, exprs)

      {
        val env = bind(pat, expr, Subst.empty)
        ((expr, env) :: found, rest)
      } or {
        (found, expr :: rest)
      }
  }

  def bind(pat: Expr, arg: Expr, env: Subst): Subst = pat match {
    case Wildcard =>
      env
    /* case Strict(pat) =>
      bind(pat, arg, env) */
    case id: Id if isTag(id) =>
      if (id == arg) env
      else backtrack
    case id: Id if env contains id =>
      if (env(id) == arg) env
      else backtrack
    case id: Id =>
      env + (id -> arg)
    case Apps(fun: Id, pats) =>
      arg match {
        case Apps(`fun`, args) => bind(pats, args, env)
        case _ => backtrack
      }
    case _ =>
      backtrack
  }

  def bind(pats: List[Expr], args: List[Expr], env: Subst): Subst = (pats, args) match {
    case (Nil, Nil) => env
    case (pat :: pats, arg :: args) => bind(pats, args, bind(pat, arg, env))
    case _ => fail("argument length mismatch: " + pats.mkString(" ") + " and " + args.mkString(" "))
  }

  def lex(expr: Expr, pat: Expr): Boolean = (expr, pat) match {
    case (_, Apps(tag: Id, args)) if isTag(tag) && (args contains expr) || (args exists (lex(expr, _))) => true
    case _ => false
  }

  def lex(exprs: List[Expr], pats: List[Expr]): Boolean = {
    (exprs zip pats) exists { case (expr, pat) => lex(expr, pat) }
  }

  def isSafe(fun: Id, pats: List[Expr], exprs: List[Expr]): Boolean = {
    exprs forall (isSafe(fun, pats, _))
  }

  def isSafe(fun: Id, pats: List[Expr], rhs: Expr): Boolean = rhs match {
    case Apps(`fun`, args) =>
      lex(args, pats) && isSafe(fun, pats, args)
    case Apps(_, args) =>
      isSafe(fun, pats, args)
    case _ =>
      false
  }

  def isSafe(fun: Id, exprs: List[Expr]): Boolean = {
    exprs forall (isSafe(fun, _))
  }

  def isSafe(fun: Id, rhs: Expr): Boolean = rhs match {
    case Apps(`fun`, _) =>
      false
    case Apps(_, args) =>
      isSafe(fun, args)
  }
}