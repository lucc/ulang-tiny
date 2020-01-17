package ulang

import arse._

class Prove(context: Context) {
  import Prove._
  import context._

  def prove(ant: List[Expr], suc: Expr, proof: Option[Tactic]): Proof = {
    val goal = auto(ant, suc, Goal.empty)

    (goal, proof) match {
      case (open: Open, Some(tactic)) =>
        prove(open, tactic)
      case (step @ Step(List(prem: Open), concl, auto), Some(tactic)) =>
        Step(List(prove(prem, tactic)), concl, auto)
      case (_, Some(tactic)) =>
        sys.error("cannot apply: " + tactic + " (goal is closed)")
      case (goal, _) =>
        goal
    }
  }

  def elim(intro: Intro, target: Expr, eqs: Subst, ant: List[Expr], suc: List[Expr], hyp: Option[Pat]): Proof = {
    val fresh = Expr.fresh(intro.free -- sig)
    val Intro(pre, post) = intro rename fresh

    val Apps(fun1, args1) = post
    val Apps(fun2, args2) = target
    assert(fun1 == fun2) // satisifed from the pattern match
    assert(args1.length == args2.length)

    val eq = Eq.zip(args1, args2)
    val _suc = Or(suc)

    def collapse(left: List[Expr], right: List[Expr]): List[(Var, Expr)] = (left, right) match {
      case (Nil, Nil) => Nil
      case ((x: Var) :: left, e :: right) => (x, e) :: collapse(left, right)
      case (Apps(fun1, args1) :: left, Apps(fun2, args2) :: right) if fun1 == fun2 => collapse(args1 ++ left, args2 ++ right)
      case (x :: _, e :: _) if x != e => sys.error("can't instantiate inductive premise for: " + x + " == " + e)
    }

    hyp match {
      case Some(pat) =>
        val (found, rest) = searchAll(pat, pre)
        val hyps = found map {
          case (rec, env) =>
            val Apps(fun0, args0) = rec
            val inst = collapse(args2, args0)
            val hyp = imp(And(ant), _suc)
            val _hyp = hyp subst inst.toMap
            _hyp
        }
        auto(eq ++ ant ++ hyps, _suc, Open(eqs, Nil, Nil))
      case None =>
        auto(eq ++ ant, _suc, Open(eqs, Nil, Nil))
    }
  }

  def ind(pat: Pat, goal: Open, hyp: Boolean): List[Proof] = {
    val Open(eqs, ant, suc) = goal
    val (found, env, rest) = { search(pat, ant) } or { sys.error("no formula: " + pat) }
    // if (!env.isEmpty)
    //   sys.error("can't introduce new vars here: " + env.keys.mkString(" "))
    val (gen, kind, intros) = fix(pat)
    val rec = if (hyp) Some(gen) else None
    val free = goal.free
    intros map (elim(_, found, eqs, rest, suc, rec))
  }

  def prove(goal: Open, tactic: Tactic): Proof = tactic match {
    case Split(pat) =>
      val prems = ind(pat, goal, hyp = false)
      Step(prems, goal, tactic)
    case Ind(pat, Least) =>
      val prems = ind(pat, goal, hyp = true)
      Step(prems, goal, tactic)
    case Ind(pat, Greatest) =>
      ???
  }

  def auto(ant: List[Expr], suc: Expr, goal: Open): Proof = {
    val Open(eqs, rant, rsuc) = goal
    val prem = init(ant, suc, goal)
    Step(List(prem), Open(eqs, ant ++ rant, suc :: rsuc), Auto)
  }

  def auto(goal: Goal): Proof = goal match {
    case Closed => Closed
    case Open(eqs, ant, suc) => auto(ant, Or(suc), Open(eqs, Nil, Nil))
  }

  def init(ant: List[Expr], suc: Expr, goal: Goal): Goal = ant match {
    case Nil =>
      val _suc = simp(suc, goal, Suc)
      goal assert _suc
    case phi :: rest =>
      val _phi = simp(phi, goal, Ant)
      init(rest, suc, goal assume _phi)
  }

  def simp(phi: Expr, goal: Goal, pos: Pos): Expr = goal match {
    case Closed => True
    case open: Open => simp(phi, open, pos)
  }

  def simp(phi: Expr, goal: Open, pos: Pos): Expr = {
    val res = _simp(phi, goal, pos)
    if (phi != res)
      println(phi + " ~> " + res)
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
    case Case(pats, body) if pats.length == args.length =>
      val env = bind(pats, args, sig, Subst.empty)
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

  def search(pat: Pat, exprs: List[Expr]): (Expr, Subst, List[Expr]) = exprs match {
    case Nil =>
      backtrack
    case expr :: exprs =>
      {
        (expr, bind(pat, expr, sig, Subst.empty), exprs)
      } or {
        val (found, env, rest) = search(pat, exprs)
        (found, env, expr :: rest)
      }
  }

  def searchAll(pat: Pat, exprs: List[Expr]): (List[(Expr, Subst)], List[Expr]) = exprs match {
    case Nil =>
      (Nil, Nil)
    case expr :: exprs =>
      val (found, rest) = searchAll(pat, exprs)

      {
        val env = bind(pat, expr, sig, Subst.empty)
        ((expr, env) :: found, rest)
      } or {
        (found, expr :: rest)
      }
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

  def bind(pat: Pat, arg: Expr, sig: Set[Var], env: Subst): Subst = pat match {
    case Wildcard =>
      env
    case Strict(pat) =>
      bind(pat, arg, sig, env)
    case x: Var if sig contains x =>
      if (x == arg) env
      else backtrack
    case x: Var if env contains x =>
      if (env(x) == arg) env
      else backtrack
    case x: Var =>
      env + (x -> arg)
    case tag: Tag =>
      if (tag == arg) env
      else backtrack
    case UnApp(pfun, parg) =>
      arg match {
        case App(vfun, varg) => bind(parg, varg, sig, bind(pfun, vfun, sig, env))
        case _ => backtrack
      }
    case _ =>
      backtrack
  }

  def bind(pats: List[Pat], args: List[Expr], sig: Set[Var], env: Subst): Subst = (pats, args) match {
    case (Nil, Nil) => env
    case (pat :: pats, arg :: args) => bind(pats, args, sig, bind(pat, arg, sig, env))
    case _ => sys.error("argument length mismatch: " + pats.mkString(" ") + " and " + args.mkString(" "))
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