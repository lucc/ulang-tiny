package ulang

import arse._

object Prove {
  import context._
  import Rewrite._

  def prove(ant: List[Expr], suc: Expr, proof: Option[Tactic]): Proof = {
    val goal = auto(ant, suc, Goal.empty)

    (goal, proof) match {
      case (open: Open, Some(tactic)) =>
        prove(open, tactic)
      case (step @ Step(List(prem: Open), concl, auto), Some(tactic)) =>
        Step(List(prove(prem, tactic)), concl, auto)
      case (_, Some(tactic)) =>
        fail("cannot apply: " + tactic + " (goal is closed)")
      case (goal, _) =>
        goal
    }
  }

  /* def elim(intro: Intro, target: Expr, eqs: Subst, ant: List[Expr], suc: List[Expr], hyp: Option[Expr]): Proof = {
    val fresh = Expr.fresh(intro.free)
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
        val (found, rest) = findAll(pat, pre)
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

  def ind(pat: Expr, goal: Open, hyp: Boolean): List[Proof] = {
    val free = goal.free
    val Open(eqs, ant, suc) = goal
    val (found, env, rest) = { find(pat, ant) } or { sys.error("no formula: " + pat) }
    ??? // TODO ensure that free is not bound by env
    // if (!env.isEmpty)
    //   sys.error("can't introduce new vars here: " + env.keys.mkString(" "))
    // val (gen, kind, intros) = fix(pat)
    // val rec = if (hyp) Some(gen) else None
    // intros map (elim(_, found, eqs, rest, suc, rec))
    ???
  } */

  def prove(goal: Open, tactic: Tactic): Proof = tactic match {
    /* case Split(pat) =>
      val prems = ind(pat, goal, hyp = false)
      Step(prems, goal, tactic)
    case Ind(pat, Least) =>
      val prems = ind(pat, goal, hyp = true)
      Step(prems, goal, tactic)
    case Ind(pat, Greatest) =>
      ??? */
    case _ => ???
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
}