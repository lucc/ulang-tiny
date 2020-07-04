package ulang

import arse._

object Prove {
  import context._
  import Simp._

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

  def elim(intro: Intro, target: Expr, ant: List[Expr], suc: List[Expr], hyp: Option[Expr]): Proof = {
    // all variables of the introduction rule need to be fresh
    val fresh = Expr.fresh(intro.free)
    val _intro = intro rename fresh
    val Intro(rec, pre, post) = _intro

    val Apps(fun1, args1) = post
    val Apps(fun2, args2) = target
    assert(fun1 == fun2) // satisifed from the pattern match
    assert(args1.length == args2.length)

    val eqs = Eq.zip(args1, args2)
    val _ant = And(ant)
    val _suc = Or(suc)

    // variables that may be generalized in the induction
    val free = ant.free ++ suc.free ++ target.free

    hyp match {
      case Some(pat) =>
        val hyps = rec map {
          prem =>
            val Apps(fun0, args0) = prem
            assert(fun0 == fun2)
            assert(args0.length == args2.length)
            val req = Eq.zip(args0, args2)
            val _eqs = And(req)
            val hyp = All(free.toList, imp(and(_eqs, _ant), _suc))
            println("premise:    " + prem)
            println("hypothesis: " + hyp)
            and(prem, hyp)
        }
        println()
        auto(eqs ++ ant ++ hyps, _suc, Goal.empty)
      case None =>
        auto(eqs ++ ant, _suc, Goal.empty)
    }
  }

  def induct(pat: Expr, goal: Open, hyp: Boolean): List[Proof] = {
    val Open(eqs, ant, suc) = goal

    val pos = ant.indexWhere(_ <= pat)
    ensure(pos >= 0, "no such formula: " + pat)
    val (target, rest) = ant extract pos

    // println("found inductive focus " + found + " for " + pat + " with " + env)
    val (gen, kind, intros) = unwrap(inds find (target <= _._1), "no inductive rule for: " + target)
    ensure(kind == Least, "not an inductive rule: " + kind)

    val rec = if (hyp) Some(gen) else None
    intros map (elim(_, target, rest ++ Eq.zip(eqs), suc, rec))
  }

  def prove(goal: Open, tactic: Tactic): Proof = tactic match {
    /* case Split(pat) =>
      val prems = ind(pat, goal, hyp = false)
      Step(prems, goal, tactic) */
    case Induct(pat, Least) =>
      val prems = induct(pat, goal, hyp = true)
      Step(prems, goal, tactic)
    /* case Ind(pat, Greatest) =>
      ??? */
    case _ =>
      goal
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
}