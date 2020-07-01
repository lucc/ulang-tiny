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

  def elim(intro: Intro, target: Expr, locals: Subst, ant: List[Expr], suc: List[Expr], hyp: Option[Expr]): Proof = {
    val fresh = Expr.fresh(intro.free)
    val _intro = intro rename fresh
    val Intro(rec, pre, post) = _intro

    val Apps(fun1, args1) = post
    val Apps(fun2, args2) = target
    assert(fun1 == fun2) // satisifed from the pattern match
    assert(args1.length == args2.length)

    val pairs = (args1 zip args2) ++ locals
    val eqs = Eq.zip(pairs)
    val _suc = Or(suc)

    def collapse(left: List[Expr], right: List[Expr]): List[(Id, Expr)] = (left, right) match {
      case (Nil, Nil) => Nil
      case ((x: Id) :: left, e :: right) => (x, e) :: collapse(left, right)
      case (Apps(fun1, args1) :: left, Apps(fun2, args2) :: right) if fun1 == fun2 => collapse(args1 ++ left, args2 ++ right)
      case (x :: _, e :: _) if x != e => sys.error("can't instantiate inductive premise for: " + x + " == " + e)
    }

    hyp match {
      case Some(pat) =>
        val hyps = rec map {
          prem =>
            val Apps(fun0, args0) = prem
            val inst = collapse(args2, args0)
            val hyp = imp(And(ant), _suc)
            val _hyp = hyp subst inst.toMap
            _hyp
        }
        auto(eqs ++ ant ++ hyps, _suc, Goal.empty)
      case None =>
        auto(eqs ++ ant, _suc, Goal.empty)
    }
  }

  def induct(pat: Expr, goal: Open, hyp: Boolean): List[Proof] = {
    val Open(eqs, ant, suc) = goal
    val (found, env, rest) = { find(pat, ant) } or { sys.error("no such formula: " + pat) }
    println("found inductive focus " + found + " for " + pat + " with " + env)
    val (gen, kind, intros) = unwrap(inds find (pat <= _._1), "no inductive rule for: " + pat)
    ensure(kind == Least, "not an inductive rule: " + kind)
    val rec = if (hyp) Some(gen) else None
    intros map (elim(_, found, eqs ++ env, rest, suc, rec))
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