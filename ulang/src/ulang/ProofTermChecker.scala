package ulang

import PartialFunction.cond
import util.Try
import ulang.{TypeInference => infer}

object ProofTermChecker {

  case class Error(msg: String) extends Exception(msg)

  /** Check a proof
   *
   *  The proof is assumed to have no global assumptions.
   */
  def checkSafe(proof: Expr, goal: Expr): Option[String] =
    checkSafe(Map(), proof, goal)

  def checkSafe(ctx: Map[Id, Expr], proof: Expr, goal: Expr): Option[String] =
    try {
      check(ctx, proof, goal)
      None
    } catch {
      case Error(msg) => Some(msg)
    }

  /** Check a proof with context
   *
   *  This implements checking of proofs according to the
   *  Brouwer-Heyting-Kolmogorov interpretation of proofs (see Schwichtenberg
   *  & Wainer "Proofs and Computations", 2012, CUP, p313-314).
   *
   *  If a proof should be allowed to use axioms, they need to be present in
   *  the context.
   */
  def check(ctx: Map[Id, Expr], proof: Expr, goal: Expr) {
    (proof, goal) match {
      case (Sorry, _) =>
        println("assume")
        for((id, expr) <- ctx)
          println(s"  $id := $expr;")
        println("show")
          println(s"  $goal")
          throw Error("Unfinished proof (sorry)")

      // Proof by assumption has to be the first case, this makes it possible
      // to match against any goal (even "False").  If the given goal is not
      // in the context we fall through to the other cases.
      case (id: Id, _) if ctx contains id =>
        if (!alphaEqui(ctx(id), goal))
          throw Error(f"Assumption $id does not match the goal $goal")
      case (id: Id, _) if context.lemmas contains id =>
        if (!alphaEqui(context.lemmas(id), goal))
          throw Error(f"Lemma $id does not match the goal $goal")
      case (id: Id, _) if context.funs contains id =>
        check(ctx, Lam(context.funs(id)), goal)
      case (Id("elim", None), _) =>
        throw Error("The special function name 'elim' can only be used in applications.")
      case (Id("intro", None), _) =>
        throw Error("The special function name 'intro' can only be used in applications.")

      // special cases
      case (True, True) =>  // we use "True" to represent a trivial proof
      case (intro(pred, index), _) => throw Error("Generation of intro axioms is not yet implemented")
      case (elim(pred), _) => throw Error("Generation of elim axioms is not yet implemented")

      // propositional logic: introduction rules
      case (Pair(p1, p2), And(f1, f2)) =>
        check(ctx, p1, f1)
        check(ctx, p2, f2)
      case (LeftE(p), Or(f, _)) => check(ctx, p, f)
      case (RightE(p), Or(_, f)) => check(ctx, p, f)
      case (Lam(cases), Imp(ant, cons)) =>
        cases map {
          case Case(List(p), body) => check(bind(ctx, p, ant), body, cons)
          case Case(p::ps, body) => check(bind(ctx, p, ant), Lam1(ps, body), cons)
        }

      // predicate logic introduction rules
      case (Witness(id1, witness, p), Ex(id2, matrix)) if id1 == id2 =>
        check(ctx, p, matrix.subst(Map(id1 -> witness)))
      case (All(param, body), All(id, matrix)) =>
        // For all-introduction there is a variable condition: the bound
        // variable must not occur free in any open assumption in body.
        // We allow alpha equivalence here in the same step.  In a stricter
        // setting the formula must quantify over the free variable without
        // renameing, and the alpha renameing can be done later on if the new
        // name does not occur free in the formula.
        val openFree = Expr free ctx.values
        if (openFree.contains(param) || (id != param && body.free.contains(id)))
          throw Error("Capturing variable " + param)
        else
          check(ctx, body, matrix.rename(Map(id -> param)))

      // cut rule
      case (Cut(phi, pt1, LamId(id, pt2)), _) =>
        check(ctx, pt1, phi)
        check(ctx + (id -> phi), pt2, goal)

      // TODO predicate logic elimination rules?

      case (Inst(pt, t, pt2), _) =>
        infer(ctx, pt) match {
          case Right(All(x, phi)) =>
            check(ctx, pt2, Imp(phi.subst(Map(x -> t)), goal))
          case Right(t) =>
            throw Error("Inst needs a forall formula, not " + t)
          case Left(text) =>
            throw Error(text)
        }

      // modus ponens is checked by infering the type of the argument and then
      // rerouting the check to Imp introduction.
      case (App(p@Lam(cases), arg), _) =>
        infer(ctx, arg) match {
          case Left(err) => throw Error(err)
          case Right(t) => check(ctx, p, Imp(t, goal))
        }

      // Defined functions are shadowed by assumptions from the context and
      // lemas but these are checked in the case below.
      case (App(f: Id, arg), _) if context.funs.contains(f)
                                && !ctx.contains(f)
                                && !context.lemmas.contains(f) =>
        // defined functions are checked like lambda terms
        check(ctx, App(Lam(context.funs(f)), arg), goal)

      // general applications need type inference for both sides to match the
      // types
      case (App(f, arg), _) =>
        val t1 = infer(ctx, f) match { case Right(t) => t
                                       case Left(err) => throw Error(err) }
        val t2 = infer(ctx, arg) match { case Right(t) => t
                                         case Left(err) => throw Error(err) }
        t1 match {
          case All(x, Imp(ant, cons)) if apply(ant, t2, cons) == goal =>  // TODO alpha equi
          case Imp(`t2`, `goal`) =>  // term equality
          case Imp(ant, cons) =>
            (alphaEqui(ant, t2), alphaEqui(cons, goal)) match {
              case (true, true) =>
              case (true, false) => throw Error(f"$cons does not match $goal")
              case (false, _) => throw Error(f"Argument $ant does not match $t2")
            }
          case _ => throw Error(f"Can not apply $t1 to $t2")
        }

      // match expressions can be converted to function applications
      case (Match(args, cases), _) =>
        check(ctx, Apps(Lam(cases), args), goal)

      // False is implicit here
      case _ => throw Error(f"Proof term $proof does not match the formula $goal.")
    }
  }

  /**
   * not at all general attempt to normalizate formulas before placing these into context,
   * this code should be merged with apply probably
   */
  def simpleBetaReductions(expr: Expr): Expr = {
    expr match {
      case App(fun, arg) =>
        (simpleBetaReductions(fun), simpleBetaReductions(arg)) match {
          case (LamId(id, body), arg) =>
            body subst (Map(id -> arg))
          case (fun, arg) =>
            App(fun, arg)
        }
      case Bind(quant, args, body) =>
        Bind(quant, args, simpleBetaReductions(body))
      case _ =>
        expr
    }
  }

  /**
   * extend a context by binding argument types to parameter variables
   */
  def bind(ctx: Map[Id, Expr], pat: Expr, assm: Expr): Map[Id,Expr] =
    (pat, assm) match {
      case (p: Id, _) => ctx + (p -> simpleBetaReductions(assm))
      case (Pair(p1, p2), And(a1, a2)) => bind(bind(ctx, p1, a1), p2, a2)
      case (LeftE(p), Or(f, _)) => bind(ctx, p, f)
      case (RightE(p), Or(_, f)) => bind(ctx, p, f)
      case (Witness(x1, w, p), Ex(x2, matrix)) if x1 == x2 =>
        bind(bind(ctx, w, x1), p, matrix.subst(Map(x1 -> w)))
    }
  def bind(ctx: Map[Id, Expr], cases: List[Case], assm: Expr): List[Map[Id, Expr]] =
    cases.map(c => bind(ctx, c.pats.head, assm))
  /**
   * Bind an argument term to a pattern
   */
  def apply(pat: Expr, arg: Expr, body: Expr): Expr =
    (pat, arg) match {
      case (p: Id, _) => body.subst(Map(p -> arg))
      case (App(id1: Id, term1), App(id2: Id, term2))
        if context.isTag(id1) && id1 == id2 => apply(term1, term2, body)
      case (App(f1, a1), App(f2, a2)) => apply(a1, a2, apply(f1, f2, body))
      // TODO apply with apha equivalence
      //case (Bind(q1, id1, body1), Bind(q2, id2, body2)) if q1 == q2 =>
      //  throw new RuntimeException("apply can not check alpha equivalence yet")
    }
  def apply(cases: List[Case], arg: Expr): List[Expr] = cases.map {
    case Case(List(p), body) => apply(p, arg, body)
    case Case(p::ps, body) => apply(p, arg, Lam1(ps, body))
  }


  // Functions that have been suggested by Gidon but are not yet implemented.
  //def elim(ctx: Map[Id, Expr], pats: List[Expr], body: Expr, goal: Expr): Boolean =
  //  (pats, goal) match {
  //    case (Nil, _) => check(ctx, body, goal)
  //    case (pat::rest, Imp(assm, concl)) =>
  //      val ctx_ = bind(ctx, pat, assm)
  //      elim(ctx_, rest, body, concl)
  //  }
  //def elim(ctx: Map[Id, Expr], cs: Case, goal: Expr): Boolean = ???
  //def elim(ctx: Map[Id, Expr], cases: List[Case], goal: Expr): Boolean =
  //  cases.forall(elim(ctx, _, goal))
  //def apply(assumption: Map[Id, Expr], fun: Expr, arg: Expr): Expr =
  //  (fun, arg) match {
  //    case (LamId(v, body), _) => body.subst(Map(v -> arg))
  //    case (All(x, matrix), _) =>
  //       (forall x -> p) t == p[x -> t]
  //       (a ==> b) a       == b
  //  case _ => App(fun, arg)
  //}
}

/**
 * a simple attempt at alpha equivalence
 *
 * We use De Bruijn indices but we do not rewrite the terms.  Instead we
 * compare the structure of the given Ulang terms and use two contexts to map
 * variable names in the two terms to "indices".  As indices we use new Scala
 * Objects ensuring that no two indices compare equal.  Every time we decend
 * into a binding term constructor we map the two bound names to the same new
 * Object.
 */
object alphaEqui extends ((Expr, Expr) => Boolean) {
  type Ctx = Map[Id, Object]
  def apply(left: Expr, right: Expr) = eqi(Map(), Map(), left, right)
  def eqi(ctxL: Ctx, ctxR: Ctx, left: Expr, right: Expr): Boolean =
    (left, right) match {
      case (l: Id, r: Id) =>
        // if both sides have bound the variable they should have bound it at
        // the same structural position
        if (ctxL.contains(l) && ctxR.contains(r)) ctxL(l) == ctxR(r)
        // if only one side did bind this varialble they are not equal
        else if (ctxL.contains(l) || ctxR.contains(r)) false
        // global names, free variables, etc
        else l == r
      case (Lam1(l::ls, bodyL), Lam1(r::rs, bodyR)) =>
        val bodyL2 = if (ls == Nil) bodyL else Lam1(ls, bodyL)
        val bodyR2 = if (rs == Nil) bodyR else Lam1(rs, bodyR)
        bind(l, r) match {
          case None => false
          case Some((l, r)) => eqi(ctxL ++ l, ctxR ++ r, bodyL2, bodyR2)
        }
      case (Lam(casesL), Lam(casesR)) =>
        casesL zip casesR forall(p =>
            eqi(ctxL, ctxR, Lam(List(p._1)), Lam(List(p._2))))
      case (Bind(ql, l, bodyL), Bind(qr, r, bodyR)) if ql == qr =>
        val marker = new Object()
        eqi(ctxL + (l -> marker), ctxR + (r -> marker), bodyL, bodyR)
      case (App(funL, argL), App(funR, argR)) =>
        eqi(ctxL, ctxR, funL, funR) && eqi(ctxL, ctxR, argL, argR)
      case _ => false
    }
  def bind(left: Expr, right: Expr): Option[(Ctx, Ctx)] =
    (left, right) match {
      case (left: Id, right: Id)
        if !context.isTag(left) && !context.isTag(right) =>
          val marker = new Object()
          Some((Map(left -> marker), Map(right -> marker)))
      case (App(funL: Id, left), App(funR: Id, right)) =>
        if (context.isTag(funL) && funL == funR) bind(left, right)
        else None
      case (App(funL, argL), App(funR, argR)) =>
        for {
          (left1, right1) <- bind(funL, funR)
          (left2, right2) <- bind(argL, argR)
        } yield (left1 ++ left2, right1 ++ right2)
      case _ => None
    }
}
