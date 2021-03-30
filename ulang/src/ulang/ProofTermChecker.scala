package ulang

object ProofTermChecker {

  /** Check a proof
   *
   *  The proof is assumed to have no global assumptions.
   */
  def check(proof: Expr, goal: Expr): Option[String] = check(Map(), proof, goal)

  /** Check a proof with context
   *
   *  This implements checking of proofs according to the
   *  Brouwer-Heyting-Kolmogorov interpretation of proofs (see Schwichtenberg
   *  & Wainer "Proofs and Computations", 2012, CUP, p313-314).
   *
   *  If a proof should be allowed to use axioms, they need to be present in
   *  the context.
   */
  def check(ctx: Map[Id, Expr], proof: Expr, goal: Expr): Option[String] =
    (proof, goal) match {

      // Proof by assumption has to be the first case, this makes it possible
      // to match against any goal (even "False").  If the given goal is not
      // in the context we fall through to the other cases.
      case (id: Id, _) if ctx contains id =>
        if (ctx(id) == goal) None
        else Some(f"Assumption $id does not match the goal $goal")
      case (id: Id, _) if context.lemmas contains id =>
        if (context.lemmas(id) == goal) None
        else Some(f"Lemma $id does not match the goal $goal")
      case (id: Id, _) if context.funs contains id =>
        check(ctx, Lam(context.funs(id)), goal)
      case (Id("elim", None), _) =>
        Some("The special function name 'elim' can only be used in applications.")
      case (Id("intro", None), _) =>
        Some("The special function name 'intro' can only be used in applications.")

      // special cases
      case (True, True) => None // we use "True" to represent a trivial proof
      case (intro(pred, index), _) => Some("Generation of intro axioms is not yet implemented")
      case (elim(pred), _) => Some("Generation of elim axioms is not yet implemented")

      // propositional logic: introduction rules
      case (Pair(p1, p2), And(f1, f2)) =>
        check(ctx, p1, f1) orElse check(ctx, p2, f2)
      case (LeftE(p), Or(f, _)) => check(ctx, p, f)
      case (RightE(p), Or(_, f)) => check(ctx, p, f)
      // special case for lambdas with one pattern only
      case (Lam1(List(pat), body), Imp(ant, cons)) =>
        check(bind(ctx, pat, ant), body, cons)
      // special case for lambdas with one case only
      case (Lam1(pat::pats, body), Imp(ant, cons)) =>
        check(bind(ctx, pat, ant), Lam1(pats, body), cons)
      // special case for multible cases but with only one pattern each
      case (Lam(cases), Imp(ant, cons)) if cases.forall(_.pats.length == 1) =>
        val checks = cases.map(c => check(bind(ctx, c.pats.head, ant), c.body, cons))
        val errs = checks.filter(_.isDefined)
        if (errs.isEmpty) None
        else Some(errs map(_.get) mkString "\n")

      // predicate logic introduction rules
      case (Witness(id1, witness, p), Ex(id2, matrix)) if id1 == id2 =>
        check(ctx, p, matrix.subst(Map(id1 -> witness)))
      case (All(param, body), All(id, matrix)) =>
        // For all-introduction there is a variable condition: the bound
        // variable must not occur free in any open assumption in body.
        val openFree = Expr free ctx
        if (openFree contains id) Some("Capturing variable " + id)
        else check(ctx, body, matrix.rename(Map(id -> param)))

      // TODO predicate logic elimination rules?

      case (Inst(pt, t, pt2), _)
      if (infer(ctx, pt) match {case Right(All(_, _)) => true; case _ => false}) =>
        val Right(All(x, phi)) = infer(ctx, pt)
        println(f"TODO: $ctx ⊢ $pt2 : ${Imp(phi.subst(Map(x -> t)), goal)}")
        check(ctx, pt2, Imp(phi.subst(Map(x -> t)), goal))

      // different cases for modus ponens
      case (App(LamId(id, body), arg), _) =>
        check(ctx, body.subst(Map(id -> arg)), goal)
      // This must have more than one Id because of previous case
      case (App(LamIds(id::ids, body), arg), _) =>
        check(ctx, LamIds(ids, body).subst(Map(id -> arg)), goal)
      case (App(Lam1(pat, body), arg), _) =>
        // if we can apply the argument to the patterns we do that directly
        try {
          pat match {
            case Nil => throw new Exception("This should never happen")
            case List(p) => check(ctx, apply(p, arg, body), goal)
            case p::ps => check(ctx, apply(p, arg, Lam1(ps, body)), goal)
          }
        } catch {
          // in case that fails (i.e. because the argument was an Id and the
          // pattern was complex) then we can still try to bind the argument
          // type to the pattern in the context and leave the body unchanged
          case _: MatchError =>
            infer(ctx, arg) match {
              case Left(err) => Some(err)
              case Right(t) =>
                pat match {
                  case Nil => throw new Exception("This should never happen")
                  case List(p) => check(bind(ctx, p, t), body, goal)
                  case p::ps => check(bind(ctx, p, t), Lam1(ps, body), goal)
                }
            }
        }
      case (App(Lam(cases), arg), _) =>
        infer(ctx, arg) match {
          case Left(err) => Some(err)
          case Right(t) =>
            val proofs = apply(cases, arg)
            val ctxs = bind(ctx, cases, t)
            ctxs.zip(proofs).map { case (c, p) => check(c, p, goal)
            }.foldLeft(None: Option[String])((a,o) => a orElse o)
        }

      case (App(f: Id, arg), _) if ctx.contains(f) || context.lemmas.contains(f) =>
        val t1 = ctx.getOrElse(f, context.lemmas(f))
        t1 match {
          case All(x, matrix) if matrix.subst(Map(x -> arg)) == goal => None
          case _ =>
            infer(ctx, arg) match {
              case Left(err) => Some(err)
              case Right(t2) =>
                if (t1 == Imp(t2, goal)) None
                else if (t2.isInstanceOf[Id] && t1 == All(t2.asInstanceOf[Id], goal)) None
                else Some(f"Formulas do not match: $t1 should be equal to $t2 ==> $goal or forall $t2. $goal")
            }
        }

      case (App(f: Id, arg), _) if context.funs contains f =>
        // defined functions are checked like lambda terms
        check(ctx, App(Lam(context.funs(f)), arg), goal)

      // general applications need type inference for either the left or the
      // right side.  We use the left side for now.
      case (App(f, arg), _) =>
        infer(ctx, arg) match {
          case Right(ty) if check(ctx, f, Imp(ty, goal)).isEmpty => None
          case Right(ty: Id) => check(ctx, f, All(ty, goal))
          case Left(err1) =>
            infer(ctx, f) match {
              case Right(Imp(a, `goal`)) => check(ctx, a, arg)
              case Right(All(v, matrix)) if matrix.subst(Map(v -> arg)) == goal => None
              case Left(err2) => Some(err1 + "\n" + err2)
            }
        }

      // match expressions can be converted to function applications
      case (Match(args, cases), _) =>
        check(ctx, Apps(Lam(cases), args), goal)

      // False is implicit here
      case _ => Some(f"Proof term $proof does not match the formula $goal.")
    }

  val infer = TypeInference(_, _)

  /**
   * extend a context by binding argument types to parameter variables
   */
  def bind(ctx: Map[Id, Expr], pat: Expr, assm: Expr): Map[Id,Expr] =
    (pat, assm) match {
      case (p: Id, _) => ctx + (p -> assm)
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
