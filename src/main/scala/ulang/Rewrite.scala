package ulang

import arse._

class Rewrite(context: Context) {
  import context._

  case object Postponed extends Throwable

  def postpone() = {
    throw Postponed
  }

  def matches(pat: Pat, arg: Expr) = {
    try {
      println("try match " + pat + " with " + arg)
      val env = bind(pat, arg, Subst.empty)
      println("success: " + env)
      true
    } catch {
      case _: Backtrack | Postponed =>
        false
    }
  }

  def equal(e1: Expr, e2: Expr): Boolean = (e1, e2) match {
    case _ if e1 == e2 =>
      true
    case (Apps(tag1: Tag, args1), Apps(tag2: Tag, args2)) =>
      false
    case _ =>
      postpone()
  }

  def equal(p1: Pat, e2: Expr): Boolean = (p1, e2) match {
    case _ if p1 == e2 =>
      true
    case (UnApps(tag1: Tag, args1), Apps(tag2: Tag, args2)) =>
      false
    case _ =>
      postpone()
  }

  def bind(pat: Pat, arg: Expr, env: Subst): Subst = pat match {
    case Wildcard =>
      env

    case x: Var if env contains x =>
      if (equal(env(x), arg)) env
      else backtrack()

    case x: Var =>
      println("bind " + x + " to " + arg + " in " + env)
      env + (x -> arg)

    case tag: Tag =>
      if (equal(tag: Pat, arg)) env
      else backtrack()

    case UnApp(pfun, parg) =>
      arg match {
        case App(vfun, varg) =>
          bind(parg, varg, bind(pfun, vfun, env))
        // case pfun has a tag in function position and this is also a tag => backtrack()
        case _ =>
          if (!equal(pat, arg)) backtrack()
          else ???
      }

    case _ =>
      postpone()
  }

  def bind(pats: List[Pat], args: List[Expr], env: Subst): Subst = (pats, args) match {
    case (Nil, Nil) =>
      env
    case (pat :: pats, arg :: args) =>
      bind(pats, args, bind(pat, arg, env))
    case _ =>
      sys.error("argument length mismatch: " + pats.mkString(" ") + " and " + args.mkString(" "))
  }

  def apply(cs: Case, args: List[Expr]): Expr = cs match {
    case Case(pats, body) =>
      postpone()
      val env = Subst.empty
      rewrite(body, bind(pats, args, env))
  }

  def apply(cases: List[Case], arg: Expr): Expr = cases match {
    case Nil =>
      backtrack()

    case cs :: rest =>
      // XXX: if the first case does not MISMATCH, keep it and abort
      // apply(cs, arg) or apply(rest, arg)
      ???
  }

  def apply(fun: Expr, body: Expr, arg: Expr): Expr = {
    val res = body match {
      case Lam(cases) =>
        try {
          apply(cases, arg) or App(fun, arg)
        } catch {
          case Postponed => App(fun, arg)
        }
      case _ =>
        App(fun, arg)
    }
    res
  }

  def rewrite(cs: Case, lex: Subst): Case = cs match {
    case Case(pat, body) =>
      /* for a variable x in pat:
       * if it is in the domain of lex then this imposes an equality constraint on the argument passed to this case == lex(x)
       * otherwise, potentially rename it to avoid capturing variables in the range of lex
       */
      cs
  }

  def rewrite(exprs: List[Expr], lex: Subst): List[Expr] = {
    exprs map (rewrite(_, lex))
  }

  def rewrite(expr: Expr, lex: Subst): Expr = {
    val res = expr match {
      case x: Var if lex contains x =>
        lex(x)

      /* case x: Var if dyn contains x =>
        dyn(x) */

      case App(fun, arg) =>
        apply(fun, rewrite(fun, lex), rewrite(arg, lex))

      case Lam(cases) =>
        Lam(cases map (rewrite(_, lex)))

      case _ =>
        expr
    }
    if (res != expr) println("rewrite " + expr + " = " + res)
    res
  }
}