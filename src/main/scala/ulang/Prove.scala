package ulang

import arse._

class Prove(context: Context) {
  import context._

  def flatten(assume: List[Expr]): List[Expr] = {
    ???
  }

  def prove(assume: List[Expr], show: Expr): List[Expr] = show match {
    case True =>
      Nil
    case False =>
      List(show)
    case _ if assume contains show =>
      Nil
    case And(left, right) =>
      prove(assume, left) ++ prove(left :: assume, right)
    case Or(left, right) =>
      val _left = prove(assume, left)
      val _right = prove(assume, right)
      if (_left.isEmpty || _right.isEmpty) {
        Nil
      } else {
        List(Or(And(_left), And(_right)))
      }
    case Imp(left, right) =>
      prove(left :: assume, right)
    case Eqv(left, right) =>
      prove(right :: assume, left) ++ prove(left :: assume, right)
    case Eq(left, right) if left == right =>
      List()
    case _ =>
      List(show)
  }

  def apply(cs: Case, args: List[Expr]): Expr = cs match {
    case Case(pats, body) =>
      val env = bind(pats, args, Subst.empty)
      body subst env
  }

  def apply(cases: List[Case], args: List[Expr]): Expr = cases match {
    case Nil =>
      backtrack
    case cs :: rest =>
      { apply(cs, args) } or { apply(rest, args) }
  }

  def rewrite(expr: Expr): Expr = expr match {
    case id: Var if rewrites contains id =>
      { apply(rewrites(id), Nil) } or { expr }
    case Apps(id: Var, args) if rewrites contains id =>
      { apply(rewrites(id), args) } or { expr }
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

}