package ulang

object Eval {
  var dyn: Env = Map()

  def equal(v1: Val, v2: Val): Boolean = {
    const(v1) == const(v2)
  }

  def bind(pat: Pat, arg: Val, env: Env): Env = pat match {
    case Wildcard =>
      env
    case Strict(pat) =>
      bind(pat, const(arg), env)
    case id: Id if env contains id =>
      if (equal(env(id), arg)) env
      else backtrack
    case id: Id =>
      env + (id -> arg)
    case tag: Tag =>
      force(arg) match {
        case `tag` => env
        case _ => backtrack
      }
    case UnApp(pat1, pat2) =>
      force(arg) match {
        case Obj(arg1, arg2) => bind(pat2, arg2, bind(pat1, arg1, env))
        case _ => backtrack
      }
    case _ =>
      backtrack
  }

  def bind(pats: List[Pat], args: List[Val], env: Env): Env = (pats, args) match {
    case (Nil, Nil) => env
    case (pat :: pats, arg :: args) => bind(pats, args, bind(pat, arg, env))
    case _ => sys.error("argument length mismatch: " + pats.mkString(" ") + " and " + args.mkString(" "))
  }

  def apply(cs: Case, args: List[Val], lex: Env): Norm = cs match {
    case Case(pats, body) =>
      norm(body, bind(pats, args, lex))
  }

  def apply(fun: Curry, cases: List[Case], args: List[Val], lex: Env): Norm = cases match {
    case Nil =>
      sys.error("cannot apply " + fun + " to " + args.mkString(" "))
    case cs :: rest =>
      { apply(cs, args, lex) } or { apply(fun, rest, args, lex) }
  }

  def apply(fun: Curry): Norm = {
    if (fun.isComplete) {
      val cases = fun.cases
      val args = fun.rargs.reverse
      val lex = fun.lex
      apply(fun, cases, args, lex)
    } else {
      fun
    }
  }

  def push(fun: Norm, arg: Val): Norm = fun match {
    case data: Data => Obj(data, arg)
    case Curry(cases, rargs, lex) => apply(Curry(cases, arg :: rargs, lex))
    case _ => sys.error("not a function: " + fun)
  }

  def force(arg: Val): Norm = arg match {
    case defer: Defer => defer.norm
    case norm: Norm => norm
  }

  def defer(expr: Expr, lex: Env): Val = {
    Defer(expr, lex)
  }

  def const(arg: Val): Data = arg match {
    case lzy: Defer => const(lzy.norm)
    case tag: Tag => tag
    case Obj(fun, arg) => Obj(const(fun), const(arg))
    case _ => sys.error("not constant: " + arg)
  }

  def norm(expr: Expr, lex: Env): Norm = expr match {
    case tag: Tag =>
      tag
    case id: Id =>
      if (lex contains id) force(lex(id))
      else if (dyn contains id) force(dyn(id))
      else sys.error("unbound identifier: " + id + " in " + lex + " and " + dyn)
    case Lam(cases) =>
      Curry(cases, Nil, lex)
    case App(fun, arg) =>
      push(norm(fun, lex), defer(arg, lex))
    case Let(eqs, body) =>
      ???
    case Match(arg, cases) =>
      ???
    case Ite(test, left, right) =>
      strict(test, lex) match {
        case True => norm(left, lex)
        case False => norm(right, lex)
        case test => sys.error("not boolean: " + test + " = " + test)
      }
  }

  def strict(expr: Expr, lex: Env): Norm = {
    const(norm(expr, lex))
  }
}