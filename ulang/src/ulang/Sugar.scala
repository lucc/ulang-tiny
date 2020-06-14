package ulang

/* object Binder extends ((Expr, Case) => App) {
  def apply(fun: Expr, cs: Case): App = {
    App(fun, Lam(List(cs)))
  }

  def unapply(expr: Expr) = expr match {
    case App(fun, Lam(List(cs))) => Some(fun, cs)
    case _ => None
  }
} */

class Vars(vars: List[Var]) {
  def rename(re: Map[Var, Var]) = vars map (_ rename re)
}

class Exprs(exprs: List[Expr]) {
  def free = Set(exprs flatMap (_.free): _*)
  def rename(re: Map[Var, Var]) = exprs map (_ rename re)
  def subst(su: Map[Var, Expr]) = exprs map (_ subst su)
}

class Cases(cases: List[Case]) {
  def free = Set(cases flatMap (_.free): _*)
  def bound = Set(cases flatMap (_.bound): _*)
  def rename(re: Map[Var, Var]) = cases map (_ rename re)
  def subst(su: Map[Var, Expr]) = cases map (_ subst su)
}

class Cases1(cases: List[Case1]) {
  def pats = cases map (_.pat)
  def args = cases map (_.arg)
  def free = Set(cases flatMap (_.free): _*)
  def bound = Set(cases flatMap (_.bound): _*)
  def rename(a: Map[Var, Var], re: Map[Var, Var]) = cases map (_ rename (a, re))
  def subst(a: Map[Var, Var], su: Map[Var, Expr]) = cases map (_ subst (a, su))
}

object Apps extends ((Expr, List[Expr]) => Expr) {
  def apply(fun: Expr, args: List[Expr]): Expr = {
    args.foldLeft(fun)(App)
  }

  def flatten(expr: Expr, args: List[Expr]): (Expr, List[Expr]) = expr match {
    case App(fun, arg) =>
      flatten(fun, arg :: args)
    case _ =>
      (expr, args)
  }

  def unapply(expr: Expr): Option[(Expr, List[Expr])] = {
    Some(flatten(expr, Nil))
  }
}

object Objs extends ((Data, List[Val]) => Val) {
  def apply(fun: Data, args: List[Val]): Val = {
    args.foldLeft(fun)(Obj)
  }

  def flatten(any: Data, args: List[Val]): (Data, List[Val]) = any match {
    case Obj(fun, arg) =>
      flatten(fun, arg :: args)
    case _ =>
      (any, args)
  }

  def unapply(any: Data): Option[(Data, List[Val])] = {
    Some(flatten(any, Nil))
  }
}

class Unary[A <: Id](val op: A) {
  def unapply(e: Expr) = e match {
    case App(`op`, arg) => Some(arg)
    case _ => None
  }

  def unapply(v: Val) = v match {
    case Obj(`op`, arg) => Some(arg)
    case _ => None
  }

  def apply(arg: Expr) = {
    App(op, arg)
  }
}

class Binary[A <: Id](val op: A) {
  def unapply(e: Expr) = e match {
    case App(App(`op`, arg1), arg2) => Some((arg1, arg2))
    case _ => None
  }

  def unapply(v: Val) = v match {
    case Obj(Obj(`op`, arg1), arg2) => Some((arg1, arg2))
    case _ => None
  }

  def apply(arg1: Expr, arg2: Expr): Expr = {
    App(App(op, arg1), arg2)
  }

  def apply(args: List[Expr], zero: Expr): Expr = {
    args.foldRight(zero)(apply)
  }

  def apply(zero: Expr, args: List[Expr]): Expr = {
    args.foldLeft(zero)(apply)
  }
}
