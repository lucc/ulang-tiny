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

class Ids(ids: List[Id]) {
  def rename(re: Map[Id, Id]) = ids map (_ rename re)
}

class Exprs(exprs: List[Expr]) {
  def free = Set(exprs flatMap (_.free): _*)
  def rename(re: Map[Id, Id]) = exprs map (_ rename re)
  def subst(su: Map[Id, Expr]) = exprs map (_ subst su)
}

class Cases(cases: List[Case]) {
  def free = Set(cases flatMap (_.free): _*)
  def bound = Set(cases flatMap (_.bound): _*)
  def rename(re: Map[Id, Id]) = cases map (_ rename re)
  def subst(su: Map[Id, Expr]) = cases map (_ subst su)
}

class Cases1(cases: List[Case1]) {
  def pats = cases map (_.pat)
  def args = cases map (_.arg)
  def free = Set(cases flatMap (_.free): _*)
  def bound = Set(cases flatMap (_.bound): _*)
  def rename(a: Map[Id, Id], re: Map[Id, Id]) = cases map (_ rename (a, re))
  def subst(a: Map[Id, Id], su: Map[Id, Expr]) = cases map (_ subst (a, su))
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

class Unary(val op: Id) {
  def this(name: String) = this(Id(name))

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

class Binary(val op: Id) {
  def this(name: String) = this(Id(name))

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

class Ternary(val op: Id) {
  def this(name: String) = this(Id(name))

  def unapply(e: Expr) = e match {
    case App(App(App(`op`, arg1), arg2), arg3) => Some((arg1, arg2, arg3))
    case _ => None
  }

  def unapply(v: Val) = v match {
    case Obj(Obj(Obj(`op`, arg1), arg2), arg3) => Some((arg1, arg2, arg3))
    case _ => None
  }

  def apply(arg1: Expr, arg2: Expr, arg3: Expr): Expr = {
    App(App(App(op, arg1), arg2), arg3)
  }
}

object Eq extends Binary("==") {
  def zip(left: List[Expr], right: List[Expr]): List[Expr] = {
    if (left.length != right.length)
      sys.error("length mismatch: " + left + " " + right)
    zip(left zip right)
  }

  def zip(pairs: Iterable[(Expr, Expr)]): List[Expr] = {
    val eqs = pairs map { case (a, b) => Eq(a, b) }
    eqs.toList
  }

  def split(expr: Expr) = expr match {
    case Eq(lhs, rhs) =>
      (lhs, rhs)
    case Eqv(lhs, rhs) =>
      (lhs, rhs)
    case Not(lhs) =>
      (lhs, False)
    case lhs =>
      (lhs, True)
  }
}

object True extends Id("True")
object False extends Id("False")

object Zero extends Id("0")
object Succ extends Unary("+1")

object Not extends Unary("not")

object And extends Binary("/\\") {
  def apply(args: List[Expr]): Expr = args match {
    case Nil => True
    case _ => args.reduce(apply(_, _))
  }
}

object Or extends Binary("\\/") {
  def apply(args: List[Expr]): Expr = args match {
    case Nil => False
    case _ => args.reduce(apply(_, _))
  }
}

object Imp extends Binary("==>") {
  def split(expr: Expr) = expr match {
    case Imp(Apps(And.op, ant), suc) =>
      (ant, suc)
    case Imp(ant, suc) =>
      (List(ant), suc)
    case suc =>
      (Nil, suc)
  }
}

object Sorry extends Id("sorry")
object Eqv extends Binary("<=>")
object Pair extends Binary(",")
object LeftE extends Unary("Left")
object RightE extends Unary("Right")
object Assumption extends Id("Assumption")

// Special function names to manage intro and elim axioms of inductive
// predicates
object intro extends Binary("intro")
object elim extends Unary("elim")

object Inst extends Ternary("Inst")
object Witness extends Ternary("Witness") {
  def apply(x: Id, wit: Expr, body: Expr) =
    App(App(App(Id("Witness"), x), wit), body)
  override def unapply(e: Expr): Option[(Id, Expr, Expr)] = e match {
    case App(App(App(Id("Witness", None), x: Id), arg2), arg3) =>
      Some((x, arg2, arg3))
    case _ => None
  }
}
