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

object Cut extends Ternary("Cut")

object Inst extends Ternary("Inst")
object Witness extends Binary("Witness")
object Unfold extends Unary("Unfold") {
  def suitable(fun: Id, args: List[Expr]): Boolean =
    context.funs.contains(fun) && {
      val cases = context.funs(fun)
      cases.length == 1 &&
      cases.head.pats.length == args.length &&
      cases.head.pats.forall(_.isInstanceOf[Id])
    } || context.consts.contains(fun) && args.length == 0
  def unfold(fun: Id, args: List[Expr]): Expr = {
    if (context.funs contains fun) {
      val cs = context.funs(fun).head
      val mapping = cs.pats.zip(args).foldLeft(Map.empty[Id, Expr]) {
        case (m, (pat: Id, arg)) => m + (pat -> arg)
      }
      cs.body.subst(mapping)
    } else {
      context.consts(fun)
    }
  }
}
object DefEq extends Binary("Def")
object DefIntro extends Binary("Intro")
object DefInd extends Binary("Ind")
object DefCoind extends Binary("Coind")
