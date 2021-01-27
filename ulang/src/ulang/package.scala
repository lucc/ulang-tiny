package object ulang {
  import arse._

  type Env = Map[Id, Val]
  type Subst = Map[Id, Expr]

  implicit def toIds(ids: List[Id]) = new Ids(ids)
  implicit def toExprs(exprs: List[Expr]) = new Exprs(exprs)
  implicit def toCases(cases: List[Case]) = new Cases(cases)
  implicit def toCases1(cases: List[Case1]) = new Cases1(cases)

  object context extends Context /* {
    // convenience ...
    notation(List("==", "!="), Infix(Non, 6))
    notation(List("==>") Infix(Non, 4))
  } */

  def fail(msg: String) = {
    sys.error(msg)
  }

  def ensure(test: Boolean, msg: String) = {
    if (!test) fail(msg)
  }

  def prevent(test: Boolean, msg: String) = {
    if (test) fail(msg)
  }

  def unwrap[A](a: Option[A], msg: String) = a match {
    case None => fail(msg)
    case Some(a) => a
  }

  object Env {
    def empty: Env = Map()
  }

  object Subst {
    def empty: Subst = Map()
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

  object Eqv extends Binary("<=>")
  object Pair extends Binary("Pair")
  object Left extends Unary("Left")
  object Right extends Unary("Right")
  object Assumption extends Id("Assumption")

  def group[A, B](xs: List[(A, B)]) = {
    xs.groupBy(_._1).map {
      case (x, ys) => (x, ys.map(_._2))
    }
  }

  val sub = "₀₁₂₃₄₅₆₇₈₉"
  implicit class StringOps(self: String) {
    def prime = self + "'"

    def __(index: Int): String = {
      self + (index.toString map (n => sub(n - '0')))
    }

    def __(index: Option[Int]): String = index match {
      case None => self
      case Some(index) => this __ index
    }
  }

  implicit class SetOps[A](self: Set[A]) {
    def disjoint(that: Set[A]) = {
      (self & that).isEmpty
    }
  }

  implicit class ListOps[A](self: List[A]) {
    def extract(index: Int): (A, List[A]) = {
      assert(0 <= index && index <= self.length)
      val rest = (self take index) ++ (self drop (index + 1))
      val at = self apply index
      (at, rest)
    }
  }
}
