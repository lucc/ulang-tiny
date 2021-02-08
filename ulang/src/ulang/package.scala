package object ulang {
  import arse._

  type Env = Map[Id, Val]
  type Subst = Map[Id, Expr]

  implicit def toIds(ids: List[Id]) = new Ids(ids)
  implicit def toExprs(exprs: List[Expr]) = new Exprs(exprs)
  implicit def toCases(cases: List[Case]) = new Cases(cases)
  implicit def toCases1(cases: List[Case1]) = new Cases1(cases)

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
