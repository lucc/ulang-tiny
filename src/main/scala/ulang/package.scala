package object ulang {
  import arse._

  type Env = Map[Var, Val]
  type Subst = Map[Var, Expr]

  object Env {
    def empty: Env = Map()
  }

  object Subst {
    def empty: Subst = Map()
  }

  object Eq extends Binary(Var("==", Infix(Non, 6)))

  object True extends Tag("true")
  object False extends Tag("false")

  object Zero extends Tag("0")
  object Succ extends Unary(Tag("+1", Postfix(11)))

  object Not extends Unary(Var("not", Infix(Right, 5)))
  object And extends Binary(Var("/\\", Infix(Right, 4)))
  object Or extends Binary(Var("\\/", Infix(Right, 3)))
  object Imp extends Binary(Var("==>", Infix(Right, 2)))
  object Eqv extends Binary(Var("<=>", Infix(Non, 1)))

  def group[A, B](xs: List[(A, B)]) = {
    xs.groupBy(_._1).map {
      case (x, ys) => (x, ys.map(_._2))
    }
  }
}