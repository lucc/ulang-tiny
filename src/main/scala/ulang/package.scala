package object ulang {
  type Env = Map[Var, Val]
  
  object Eq extends Binary(Var("=="))

  object True extends Tag("true")
  object False extends Tag("false")

  object Zero extends Tag("0")
  object Succ extends Unary(Tag("+1"))

  object And extends Binary(Var("/\\"))
  object Or extends Binary(Var("\\/"))
  object Imp extends Binary(Var("==>"))
  object Eqv extends Binary(Var("<=>"))
  
  def group[A, B](xs: List[(A, B)]) = {
    xs.groupBy(_._1).map {
      case (x, ys) => (x, ys.map(_._2))
    }
  }
}