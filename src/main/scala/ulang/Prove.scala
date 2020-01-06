package ulang

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
    case _ =>
      List(show)
  }
}