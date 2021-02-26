package ulang

/**
 * A pattern matching abbreviation for lambda expressions with just one
 * pattern and one argument.
 */
object Lam1 {
  def unapply(e: Expr) = e match {
    case Lam(List(Case(List(id@Id(_, _)), body))) => Some((id, body))
    case _ => None
  }
}

/**
 * A pattern matching abbreviation for lambda expressions with only one case
 * and only Ids in the pattern
 */
object LamIds extends ((List[Id], Expr) => Expr) {
  def apply(ids: List[Id], body: Expr) = Lam(List(Case(ids, body)))
  def unapply(e: Expr): Option[(List[Id], Expr)] = e match {
    case Lam(List(Case(ids, body))) if ids.forall(_.isInstanceOf[Id]) =>
      Some((ids.map(_.asInstanceOf[Id]), body))
    case _ => None
  }
}
