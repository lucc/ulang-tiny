package ulang

/**
 * A pattern matching abbreviation for lambda expressions with just one
 * pattern and one argument.
 */
object LamId {
  def unapply(e: Expr) = e match {
    case Lam1(List(id: Id), body) => Some((id, body))
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
    case Lam1(ids, body) if ids.forall(_.isInstanceOf[Id]) =>
      Some((ids.map(_.asInstanceOf[Id]), body))
    case _ => None
  }
}

/**
 * A pattern matching abbreviation for lambda expressions with only one case
 */
object Lam1 extends ((List[Expr], Expr) => Expr) {
  def apply(pats: List[Expr], body: Expr) = Lam(List(Case(pats, body)))
  def unapply(e: Expr): Option[(List[Expr], Expr)] = e match {
    case Lam(List(Case(pats, body))) => Some((pats, body))
    case _ => None
  }
}
