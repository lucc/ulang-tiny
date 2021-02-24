object TestHelpers {
  /** Parse a string into an ulang expression */
  def expr(in: String) = {
    import arse._
    import ulang.Parse.whitespace
    ulang.Parse.expr.parseAll(in)
  }
  /** A String interpolator to parse u"..." into Expr.  */
  implicit class UlangParser(val sc: StringContext) {
    def u() = expr(sc.parts.mkString(" "))
  }
}
