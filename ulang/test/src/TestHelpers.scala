object TestHelpers {
  /** A String interpolator to parse u"..." into Expr.  */
  implicit class UlangParser(val sc: StringContext) {
    def u(): ulang.Expr = {
      import arse._
      implicit val w = ulang.Parse.whitespace
      ulang.Parse.expr.parseAll(sc.parts.mkString(" "))
    }
  }
}
