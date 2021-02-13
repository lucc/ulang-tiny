import org.scalatest.funspec.AnyFunSpec
import org.scalatest.BeforeAndAfter
import TestHelpers.UlangParser
import ulang.{App, Pair, Id}

class PreludeTest extends AnyFunSpec with PreloadLoader {

  // We import the automatic conversion String -> arse.Input.
  import arse._
  implicit val w = ulang.Parse.whitespace

  describe("tuples") {
    it("are defined with a comma") {
      val actual = u"(a,b)"
      assert(actual == Pair(Id("a"), Id("b")))
    }
    it("can be written without parens") {
      val actual = u"a,b"
      assert(actual == Pair(Id("a"), Id("b")))
    }
  }
  describe("equality") {
    it("parses as infix") {
      val actual = u"A == B"
      val expected = App(App(Id("=="), Id("A")), Id("B"))
      assert(actual == expected)
    }
  }

}
