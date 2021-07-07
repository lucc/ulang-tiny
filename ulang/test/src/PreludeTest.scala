import org.scalatest.funspec.AnyFunSpec
import TestHelpers.UlangParser
import ulang.{App, Pair, Id, And, Eqv, Or}

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

  describe("parsing with the u string modifier") {
    it("handles backslashes like in normal strings") {
      val actual = u" \ "
      val expected = Id("\\")
      assert(actual == expected)
    }
    it("can parse and expressions") {
      val actual = u"a /\ b"
      val expected = App(App(Id("/\\"), Id("a")), Id("b"))
      assert(actual == expected)
    }
  }
  describe("associativity") {
    it("of Pair is right") {
      val actual = u"a, b, c"
      val expected = App(App(Id(","), Id("a")), App(App(Id(","), Id("b")), Id("c")))
      assert(actual == expected)
    }
    it("of And is right") {
      val actual = u"a /\ b /\ c"
      val expected = App(App(Id("/\\"), Id("a")), App(App(Id("/\\"), Id("b")), Id("c")))
      assert(actual == expected)
    }
    it("of Imp is right") {
      val actual = u"a ==> b ==> c"
      val expected = App(App(Id("==>"), Id("a")), App(App(Id("==>"), Id("b")), Id("c")))
      assert(actual == expected)
    }
    it("of application is left") {
      val actual = u"a b c"
      val expected = App(App(Id("a"), Id("b")), Id("c"))
      assert(actual == expected)
    }
  }
  describe("precedence") {
    it("<=> has lower precedence than /\\") {
      val a = Id("a")
      val b = Id("b")
      val actual = u"a /\ b <=> b /\ a"
      val expected = Eqv(And(a, b), And(b, a))
      assert(actual == expected)
    }
    it("<=> has lower precedence than \\/") {
      val a = Id("a")
      val b = Id("b")
      val actual = u"a \/ b <=> b \/ a"
      val expected = Eqv(Or(a, b), Or(b, a))
      assert(actual == expected)
    }
  }

}
