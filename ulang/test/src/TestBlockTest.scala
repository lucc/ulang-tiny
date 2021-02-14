import org.scalatest.funspec.AnyFunSpec
import TestHelpers.UlangParser

class TestBlockTest extends AnyFunSpec with PreloadLoader {

  describe("Eq.split (used in Exec.exec for Tests() blocks)") {
    import ulang.Eq.split
    import ulang.Id
    it("splits equalities in left and right hand side") {
      val eq = u"a == b"
      assert(split(eq) == (Id("a"), Id("b")))
    }
    it("splits equivalences in left and right hand side") {
      val eqv = u"a <=> b"
      assert(split(eqv) == (Id("a"), Id("b")))
    }
    it("Splits negations into the inner term and False") {
      val neg = u"not foo"
      assert(split(neg) == (Id("foo"), ulang.False))
    }
    it("other application terms are return with True") {
      val other = u"other application"
      assert(split(other) == (other, ulang.True))
    }
    it("let terms are return with True") {
      val other = u"let x = X in x x"
      assert(split(other) == (other, ulang.True))
    }
    it("match terms are return with True") {
      val other = u"match x with True -> False | False -> True"
      assert(split(other) == (other, ulang.True))
    }
    it("lamdba terms are return with True") {
      val other = u"lambda x -> x x"
      assert(split(other) == (other, ulang.True))
    }
  }

}
