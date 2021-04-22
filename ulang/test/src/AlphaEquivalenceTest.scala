import org.scalatest.funspec.AnyFunSpec
import TestHelpers.expr

class AlphaEquivalenceTest extends AnyFunSpec with PreloadLoader {
  private def t(left: String, right: String, msg: String = "") {
    val msg2 = if (msg != "") msg else left + " =~= " + right
    it(msg2) {
      assert(ulang.alphaEqui(expr(left), expr(right)))
    }
  }
  private def f(left: String, right: String, msg: String = "") {
    val msg2 = if (msg != "") msg else left + " ≠ " + right
    it(msg2) {
      assert(!ulang.alphaEqui(expr(left), expr(right)))
    }
  }
  describe("equivalence of some simple terms") {
    t("x", "x", "equal free variables are α-equivalent")
    f("x", "y", "different free variables are not α-equivalent")
    t("Tag1", "Tag1")
    f("Tag1", "Tag2", "tags need to be equal")
    t("lambda x -> Tag1", "lambda y -> Tag1")
    f("lambda x -> Tag1", "lambda x -> Tag2")
    t("lambda x -> x", "lambda y -> y")
    t("lambda (Right a) y -> y | (Left b) x -> x",
      "lambda (Right p) x -> x | (Left q) z -> z")
    t("lambda (Foo a b c) (Bar x y z) -> z y x c b a",
      "lambda (Foo g h i) (Bar u v w) -> w v u i h g")
    t("forall x. phi x", "forall z. phi z")
    t("exists x. phi x", "exists z. phi z")
    f("forall x. phi x", "exists x. phi x", "different quantors")
    t("lambda x y -> x y", "lambda a -> lambda b -> a b")
    t("forall x y. x y", "forall a. forall b. a b")
  }
}
