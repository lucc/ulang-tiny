import org.scalatest.funspec.AnyFunSpec
import TestHelpers.{expr, UlangParser}
import ulang.ProofTermChecker.infer
import ulang.{Expr, Id}

class TypeInferenceTests extends AnyFunSpec {
  def test(term: Expr, ty: Expr, context: Map[Id, Expr] = Map.empty) {
    assert(infer(context: Map[Id,Expr], term) == Right(ty))
  }
  def ctx(kvs: (String, String)*) = kvs map { case (k, v) => (Id(k), expr(v)) } toMap

  describe("lookup in context") {
    import ulang.{Pair, LeftE, RightE, And, Or}
    it("works for Ids") { test(u"var", u"Type", ctx("var" -> "Type")) }
    it("pair") { test(Pair(Id("a"), Id("b")), And(Id("A"), Id("B")), ctx("a" -> "A", "b" -> "B")) }
    it("left") { test(u"Left a", Or(u"A",  u"_"), ctx("a" -> "A", "b" -> "B")) }
    it("right") { test(u"Right b", Or(u"_",  u"B"), ctx("a" -> "A", "b" -> "B")) }
  }
}
