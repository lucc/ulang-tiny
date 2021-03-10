import org.scalatest.funspec.AnyFunSpec
import TestHelpers.{expr, UlangParser}
import ulang.ProofTermChecker.infer
import ulang.TypeInference
import ulang.{Expr, Id, And, Pair}

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

  // load the prelude file when initializeing the test suite
  ulang.Main.loadPrelude()

  import ulang.{Lam, Case, App, All, RightE, LeftE, Wildcard, Or}

  val a = Id("a")
  val b = Id("b")
  val x = Id("x")
  val T = Id("T")
  val T1 = Id("T", Some(1))
  val T2 = Id("T", Some(2))

  describe("building type equations") {
    /** Wrapper around TypeInference.build to hide the initial type variable */
    def build(ctx: Map[Id, Expr], term: Expr) = {
      val tvar = TypeInference.TypeVar()
      TypeInference.build(ctx, term, tvar) map (_(tvar))
    }

    it("can find type assumtions in the context") {
      val actual = build(Map(a -> T), a)
      assert(actual == Right(T))
    }
    it("fails if variable is missing from the context") {
      val actual = build(Map(), a)
      assert(actual.isInstanceOf[Left[String, _]])
    }
  }
  describe("simple type inference examples") {
    it("pairs") {
      val actual = TypeInference(Map(a -> T1, b -> T2), Pair(a, b))
      assert(actual == Right(And(T1, T2)))
    }
    it("left") {
      val actual = TypeInference(Map(a -> T), LeftE(a))
      assert(actual == Right(Or(T, Wildcard)))
    }
    it("right") {
      val actual = TypeInference(Map(a -> T), RightE(a))
      assert(actual == Right(Or(Wildcard, T)))
    }
    it("omega term") {
      val actual = TypeInference(Map(), u"lambda x -> x x")
      assert(actual.isInstanceOf[Left[String, _]])
    }
  }
}
