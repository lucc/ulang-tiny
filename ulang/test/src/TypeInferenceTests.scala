import org.scalatest.funspec.AnyFunSpec
import TestHelpers.{expr, UlangParser}
import ulang._
import ulang.TypeInference.Ctx

class TypeInferenceTests extends AnyFunSpec {

  // load the prelude file when initializeing the test suite
  ulang.Main.loadPrelude()

  // define some expressions to reuse during tests
  val a = Id("a")
  val b = Id("b")
  val S = Id("S")
  val T = Id("T")

  describe("type inference") {
    val futs: Map[String, (Ctx, Expr) => Either[String, Expr]] =
      Map("simple" -> TypeInference.simple, "full" -> TypeInference.full)
    for ((name, fut) <- futs) {
      def test(term: Expr, ty: Expr, context: Map[Id, Expr] = Map(a -> S, b -> T)) {
        assert(fut(context: Map[Id,Expr], term) == Right(ty))
      }
      describe(name) {
        it("works for Ids") { test(a, T, Map(a -> T)) }
        it("pairs") { test(Pair(a, b), And(S, T)) }
        it("left") { test(LeftE(a), Or(S, Wildcard)) }
        it("right") { test(RightE(b), Or(Wildcard, T)) }
      }
    }
  }

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
}
