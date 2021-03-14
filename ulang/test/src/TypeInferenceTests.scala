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
  val f = Id("f")
  val S = Id("S")
  val T = Id("T")

  describe("type inference") {

    val futs: Map[String, (Ctx, Expr) => Either[String, Expr]] = Map(
      "simple" -> TypeInference.simple,
      //"full" -> TypeInference.full,
    )

    for ((name, fut) <- futs) {
      // This is our default context for this test block
      val defaultContext = Map(a -> S, b -> T)

      def test(name: String, term: Expr, ty: Expr, context: Map[Id, Expr] = defaultContext) {
        it(name) {
          val result = fut(context, term)
          assert(result == Right(ty))
        }
      }

      describe(name) {
        test("works for Ids", a, S)
        test("pairs", Pair(a, b), And(S, T))
        test("left", LeftE(a), Or(S, Wildcard))
        test("right", RightE(b), Or(Wildcard, T))
        test("simple applications", u"f a", T, Map(a -> S, f -> Imp(S, T)))
        test("implication", u"lambda a -> a", All(a, Imp(a, a)))
      }
    }
  }

  describe("building type equations") {
    /** Wrapper around TypeInference.build to hide the initial type variable */
    def build(ctx: Map[Id, Expr], term: Expr) = {
      val tvar = TypeInference.TypeVar()
      TypeInference.build(ctx, term, tvar)(tvar)
    }

    it("can find type assumtions in the context") {
      val actual = build(Map(a -> T), a)
      assert(actual == T)
    }
    it("fails if variable is missing from the context") {
      assertThrows[TypeInference.InferenceError] { build(Map(), a) }
    }
  }
}
