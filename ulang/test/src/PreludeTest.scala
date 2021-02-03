import org.scalatest.funspec.AnyFunSpec
import org.scalatest.BeforeAndAfter

class PreludeTest extends AnyFunSpec with BeforeAndAfter {

  // We import the automatic conversion String -> arse.Input.
  import arse._
  implicit val w = ulang.Parse.whitespace

  /** load the prelude file before each test */
  before { ulang.Exec.run(ulang.Main.preludeFile) }
  /** reset the parsing and execution context after each test */
  after { ulang.context.clear }

  describe("tuples") {
    import ulang.{Pair, Id}
    it("are defined with a comma") {
      val actual = ulang.Parse.expr.parse("(a,b)")
      assert(actual == Pair(Id("a"), Id("b")))
    }
    it("can be written without parens") {
      val actual = ulang.Parse.expr.parse("a,b")
      assert(actual == Pair(Id("a"), Id("b")))
    }
  }

}
