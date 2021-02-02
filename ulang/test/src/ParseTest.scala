import org.scalatest.funspec.AnyFunSpec
import ulang.{Parse => p}
import arse.Input

class ParseCommentsTest extends AnyFunSpec {
  // We put these test in a seerate class in order to seerate the imports for
  // the implicit whitespace handling.  This class should explicitly test some
  // features of this whitespace parser.

  def mkInput(string: String) = new Input(string, 0, p.whitespace)

  describe("Comments") {
    describe("Extend to the end of line") {
      it("part one") {
        val input = mkInput("//eval Foo;\n")
        assert(p.script.parseAll(input) == Nil)
      }

      it("part two") {
        val input = mkInput("//eval Foo;\neval Foo;")
        val actual = p.script.parseAll(input)
        val expected = List(ulang.Evals(List(ulang.Id("Foo"))))
        assert(actual == expected)
      }
    }
  }

}
