import org.scalatest.funspec.AnyFunSpec
import ulang.{Parse => p}
import arse.Input

class ParseTest extends AnyFunSpec {

  def mkInput(string: String) = new Input(string, 0, p.whitespace)

  describe("Comments") {
    describe("Extend to the end of line") {
      it("part one") {
        val input = mkInput("//eval Foo;\n")
        assert(p.script.parseAll(input) == Nil)
      }
      it("part two") {
        val input1 = mkInput("//eval Foo;\neval Foo;")
        val input2 = mkInput("eval Foo;")
        assert(p.script.parseAll(input1) == p.script.parseAll(input2))
      }
    }
  }

}
