import org.scalatest.funspec.AnyFunSpec
import ulang.Parse.script
import ulang.Parse.whitespace

class LemmaTest extends AnyFunSpec with PreloadLoader {

  import ulang.{Id, Imp, All}
  val a = Id("a")
  val b = Id("b")
  val c = Id("c")
  val foo = Id("foo")

  val mock_stdout = new java.io.ByteArrayOutputStream()
  def noStdout(test: => Unit) = Console.withOut(mock_stdout)(test)
  def eval(snippet: String) = noStdout { ulang.Exec.run(snippet) }

  import ulang.context.lemmas

  describe("starting lemmas") {
    it("with a name and assumptions") {
      script.parse("lemma foo; assume a; show a;")
    }
    it("with a name only") {
      script.parse("lemma foo; show a ==> a;")
    }
    it("unnamed but with assumptions") {
      script.parse("assume a; show a;")
    }
    it("unnamed without assumptions") {
      script.parse("show a ==> a;")
    }
  }

  describe("saving lemmas") {
    it("works") {
      assert(!(lemmas contains foo))
      eval("lemma foo; show a ==> a; proof term lambda x -> x;")
      assert(lemmas(foo) == Imp(a, a))
    }
    it("with named assumptions") {
      assert(!(lemmas contains foo))
      eval("lemma foo; assume hyp := b; show b; proof term hyp;")
      assert(lemmas(foo) == Imp(b, b))
    }
  }

  describe("using lemmas") {
    it("works") {
      lemmas += (foo -> Imp(c, c))
      eval("show c ==> c; proof term foo;")
    }
    it("with alpha equivalence") {
      lemmas += (foo -> All(a, Imp(a, a)))
      eval("show forall b. b ==> b; proof term foo;")
    }
  }
}
