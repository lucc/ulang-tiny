import org.scalatest.funspec.AnyFunSpec
import ulang.Parse.script
import ulang.Parse.whitespace

class LemmaTest extends AnyFunSpec {

  import ulang.{Id, Imp}
  val a = Id("a")
  val foo = Id("foo")

  describe("starting lemmas") {
    it("with a name and assumptions") {
      script.parse("lemma foo := assume a; show a;")
    }
    it("with a name only") {
      script.parse("lemma foo := show a ==> a;")
    }
    it("unnamed but with assumptions") {
      script.parse("assume a; show a;")
    }
    it("unnamed without assumptions") {
      script.parse("show a ==> a;")
    }
  }
  describe("saving lemmas") {
    import ulang.context.lemmas
    it("works") {
      ulang.Exec.run("lemma foo := show a ==> a; proof term lambda x -> x;")
      assert(lemmas contains foo)
      assert(lemmas(foo) == Imp(a, a))
    }
  }

  describe("using lemmas") {
    import ulang.context.lemmas
    it("works") {
      lemmas += (foo -> Imp(a, a))
      ulang.Exec.run("show a ==> a; proof term foo;")
    }
  }
}
