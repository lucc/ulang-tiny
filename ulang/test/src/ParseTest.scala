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

class ParseTest extends AnyFunSpec {
  // We import the automatic conversion String -> arse.Input.
  import arse._
  implicit val w = p.whitespace

  describe("Fixity expressions") {
    it("for prefix operators") {
      val (names, fixity) = p.fix.parse("opname [prefix 5]")
      assert(names == List("opname"))
      assert(fixity == Prefix(5))
    }
    it("for postfix operators") {
      val (names, fixity) = p.fix.parse("opname [postfix 5]")
      assert(names == List("opname"))
      assert(fixity == Postfix(5))
    }
    it("for infix operators") {
      val (names, fixity) = p.fix.parse("opname [infix 5]")
      assert(names == List("opname"))
      assert(fixity == Infix(Non, 5))
    }
    it("accept several operator names") {
      val (names, fixity) = p.fix.parse("op1 op2 op3 [infix 42]")
      assert(names == List("op1", "op2", "op3"))
      assert(fixity == Infix(Non, 42))
    }
  }

  describe("let expressions") {
    import ulang.{Let, Case1, Id, App}
    it("can define simple bindings") {
      val actual = p.let.parse("let x := y in x")
      assert(actual == Let(List(Case1(Id("x"), Id("y"))), Id("x")))
    }
    it("can bind several names, separated by ;") {
      val actual = p.let.parse("let x := y; a := b in x a")
      assert(actual == Let(List(Case1(Id("x"), Id("y")),
                                Case1(Id("a"), Id("b"))),
                           App(Id("x"), Id("a"))))
    }
    it("can be nested on both sides") {
      val actual = p.let.parse("""
        let x := let a := A;
                     b := B
                 in a b
        in let y := Z
           in x y""")
      val expected = Let(List(Case1(Id("x"), Let(List(Case1(Id("a"), Id("A")),
                                                      Case1(Id("b"), Id("B"))),
                                                 App(Id("a"), Id("b"))))),
                         Let(List(Case1(Id("y"), Id("Z"))),
                             App(Id("x"), Id("y"))))
      assert(actual == expected)
    }
  }

  describe("match expressions") {
    import ulang.{Match, Case, Id, App, Let, Case1}
    it("can match one case") {
      val actual = p.mtch.parse("match x with A -> B")
      assert(actual == Match(List(Id("x")),
                             List(Case(List(Id("A")), Id("B")))))
    }
    it("can match with variable bindings") {
      val actual = p.mtch.parse("match x with (A y) -> B y")
      assert(actual == Match(List(Id("x")),
                             List(Case(List(App(Id("A"), Id("y"))),
                                       App(Id("B"), Id("y"))))))
    }
    it("can match serveral cases") {
      val actual = p.mtch.parse("match x with A -> B | C -> D")
      assert(actual == Match(List(Id("x")),
                             List(Case(List(Id("A")), Id("B")),
                                  Case(List(Id("C")), Id("D")))))
    }
    it("can be used in let bindings") {
      val actual = p.let.parse("let a := match x with A -> B | C -> D in a")
      val expected = Let(List(Case1(Id("a"),
                                    Match(List(Id("x")),
                                          List(Case(List(Id("A")), Id("B")),
                                               Case(List(Id("C")), Id("D")))))),
                         Id("a"))
      assert(actual == expected)
    }
  }

  describe("lambda expressions") {
    import ulang.{Lam, Case, Id, App}
    it("can have one simple argument") {
      val actual = p.lam.parse("lambda x -> x")
      assert(actual == Lam(List(Case(List(Id("x")), Id("x")))))
    }
  }

  describe("parser state") {
    import ulang.{Notation, Evals, App, Id}
    import arse.{Infix, Non}
    it("without noatation + is just an Id") {
      val actual = p.script.parseAll("eval A + B;")
      val expected = List(Evals(List(App(App(Id("A"), Id("+")), Id("B")))))
      assert(actual == expected)
    }
    it("fixity definitions are carried in a parse context") {
      val List(actual_n, actual_e) = p.script.parseAll("notation + [infix 10]; eval A + B;")
      val expected_n = Notation(List((List("+"), Infix(Non, 10))))
      val expected_e = Evals(List(App(App(Id("+"), Id("A")), Id("B"))))
      assert(actual_n == expected_n)
      assert(actual_e == expected_e)
    }
  }

  describe("assignment operator") {
    import ulang.{Id, Def}
    it("simplest version") {
      val actual = p.df.parse("a := b;")
      val expected = Def(Id("a"), Id("b"))
      assert(actual == expected)
    }
  }

  describe("parsing ids") {
    def test(description: String, input: String) {
      it(description) { assert(p.expr.parse(input) == ulang.Id(input)) }
    }
    test("with letters and symbols", "a+")
    test("with symbols and letters", "+a")
    test("with symbols and numbers", "+1")
    test("with numbers and symbols", "1+")
    test("names for elim rule constructor terms", "Elim-/\\")
  }

  describe("define") {
    it("can not have lambdas on the left") {
      assertThrows[RuntimeException] {
        p.cmd.parse("define (lambda x -> x) := A;")
      }
    }
    it("can not have let on the left") {
      assertThrows[RuntimeException] {
        p.cmd.parse("define (let x := y in x) := A;")
      }
    }
    describe("can not have a tag on the left") {
      it("plain") {
        assertThrows[RuntimeException] {
          p.cmd.parse("define Foo := A;")
        }
      }
      it("With arguments") {
        assertThrows[RuntimeException] {
          p.cmd.parse("define Foo x := A;")
        }
      }
    }
  }
}
