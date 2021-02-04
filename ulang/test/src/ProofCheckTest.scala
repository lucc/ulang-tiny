import org.scalatest.funspec.AnyFunSpec
import ulang.Expr.check
import ulang.{True, False, Imp, And, Id, Expr}

class ProofCheckTest extends AnyFunSpec {

  // load the prelude file when initializeing the test suite
  ulang.Main.loadPrelude()

  def parse(s: String) = {
    import arse._
    implicit val w = ulang.Parse.whitespace
    ulang.Parse.expr.parseAll(s)
  }
  def assertProves(proof: Expr, goal: Expr) {
    assert(check(Map(), proof, goal), proof + " does not prove " + goal)
  }

  describe("simple proofs") {
    it("True represents the trivial proof of True") {
      assertProves(True, True)
    }
    it("the identity function proofs a==>a") {
      val id_term = parse("lambda x -> x")
      assertProves(id_term, Imp(Id("a"), Id("a")))
    }
  }

  describe("Hilbert axioms") {
    it("cons proves weakening") {
      val cons = parse("lambda x -> lambda y -> x")
      val weakening = Imp(Id("a"), Imp(Id("b"), Id("a")))
      assertProves(cons, weakening)
    }
    it("flip function proof order innvariance in implications") {
      val flip = parse("lambda x -> lambda y -> lambda z -> x z y")
      val invariance = Imp(Imp(Id("a"), Imp(Id("b"), Id("c"))),
                           Imp(Id("b"), Imp(Id("a"), Id("c"))))
      assertProves(flip, invariance)
    }
    it("function composition proves chaining") {
      val composition = parse("lambda f -> lambda g -> lambda x -> f (g x)")
      val chain = Imp(Imp(Id("b"), Id("c")),
                      Imp(Imp(Id("a"), Id("b")),
                          Imp(Id("a"), Id("c"))))
      assertProves(composition, chain)
    }
    it("ex falso quodlibet") {
      val foo = ???
      val efq = Imp(Id("a"), Imp(Imp(Id("a"), False), Id("b")))
      assertProves(foo, efq)
    }
  }

  describe("conjunction") {
    it("is symmetric") {
      val switch1 = parse("lambda (x,y) -> (y,x)")
      val switch2 = parse("lambda p -> match p with (x,y) -> (y,x)")
      val sym = Imp(And(Id("a"), Id("b")), And(Id("b"), Id("a")))
      assertProves(switch1, sym)
      assertProves(switch2, sym)
    }
  }

  describe("disjunction") {
  }
}
