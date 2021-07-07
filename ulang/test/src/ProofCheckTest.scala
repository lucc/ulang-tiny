import org.scalatest.funspec.AnyFunSpec
import ulang.ProofTermChecker.checkSafe
import ulang.{True, False, Imp, And, Id, Expr}
import TestHelpers.UlangParser

class ProofCheckTest extends AnyFunSpec {

  // load the prelude file when initializeing the test suite
  ulang.Main.loadPrelude()

  def assertProves(proof: Expr, goal: Expr) {
    checkSafe(proof, goal) match {
      case None => assert(true)
      case Some(err) => assert(false, err)
    }
  }

  describe("simple proofs") {
    it("True represents the trivial proof of True") {
      assertProves(True, True)
    }
    it("the identity function proofs a==>a") {
      val id_term = u"lambda x -> x"
      assertProves(id_term, u"a ==> a")
    }
  }

  describe("Hilbert axioms") {
    it("cons proves weakening") {
      val cons = u"lambda x -> lambda y -> x"
      val weakening = u"a ==> (b ==> a)"
      assertProves(cons, weakening)
    }
    it("flip function proof order innvariance in implications") {
      val flip = u"lambda x -> lambda y -> lambda z -> x z y"
      val invariance = u"(a ==> b ==> c) ==> b ==> a ==> c"
      assertProves(flip, invariance)
    }
    it("function composition proves chaining") {
      val composition = u"lambda f -> lambda g -> lambda x -> f (g x)"
      val chain = u"(b ==> c) ==> (a ==> b) ==> a ==> c"
      assertProves(composition, chain)
    }
  }

  describe("conjunction") {
    it("is symmetric") {
      val switch1 = u"lambda (x,y) -> (y,x)"
      val sym = u"a /\ b ==> b /\ a"
      assertProves(switch1, sym)
    }
  }
}

class DefinedFunctionAxiomsTest extends AnyFunSpec with PreloadLoader {

  import ulang.DefinedFunctionsAxiomsHelper._
  import ulang.Eq

  /**
   * define a ulang function for the tests
   */
  private def define(code: String) {
    //print("define " + code)
    ulang.Exec.run("define " + code)
  }

  describe("Def") {

    it("generates equations for defined constants") {
      define("c := Foo;")
      assert(constAxiom(Id("c")) == u"c == Foo")
    }

    it("generates equations for defined functions") {
      define("""
        map f NIL := NIL;
        map f (CONS x xs) := CONS (f x) (map f xs);
        """)
      assert(funcAxioms(Id("map")) ==
        u"""(forall f. map f NIL == NIL)
            /\
            forall f x xs. map f (CONS x xs) == CONS (f x) (map f xs)""")
    }

    it("replaces wildcards with new variables") {
      define("f _ := X;")
      // we can not test equality here because we do not know the name of the
      // generated variable
      assert(ulang.alphaEqui(funcAxioms(Id("f")), u"forall x. f x == X"))
    }

    it("handles variable reuse in patterns") {
      pendingUntilFixed {
      define("""eq x x := True;
                eq x y := False;""")
      // TODO what should the axiom actually look like?
      assert(funcAxioms(Id("eq")) !=
        u"""(forall x. eq x x == True) /\ forall x y. eq x y == False""")
      }
    }

    it("handles overlapping patterns") {
      pendingUntilFixed {
      define("f X := Y; f x := Z;")
      // TODO what should the axiom actually look like?
      assert(funcAxioms(Id("f")) != u"f X == Y /\ forall x. f x == Z")
      }
    }
  }
}
