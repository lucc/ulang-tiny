import org.scalatest.funspec.AnyFunSpec
import ulang.ProofTermChecker.check
import ulang.{True, False, Imp, And, Id, Expr}

class ProofCheckTest extends AnyFunSpec {
  import TestHelpers.UlangParser

  // load the prelude file when initializeing the test suite
  ulang.Main.loadPrelude()

  def assertProves(proof: Expr, goal: Expr) {
    check(proof, goal) match {
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
    it("ex falso quodlibet") {
      pendingUntilFixed {
      val foo = u"todo" // FIXME is this an axiom?
      val efq = u"a ==> (not a ==> b)"
      assertProves(foo, efq)
      }
    }
  }

  describe("conjunction") {
    it("is symmetric") {
      val switch1 = u"lambda (x,y) -> (y,x)"
      val switch2 = u"lambda p -> match p with (x,y) -> (y,x)"
      val sym = u"a /\ b ==> b /\ a"
      assertProves(switch1, sym)
      pendingUntilFixed {
        assertProves(switch2, sym)
      }
    }
  }

  describe("disjunction") {
    it("is symmetric") {
      pendingUntilFixed {
      val switch1 = u"""lambda ant -> match ant with (Left x) -> Right x
                                                  | (Right x) -> Left x;"""
      val switch2 = u"""lambda (Left x) -> Right x
                             | (Right x) -> Left x;"""
      val sym = u"a \/ b ==> b \/ a"
      assertProves(switch1, sym)
      }
    }
  }
}
