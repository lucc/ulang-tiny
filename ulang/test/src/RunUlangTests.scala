import org.scalatest.funspec.AnyFunSpec
import java.io.File

class RunUlangTests extends AnyFunSpec with PreloadLoader {

  val mock_stdout = new java.io.ByteArrayOutputStream()
  def noStdout(test: => Unit) = Console.withOut(mock_stdout)(test)
  def testFiles(folder: String) =
    new File(getClass.getResource("/"+folder).getFile()).listFiles(
      (_, name) => name endsWith ".u").map(_.getAbsolutePath)
  def run(file: String, pending: Boolean = false) = it(file) {
    if (pending) pendingUntilFixed { ulang.Exec.runFile(file) }
    else noStdout { ulang.Exec.runFile(file) }
  }
  def eval(snippet: String, pending: Boolean = false) = it(snippet) {
    if (pending) pendingUntilFixed { ulang.Exec.run(snippet) }
    else noStdout { ulang.Exec.run(snippet) }
  }

  describe("run file") {
    for (testFile <- testFiles("tests"))   run(testFile)
    for (testFile <- testFiles("pending")) run(testFile, pending=true)
  }

  describe("special files") {
    it("the omega term should throw an exception") {
      assertThrows[java.lang.StackOverflowError] {
        ulang.Exec.runFile(getClass.getResource("/omega.u").getPath())
      }
    }
  }

  describe("pending snippets") {
    val snippets = List(
      // proofs with match expressions
      // symmetry of \/
      """show a \/ b ==> b \/ a;
         proof term lambda ant -> match ant with (Left x) -> Right x
                                               | (Right x) -> Left x;""",
      // Schwichtenberg page 13
      """show (exists x. a x ==> b) ==> (forall x. a x) ==> b;
      proof term lambda (Witness x w p) -> lambda fa -> p (Inst fa w lambda x -> x);""",
      """show ((exists x. a x) ==> b) ==> forall x.a x ==> b;
      proof term lambda f -> forall x. lambda ha -> f (Witness x x ha);""",
      //a -> f (Witness Term (Inst fa Term lambda x -> x));
      """//show (not (not (not a))) ==> not a;
      show (((a ==> False) ==> False) ==> False) ==> a ==> False;
      proof term lambda h3n -> lambda ha -> h3n (lambda h1n -> h1n ha);""",
    )
    for (snippet <- snippets) eval(snippet, pending=true)
  }

  describe("working snippets") {
    // proving or elimination
    eval("""show a \/ b ==> (a ==> c) ==> (b ==> c) ==> c;
      proof term lambda (Left x)  -> (lambda p1 -> lambda p2 -> p1 x)
                      | (Right x) -> (lambda p1 -> lambda p2 -> p2 x);""")
    // symmetry of \/
    eval("""show a \/ b ==> b \/ a;
         proof term lambda (Left x) -> Right x | (Right x) -> Left x;""")
    // proofs with match expressions
    // symmetry of /\
    eval("""show a /\ b ==> b /\ a;
      proof term lambda p -> match p with (x,y) -> (y,x);""")
    // proof with all quantifier
    eval("show (forall x. p x) ==> p Foo; proof term lambda x -> Inst x Foo lambda x -> x;")
    // proving introduction rules for exists
    eval("show a ==> exists x. a; proof term (lambda a -> Witness x x a);")
    eval("show p x ==> exists y. p y; proof term (lambda a -> Witness y x a);")
    // Schwichtenberg page 13
    eval("""show (forall x.a x ==> b) ==> (exists x. a x) ==> b;
        proof term lambda fa -> lambda (Witness x w p) -> Inst fa w lambda hab -> hab p;""")
    eval("""show (forall x.a ==> b x) ==> a ==> forall x. b x;
        proof term lambda hfa -> lambda ha -> forall var. Inst hfa var lambda hab -> hab ha;""")
    eval("""show (a ==> forall x. b x) ==> forall x. a ==> b x;
        proof term lambda f -> forall var. lambda precond -> Inst (f precond) var lambda x -> x;""")
    // TODO why do I have to put "var" and not "x" here ----------------------^

    eval("""show (exists x. a ==> b x) ==> a ==> exists x. b x;
        proof term lambda (Witness x w hab) -> lambda ha -> Witness x w (hab ha);""")
    // reordering bound variables
    val proof1 = """proof term lambda faxy -> forall y. forall x.
                    Inst faxy x lambda fay -> Inst fay y lambda x -> x;"""
    eval("show (forall x y. a) ==> forall y x. a;"+proof1)
    eval("show (forall x. forall y. a) ==> forall y. forall x. a;"+proof1)
    val proof2 = """proof term lambda (Witness x w1 (Witness y w2 pt))
                               -> Witness y w2 (Witness x w1 pt);"""
    eval("show (exists x y. a x y) ==> exists y x. a x y;"+proof2)
    eval("show (exists x. exists y. a x y) ==> exists y. exists x. a x y;"+proof2)
    eval("""// show a ==> not not a;
            show a ==> (a ==> False) ==> False;
            proof term lambda ha haf -> haf ha;""")
  }

  describe("rules") {
    describe("from propositional logic:") {
      describe("introduction rules") {
        // implication introduction / weakening
        eval("show a ==> b ==> a; proof term lambda x -> lambda y -> x;")
        // or introduction 1
        eval("""show a ==> a \/ b; proof term lambda x -> Left x;""")
        // or introduction 2
        eval("""show b ==> a \/ b; proof term lambda x -> Right x;""")
        // and introduction
        eval("""show a ==> b ==> a /\ b; proof term lambda x -> lambda y -> (x,y);""")
      }
      describe("elimination rules") {
          // implication elimination / modus ponens
          eval("""show (a ==> b) ==> a ==> b;
          proof term lambda f -> lambda x -> f x;""")
          eval("""show a ==> (a ==> b) ==> b;
          proof term lambda x -> lambda f -> f x;""")
          // or elimination
          eval("""show a \/ b ==> (a ==> c) ==> (b ==> c) ==> c;
          proof term lambda (Left x)  -> (lambda p1 -> lambda p2 -> p1 x)
                          | (Right x) -> (lambda p1 -> lambda p2 -> p2 x);""")
          // and elimination
          eval("""show a /\ b ==> (a ==> b ==> c) ==> c;
          proof term lambda (x,y) -> lambda f -> f x y;""")
      }
    }
    describe("from predicate logic:") {
      describe("introduction rules") {
        // universal quantifier introduction
        eval("show a ==> forall x. a; proof term lambda p -> forall x. p;")
        // existential quantifier introduction
        eval("show a t ==> exists x. a x; proof term lambda p -> Witness x t p;" )
        it("universal quantifier introduction violating variable condition") {
          // it would work with "a" instead of "a x"
          val show = "show a x ==> forall x. a x;"
          val proof = "proof term lambda p -> forall x. p;"
          assertThrows[RuntimeException] { // Capturing variable x
            noStdout { ulang.Exec.run(show + proof) }
          }
        }
      }
      describe("elimination rules") {
        // universal quantifier elimination
        eval("show (forall x. p x) ==> p t; proof term lambda f -> Inst f t (lambda x -> x);")
        // existential quantifier elimination
        val exElim = "show (exists x. a x) ==> (forall x. a x ==> b) ==> b;"
        val proof ="proof term lambda (Witness x w p) -> lambda f -> Inst f w lambda ff -> ff p;"
        eval(exElim + " " + proof)
        it("existential quantifier elimination violating variable condition") {
          // it would work with "b" instead of "b x"
          val badExElim = "show (exists x. a x) ==> (forall x. a x ==> b x) ==> b x;"
          assertThrows[RuntimeException] {
            noStdout { ulang.Exec.run(badExElim + proof) }
          }
        }
      }
    }
  }
}
