import org.scalatest.funspec.AnyFunSpec
import java.io.File
import scala.reflect.ClassTag

class RunUlangTests extends AnyFunSpec with PreloadLoader {

  val mock_stdout = new java.io.ByteArrayOutputStream()
  def testFiles(folder: String): Array[String] = {
    val res = getClass.getResource("/"+folder)
    if (res == null) Array.empty
    else new File(res.getFile()).listFiles(
      (_, name) => name endsWith ".u").map(_.getAbsolutePath)
  }
  def mkTest(executor: (String => Any)) =
    (input: String, pending: Boolean) => it(input) {
      if (pending) pendingUntilFixed(executor(input))
      else Console.withOut(mock_stdout)(executor(input))
    }
  def run(file: String, pending: Boolean = false) = mkTest(ulang.Exec.runFile)(file, pending)
  def eval(snippet: String, pending: Boolean = false) = mkTest(ulang.Exec.run)(snippet, pending)
  def failRun[E <: AnyRef](file: String, pending: Boolean = false)(implicit c: ClassTag[E]) =
    mkTest(file => assertThrows[E](ulang.Exec.runFile(file)))(file, pending)
  def failEval[E <: AnyRef](snippet: String, pending: Boolean = false)(implicit c: ClassTag[E]) =
    mkTest(snippet => assertThrows[E](ulang.Exec.run(snippet)))(snippet, pending)

  describe("run file") {
    for (testFile <- testFiles("tests"))   run(testFile)
    for (testFile <- testFiles("pending")) run(testFile, pending=true)
    for (testFile <- testFiles("failing/StackOverflowError"))
      failRun[StackOverflowError](testFile)
    for (testFile <- testFiles("failing/RuntimeException"))
      failRun[RuntimeException](testFile)
    for (testFile <- testFiles("failing/pending"))
      failRun(testFile, true)
  }

  describe("pending snippets") {
    def e = eval(_, pending=true)
    // full type inference is still missing
    e("""show (((a ==> False) ==> False) ==> False) ==> a ==> False;
      proof term lambda h3n -> lambda ha -> h3n (lambda h1n -> h1n ha);""")
    // automatic forall instantiation with alpha equivalence
    e("""show (a t /\ exists y. phi y) ==> (forall x. (a x /\ exists y. p y) ==> b x) ==> b t;
      proof term lambda ha hfa -> hfa ha;""")
    // completeness check for destruction with lambda terms is still missing
    it("incomplete pattern match") { pendingUntilFixed {
      assertThrows {
        ulang.Exec.run("""show a \/ b ==> (a ==> c) ==> (b ==> c) ==> c;
      // this should fail because the Right case is missing
      proof term lambda (Left x)  -> (lambda p1 -> lambda p2 -> p1 x);""")
      }
    }}
  }

  describe("working snippets") {
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
        eval("show a t ==> exists x. a x; proof term lambda p -> Witness t p;" )
        // universal quantifier introduction violating variable condition
        // it would work with "a" instead of "a x"
        val show = "show a x ==> forall x. a x;"
        val proof = "proof term lambda p -> forall x. p;"
        failEval[RuntimeException](show + proof) // Capturing variable x
      }
      describe("elimination rules") {
        // universal quantifier elimination
        eval("show (forall x. p x) ==> p t; proof term lambda f -> Inst f t (lambda x -> x);")
        // existential quantifier elimination
        val exElim = "show (exists x. a x) ==> (forall x. a x ==> b) ==> b;"
        val proof ="proof term lambda (Witness w p) -> lambda f -> Inst f w lambda ff -> ff p;"
        eval(exElim + " " + proof)
        // existential quantifier elimination violating variable condition
        // it would work with "b" instead of "b x"
        val badExElim = "show (exists x. a x) ==> (forall x. a x ==> b x) ==> b x;"
        failEval[RuntimeException](badExElim + proof)
      }
    }
  }
}
