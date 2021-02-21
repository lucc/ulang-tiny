import org.scalatest.funspec.AnyFunSpec
import java.io.File

class RunUlangTests extends AnyFunSpec with PreloadLoader {

  def testFiles(folder: String) =
    new File(getClass.getResource("/"+folder).getFile()).listFiles(
      (_, name) => name endsWith ".u").map(_.getAbsolutePath)
  def runSilent(file: String) {
    Console.withOut(new java.io.ByteArrayOutputStream()) {
      ulang.Exec.runFile(file)
    }
  }

  describe("run file") {
    for (testFile <- testFiles("tests"))
      it(testFile) { runSilent(testFile) }
    for (testFile <- testFiles("pending"))
      it(testFile) { pendingUntilFixed { runSilent(testFile) } }
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
      // proving or elimination
      """
      show a \/ b ==> (a ==> c) ==> (b ==> c) ==> c;
      proof term lambda (Left x)  -> (lambda p1 -> lambda p2 -> p1 x)
                      | (Right x) -> (lambda p1 -> lambda p2 -> p2 x);
      """,
      // proving introduction rules for exists
      "show a ==> exists x. a; proof term (lambda a -> (x, a));",
      "show p x ==> exists y. p y; proof term (lambda a -> (x, a));",
      // proofs with match expressions
      // symmetry of /\
      """show a /\ b ==> b /\ a; proof term lambda p -> match p with (x,y) -> (y,x);""",
      // symmetry of \/
      """show a \/ b ==> b \/ a;
         proof term lambda ant -> match ant with (Left x) -> Right x
                                               | (Right x) -> Left x;""",
      """show a \/ b ==> b \/ a;
         proof term lambda (Left x) -> Right x | (Right x) -> Left x;""",
      // define statements with strange expressions on the left
      "define (let x := y in x) := A;",
    )
    for (snippet <- snippets)
      it(snippet) { pendingUntilFixed { ulang.Exec.run(snippet) } }
  }
}
