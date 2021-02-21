import org.scalatest.funspec.AnyFunSpec
import java.io.File

class RunUlangTests extends AnyFunSpec with PreloadLoader {

  def testFiles(folder: String) =
    new File(getClass.getResource("/"+folder).getFile()).listFiles(
      (_, name) => name endsWith ".u").map(_.getAbsolutePath)

  describe("run file") {
    for (testFile <- testFiles("tests"))
      it(testFile) {
        Console.withOut(new java.io.ByteArrayOutputStream()) {
          ulang.Exec.runFile(testFile)
        }
      }
    for (testFile <- testFiles("pending"))
      it(testFile) {
        pendingUntilFixed {
          ulang.Exec.runFile(testFile)
        }
      }
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
      proof lambda (Left x)  -> (lambda p1 -> lambda p2 -> p1 x)
                 | (Right x) -> (lambda p1 -> lambda p2 -> p2 x);
      """,
      // proving introduction rules for exists
      "show a ==> exists x. a; proof term (lambda a -> (x, a));",
      "show p x ==> exists y. p y; proof term (lambda a -> (x, a));",
      // define statements with strange expressions on the left
      "define (let x := y in x) := A;",
    )
    for (snippet <- snippets) {
      it(snippet) { pendingUntilFixed { ulang.Exec.run(snippet) } }
    }
  }
}
