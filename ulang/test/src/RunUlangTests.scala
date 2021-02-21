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

}
