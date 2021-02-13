import org.scalatest.funspec.AnyFunSpec
import java.io.File

class RunUlangTests extends AnyFunSpec with PreloadLoader {

  def testFiles(folder: String) =
    new File(getClass.getResource("/"+folder).getFile()).listFiles(
      (_, name) => name endsWith ".u").map(_.getAbsolutePath)

  describe("run file") {
    for (testFile <- testFiles("tests"))
      it(testFile) { ulang.Exec.run(testFile) }
    for (testFile <- testFiles("pending"))
      it(testFile) {
        pendingUntilFixed {
          ulang.Exec.run(testFile)
        }
      }
  }

  describe("special files") {
    it("the omega term should throw an exception") {
      assertThrows[java.lang.StackOverflowError] {
        ulang.Exec.run(getClass.getResource("/omega.u").getPath())
      }
    }
  }

}
