import org.scalatest.funspec.AnyFunSpec
import java.io.File

class RunUlangTests extends AnyFunSpec with PreloadLoader {

  def testFiles(extension: String) =
    new File(getClass.getResource("/tests").getFile()).listFiles(
      (_, name) => name endsWith extension).map(_.getAbsolutePath)

  describe("run file") {
    for (testFile <- testFiles(".u"))
      it(testFile) { ulang.Exec.run(testFile) }
    for (testFile <- testFiles(".u.pending"))
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
