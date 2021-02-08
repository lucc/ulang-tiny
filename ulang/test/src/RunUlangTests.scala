import org.scalatest.funspec.AnyFunSpec
import java.io.File

class RunUlangTests extends AnyFunSpec with PreloadLoader {

  val testFiles = new File(getClass.getResource("/tests").getFile()).listFiles(
    (_, name) => name endsWith ".u").map(_.getAbsolutePath)

  describe("run file") {
    for (testFile <- testFiles)
      it(testFile) { ulang.Exec.run(testFile) }
  }

  describe("special files") {
    it("the omega term should throw an exception") {
      assertThrows[java.lang.StackOverflowError] {
        ulang.Exec.run(getClass.getResource("/omega.u").getPath())
      }
    }
  }

}
