import org.scalatest.funspec.AnyFunSpec
import java.io.File

class RunUlangTests extends AnyFunSpec with PreloadLoader {

  val testFiles = new File(getClass.getResource("/").getFile()).listFiles(
    (_, name) => name endsWith ".u").map(_.getAbsolutePath)

  describe("run file") {
    for (testFile <- testFiles)
      it(testFile) { ulang.Exec.run(testFile) }
  }

}
