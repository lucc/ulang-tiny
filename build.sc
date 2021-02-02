import mill._
import mill.scalalib._

object ulang extends ScalaModule {
    def scalaVersion = "2.12.10"

    def unmanagedClasspath = T {
        Agg.from(os.list(millSourcePath / "lib").map(PathRef(_)))
    }

    def ivyDeps = Agg(ivy"com.lihaoyi::sourcecode:0.2.0")

    object test extends Tests {
        def ivyDeps = Agg(
            ivy"org.scalactic::scalactic:3.1.1",
            ivy"org.scalatest::scalatest:3.1.1"
        )
        def testFrameworks = Seq("org.scalatest.tools.Framework")
        def unmanagedClasspath = T {
          Agg.from(os.list(millSourcePath / os.up / "lib").map(PathRef(_)))
        }
    }
}
