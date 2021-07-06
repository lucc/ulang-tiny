import mill._
import mill.scalalib._

trait MyScalaModule extends ScalaModule {
    def scalaVersion = "2.12.10"
    //see https://github.com/com-lihaoyi/mill/discussions/1396#discussioncomment-969512
    override def ammoniteVersion = "2.4.0"
}

object ulang extends MyScalaModule {

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

object repl extends MyScalaModule {
    def moduleDeps = Seq(ulang)
    def unmanagedClasspath = ulang.unmanagedClasspath
}
