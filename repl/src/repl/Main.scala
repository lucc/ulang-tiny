
import ulang.Main.loadPrelude
import ulang.Exec._
import scala.io.StdIn

object Repl {

  def main(args: Array[String]) = {
    loadPrelude()
    var line = ""
    while ({
      print("ulang> ")
      line = StdIn.readLine()
      line != null
    }) {
      val cmds = parse(line)
      exec(cmds)
    }
  }
}
