
import ulang.Main.loadPrelude
import ulang.Exec._
import scala.io.StdIn.readLine

object Repl {

  val prompt = "ulang> "

  def main(args: Array[String]) = {
    println("Starting the Ulang REPL ...")
    loadPrelude()

    print(prompt)
    for (line <- io.Source.stdin.getLines) {
      try {
        exec(parse(line))
      } catch {
        case e: arse.Error =>
          println("Parse error: " + e)
      }
      print(prompt)
    }
  }
}
