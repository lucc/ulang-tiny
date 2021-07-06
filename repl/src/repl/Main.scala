
import ulang.Main.loadPrelude
import ulang.Exec._
import scala.io.StdIn.readLine
import Console.{RED, BLUE, RESET}

object Repl {

  def prompt = print(BLUE + "ulang> " + RESET)
  def error(message: String) = println(RED + message + RESET)

  def main(args: Array[String]) = {
    println("Starting the Ulang REPL ...")
    loadPrelude()

    prompt
    for (line <- io.Source.stdin.getLines) {
      try {
        exec(parse(line))
      } catch {
        case e: arse.Error => error("Parse error: " + e)
        case e: RuntimeException => error("Error: " + e.getMessage())
        case e: StackOverflowError => error("Stack overflow!")
      }
      prompt
    }
  }
}
