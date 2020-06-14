package ulang

object Main {
  def main(args: Array[String]) = {
    for (name <- args) {
      val context = new Context
      context.exec run name
    }
  }
}