package ulang

object Main {
  def main(args: Array[String]) = {
    for (file <- args) {
      Exec.run(file)
    }
  }
}