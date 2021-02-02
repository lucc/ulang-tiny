package ulang

object Main {

  val preludeFile = getClass.getResource("/prelude.u").getFile()

  def main(args: Array[String]) = {
    // First execute the prelude file.  It defines some default symbols and
    // functions for all ulang files.
    Exec.run(preludeFile)
    // execute all files from the command line in order
    for (file <- args) {
      Exec.run(file)
    }
  }
}
