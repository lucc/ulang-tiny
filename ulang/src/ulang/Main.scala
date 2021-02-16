package ulang

object Main {

  val preludeFile = getClass.getResource("/prelude.u").getFile()

  /** Load the prelude file
   *
   *  The prelude file defines some default symbols and functions for all
   *  ulang files.  These are also needed in some part of the test suite.
   */
  def loadPrelude() { Exec.runFile(preludeFile) }

  def main(args: Array[String]) = {
    loadPrelude()
    // execute all files from the command line in order
    for (file <- args) {
      Exec.runFile(file)
    }
  }
}
