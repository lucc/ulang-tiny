import scala.language.implicitConversions

package object ulang {
  type Env = Map[Id, Val]

  def backtrack = {
    throw Backtrack
  }

  implicit class Control[A](first: => A) {
    def or[B <: A](second: => B) = {
      try {
        first
      } catch {
        case Backtrack =>
          second
      }
    }
  }

  case object Backtrack extends Throwable {
    override def fillInStackTrace = this
    override val getStackTrace = Array[StackTraceElement]()
  }
}