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

  object Eq extends Binary("=")

  object True extends Tag("true")
  object False extends Tag("false")

  object Zero extends Tag("0")
  object Succ extends Unary("+1")

  object And extends Binary("/\\")
  object Or extends Binary("\\/")
  object Imp extends Binary("==>")
  object Eqv extends Binary("<=>")

  case object Backtrack extends Throwable {
    override def fillInStackTrace = this
    override val getStackTrace = Array[StackTraceElement]()
  }
}