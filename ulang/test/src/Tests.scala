
import org.scalatest.funsuite.AnyFunSuite
import ulang._

class Tests extends AnyFunSuite {

    test("unwrap works on Some(_) values") {
      assert(ulang.unwrap(Some(1), "failed") == 1)
    }

    test ("Another test ...") (pending)

}
