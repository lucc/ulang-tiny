import org.scalatest.funspec.AnyFunSpec
import ulang.{All, Ex, Id}

class Print extends AnyFunSpec {
  val x = Id("x")
  val y = Id("y")
  val foo = Id("foo")

  for ((qname, qcons) <- Map("forall" -> All, "exists" -> Ex)) {
    describe(qname + " quantifiers") {
      it("can have one variable") {
        val actual = qcons(x, foo).toString()
        assert(actual == qname + " x. foo")
      }
      it("can have many variables") {
        val actual = qcons(List(x, y), foo).toString()
        assert(actual == qname + " x y. foo")
      }
      it("can be nested but will be flattened for printing") {
        val actual = qcons(x, qcons(y, foo)).toString()
        assert(actual == qname + " x y. foo")
      }
    }
  }

}
