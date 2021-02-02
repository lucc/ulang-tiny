import org.scalatest.funspec.AnyFunSpec

class MiscTest extends AnyFunSpec {
  describe("unwrap") {
    it("works on Some(_) values") {
      assert(ulang.unwrap(Some(1), "failed") == 1)
    }
  }
}
