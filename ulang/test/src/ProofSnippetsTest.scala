import org.scalatest.funspec.AnyFunSpec

class ProofSnippetsTest extends AnyFunSpec with PreloadLoader {
  val pendingProofs = List(
    // or elimination
    """
    show a \/ b ==> (a ==> c) ==> (b ==> c) ==> c;
    proof lambda (Left x)  -> (lambda p1 -> lambda p2 -> p1 x)
               | (Right x) -> (lambda p1 -> lambda p2 -> p2 x);
    """,
    // introduction rules for exists
    "show a ==> exists x. a; proof term (lambda a -> (x, a));",
    "show p x ==> exists y. p y; proof term (lambda a -> (x, a));",
  )
  val pendingDefines = List(
    )
  val pendingScripts = pendingProofs ++ pendingDefines
  describe("test small pending scripts") {
    for (snippet <- pendingScripts) {
      it(snippet) { pendingUntilFixed { ulang.Exec.run(snippet) } }
    }

  }
}
