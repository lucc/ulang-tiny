import org.scalatest.funspec.AnyFunSpec

class ProofSnippetsTest extends AnyFunSpec with PreloadLoader {
  val pendingProofs = List(
    // order invariance
    """
    show (a ==> b ==> c) ==> b ==> a ==> c;
    proof term lambda x -> lambda y -> lambda z -> x z y;
    """,
    // or elimination
    """
    show a \/ b ==> (a ==> c) ==> (b ==> c) ==> c;
    proof lambda (Left x)  -> (lambda p1 -> lambda p2 -> p1 x)
               | (Right x) -> (lambda p1 -> lambda p2 -> p2 x);
    """,
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
