import org.scalatest.funspec.AnyFunSpec

class ProofSnippetsTest extends AnyFunSpec with PreloadLoader {
  val pendingProofs = List(
    // order infariance
    """
    show (a ==> b ==> c) ==> b ==> a ==> c;
    proof term lambda x -> lambda y -> lambda z -> x z y;
    """,
    // chaining
    """
    show (b ==> c) ==> (a ==> b) ==> a ==> c;
    proof term lambda f -> lambda g -> lambda x -> f (g x);
    """,
    // modus ponens
    """
    show a ==> (a ==> b) ==> b;
    proof term lambda x -> lambda f -> f x;
    """,
    // or elimination
    """
    show a \/ b ==> (a ==> c) ==> (b ==> c) ==> c;
    proof lambda (Left x)  -> (lambda p1 -> lambda p2 -> p1 x)
               | (Right x) -> (lambda p1 -> lambda p2 -> p2 x);
    """,
    "show a ==> a; proof term (lambda v -> (lambda u -> u) v);",
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
