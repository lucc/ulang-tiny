import org.scalatest.funspec.AnyFunSpec
import java.io.File

class RunUlangTests extends AnyFunSpec with PreloadLoader {

  def testFiles(folder: String) =
    new File(getClass.getResource("/"+folder).getFile()).listFiles(
      (_, name) => name endsWith ".u").map(_.getAbsolutePath)
  def run(file: String, pending: Boolean = false) = it(file) {
    if (pending) pendingUntilFixed { ulang.Exec.runFile(file) }
    else Console.withOut(new java.io.ByteArrayOutputStream()) {
      ulang.Exec.runFile(file)
    }
  }
  def eval(snippet: String, pending: Boolean = false) = it(snippet) {
    if (pending) pendingUntilFixed { ulang.Exec.run(snippet) }
    else Console.withOut(new java.io.ByteArrayOutputStream()) {
      ulang.Exec.run(snippet)
    }
  }

  describe("run file") {
    for (testFile <- testFiles("tests"))   run(testFile)
    for (testFile <- testFiles("pending")) run(testFile, pending=true)
  }

  describe("special files") {
    it("the omega term should throw an exception") {
      assertThrows[java.lang.StackOverflowError] {
        ulang.Exec.runFile(getClass.getResource("/omega.u").getPath())
      }
    }
  }

  describe("pending snippets") {
    val snippets = List(
      // proving or elimination
      """show a \/ b ==> (a ==> c) ==> (b ==> c) ==> c;
      proof term lambda (Left x)  -> (lambda p1 -> lambda p2 -> p1 x)
                      | (Right x) -> (lambda p1 -> lambda p2 -> p2 x);""",
      // proofs with match expressions
      // symmetry of /\
      """show a /\ b ==> b /\ a;
      proof term lambda p -> match p with (x,y) -> (y,x);""",
      // symmetry of \/
      """show a \/ b ==> b \/ a;
         proof term lambda ant -> match ant with (Left x) -> Right x
                                               | (Right x) -> Left x;""",
      """show a \/ b ==> b \/ a;
         proof term lambda (Left x) -> Right x | (Right x) -> Left x;""",
      // define statements with strange expressions on the left
      "define (let x := y in x) := A;",
      // reordering bound variables
      """show (forall x y. a) ==> forall y x. a;
      proof term lambda f -> lambda y -> lambda x -> f x y;""",
      """show (forall x. forall y. a) ==> forall y. forall x. a;
      proof term lambda f -> lambda y -> lambda x -> f x y;""",
      """show (exists x y. a x y) ==> exists y x. a x y;
      proof term lambda (w1,(w2,pt)) -> (w2,(w1,pt))""",
      """show (exists x. exists y. a x y) ==> exists y. exists x. a x y;
      proof term lambda (w1,(w2,pt)) -> (w2,(w1,pt))""",
      // Schwichtenberg page 13
      """show (exists x. a x ==> b) ==> (forall x. a x) ==> b;
      proof term lambda (w,p) -> fa -> p fa w;""",
      """show (a ==> forall x. b x) ==> forall x. a ==> b x;
      proof term lambda f -> lambda var -> lambda precond -> f precond var;""",
      """show ((exists x. a x) ==> b) ==> forall x.a x ==> b;
      proof term lambda f -> lambda fa -> f (fa Term);""",
      """show (exists x. a ==> b x) ==> a ==> exists x. b x;
      proof term lambda (w,f) -> lambda pre -> (w,f pre);""",
    )
    for (snippet <- snippets) eval(snippet, pending=true)
  }

  describe("working snippets") {
    // proof with all quantifier
    eval("show (forall x. p x) ==> p Foo; proof term lambda x -> x Foo;")
    // proving introduction rules for exists
    eval("show a ==> exists x. a; proof term (lambda a -> (x, a));")
    eval("show p x ==> exists y. p y; proof term (lambda a -> (x, a));")
    // Schwichtenberg page 13
    eval("""show (forall x.a x ==> b) ==> (exists x. a x) ==> b;
         proof term lambda f -> lambda (w,p) -> f w p;""")
    eval("""show (forall x.a ==> b x) ==> a ==> forall x. b x;
         proof term lambda f -> lambda precond -> lambda var -> f var precond;""")
  }

  describe("invaild proofs") {
    it("universal quantifier introduction violating variable condition") {
      // it would work with "a" instead of "a x"
      val show = "show a x ==> forall x. a x;"
      val proof = "proof term lambda p -> lambda x -> p;"
      assertThrows[RuntimeException] { // Capturing variable x
        ulang.Exec.run(show + proof)
      }
    }
    it("existential quantifier elimination violating variable condition") {
      pendingUntilFixed {
      // it would work with "b" instead of "b x"
      val show = "show (exists x. a x) ==> (forall x. a x ==> b x) ==> b x;"
      val proof ="proof term lambda (w,p) -> lambda f -> f w p;"
      Console.withOut(new java.io.ByteArrayOutputStream()) {
        assertThrows[RuntimeException] {
          ulang.Exec.run(show + proof)
        }
      }
    }
    }
  }

  describe("rules") {
    describe("from propositional logic:") {
      describe("introduction rules") {
        val rules = List(
          // implication introduction / weakening
          "show a ==> b ==> a; proof term lambda x -> lambda y -> x;",
          // or introduction 1
          """show a ==> a \/ b; proof term lambda x -> Left x;""",
          // or introduction 2
          """show b ==> a \/ b; proof term lambda x -> Right x;""",
          // and introduction
          """show a ==> b ==> a /\ b; proof term lambda x -> lambda y -> (x,y);""",
        )
        for (snippet <- rules) eval(snippet)
      }
      describe("elimination rules") {
        val rules = Map(
          // implication elimination / modus ponens
          """show (a ==> b) ==> a ==> b;
          proof term lambda f -> lambda x -> f x;""" -> false,
          """show a ==> (a ==> b) ==> b;
          proof term lambda x -> lambda f -> f x;""" -> false,
          // or elimination
          """show a \/ b ==> (a ==> c) ==> (b ==> c) ==> c;
          proof term lambda (Left x)  -> (lambda p1 -> lambda p2 -> p1 x)
                          | (Right x) -> (lambda p1 -> lambda p2 -> p2 x);"""
          -> true,
          // and elimination
          """show a /\ b ==> (a ==> b ==> c) ==> c;
          proof term lambda (x,y) -> lambda f -> f x y;""" -> false,
        )
        for ((snippet, pending) <- rules) eval(snippet, pending)
      }
    }
    describe("from predicate logic:") {
      describe("introduction rules") {
        // universal quantifier introduction
        eval("show a ==> forall x. a; proof term lambda p -> lambda x -> p;")
        // existential quantifier introduction
        eval("show a t ==> exists x. a x; proof term lambda p -> (t,p);" )
      }
      describe("elimination rules") {
        // universal quantifier elimination
        eval("show (forall x. p x) ==> p t; proof term lambda f -> f t;")
        // existential quantifier elimination
        // TODO variable condition?
        eval("""show (exists x. a x) ==> (forall x. a x ==> b) ==> b;
          proof term lambda (w,p) -> lambda f -> f w p;""")
      }
    }
  }
}
