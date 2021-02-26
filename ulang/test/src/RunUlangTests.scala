import org.scalatest.funspec.AnyFunSpec
import java.io.File

class RunUlangTests extends AnyFunSpec with PreloadLoader {

  def testFiles(folder: String) =
    new File(getClass.getResource("/"+folder).getFile()).listFiles(
      (_, name) => name endsWith ".u").map(_.getAbsolutePath)
  def run(file: String, pending: Boolean = false) = it(file) {
    Console.withOut(new java.io.ByteArrayOutputStream()) {
      if (pending) pendingUntilFixed { ulang.Exec.runFile(file) }
      else ulang.Exec.runFile(file)
    }
  }
  def eval(snippet: String, pending: Boolean = false) = it(snippet) {
    Console.withOut(new java.io.ByteArrayOutputStream()) {
      if (pending) pendingUntilFixed { ulang.Exec.run(snippet) }
      else ulang.Exec.run(snippet)
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
      // proving introduction rules for exists
      "show a ==> exists x. a; proof term (lambda a -> (x, a));",
      "show p x ==> exists y. p y; proof term (lambda a -> (x, a));",
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
      // proof with all quantifier
      "show (forall x. p x) ==> p Foo; proof term lambda x -> x Foo;",
      // reordering bound variables
      """show (forall x y. a) ==> forall y x. a;
      proof term lambda f -> lambda y -> lambda x -> f x y;""",
      """show (forall x. forall y. a) ==> forall y. forall x. a;
      proof term lambda f -> lambda y -> lambda x -> f x y;""",
      """show (exists x y. a x y) ==> exists y x. a x y;
      proof term lambda (w1,(w2,pt)) -> (w2,(w1,pt))""",
      """show (exists x. exists y. a x y) ==> exists y. exists x. a x y;
      proof term lambda (w1,(w2,pt)) -> (w2,(w1,pt))""",
    )
    for (snippet <- snippets) eval(snippet, pending=true)
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
        val rules = Map(
          // universal quantifier introduction
          // TODO variable condition? We can not write "a x" here because then
          // x would eb free in an open assumption.
          "show a ==> forall x. a; proof term lambda p -> lambda x -> p;"
          -> false,
          // existential quantifier introduction
          "show a t ==> exists x. a x; proof term lambda p -> (t,p);" -> true,
          )
        for ((snippet, pending) <- rules) eval(snippet, pending)
      }
      describe("elimination rules") {
        val rules = Map(
          // universal quantifier elimination
          "show (forall x. p x) ==> p t; proof term lambda f -> f t;" -> true,
          // existential quantifier elimination
          // TODO variable condition?
          """show (exists x. a x) ==> (forall x. a x ==> b) ==> b;
          proof term lambda (w,p) -> lambda f -> f w p;""" -> true,
          )
        for ((snippet, pending) <- rules) eval(snippet, pending)
      }
    }
  }
}
