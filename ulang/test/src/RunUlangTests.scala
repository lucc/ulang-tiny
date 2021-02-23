import org.scalatest.funspec.AnyFunSpec
import java.io.File

class RunUlangTests extends AnyFunSpec with PreloadLoader {

  def testFiles(folder: String) =
    new File(getClass.getResource("/"+folder).getFile()).listFiles(
      (_, name) => name endsWith ".u").map(_.getAbsolutePath)
  def run(file: String) {
    Console.withOut(new java.io.ByteArrayOutputStream()) {
      ulang.Exec.runFile(file)
    }
  }
  def runPending(file: String) = pendingUntilFixed { run(file) }
  def eval(snippet: String) {
    Console.withOut(new java.io.ByteArrayOutputStream()) {
      ulang.Exec.run(snippet)
    }
  }
  def evalPending(snippet: String) = pendingUntilFixed { eval(snippet) }

  describe("run file") {
    for (testFile <- testFiles("tests"))
      it(testFile) { run(testFile) }
    for (testFile <- testFiles("pending"))
      it(testFile) { runPending(testFile) }
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
      """
      show a \/ b ==> (a ==> c) ==> (b ==> c) ==> c;
      proof term lambda (Left x)  -> (lambda p1 -> lambda p2 -> p1 x)
                      | (Right x) -> (lambda p1 -> lambda p2 -> p2 x);
      """,
      // proving introduction rules for exists
      "show a ==> exists x. a; proof term (lambda a -> (x, a));",
      "show p x ==> exists y. p y; proof term (lambda a -> (x, a));",
      // proofs with match expressions
      // symmetry of /\
      """show a /\ b ==> b /\ a; proof term lambda p -> match p with (x,y) -> (y,x);""",
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
    )
    for (snippet <- snippets)
      it(snippet) { evalPending(snippet) }
  }

  describe("rules") {
    describe("from propositional logic:") {
      describe("introduction rules") {
        val rules = List(
          // implication introduction / weakening
          "show a ==> b ==> a; proof term lambda x -> lambda y -> x;",
          // or introduction 1
          raw"show a ==> a \/ b; proof term lambda x -> Left x;",
          // or introduction 2
          raw"show b ==> a \/ b; proof term lambda x -> Right x;",
          // and introduction
          raw"show a ==> b ==> a /\ b; proof term lambda x -> lambda y -> (x,y);",
        )
        for (snippet <- rules)
          it(snippet) { eval(snippet) }
      }
      describe("elimination rules") {
        val rules = Map(
          // implication elimination / modus ponens
          """show (a ==> b) ==> a ==> b;
          proof term lambda f -> lambda x -> f x;""" -> Ok,
          // or elimination
          raw"""show a \/ b ==> (a ==> c) ==> (b ==> c) ==> c;
          proof term lambda (Left x)  -> (lambda p1 -> lambda p2 -> p1 x)
                          | (Right x) -> (lambda p1 -> lambda p2 -> p2 x);"""
          -> Pending,
          // and elimination
          raw"""show a /\ b ==> (a ==> b ==> c) ==> c;
          proof term lambda (x,y) -> lambda f -> f x y;""" -> Ok,
        )
        for ((snippet, state) <- rules) it(snippet) { state match {
          case Pending => evalPending(snippet)
          case Ok => eval(snippet)
        }}
      }
    }
    describe("from predicate logic:") {
      describe("introduction rules") {
        val rules = Map(
          // universal quantifier introduction
          // TODO variable condition?
          "show a ==> forall x. a; proof term lambda p -> lambda x -> p;"
          -> Ok,
          // existential quantifier introduction
          "show a ==> exists x. a; proof term lambda p -> (x,p);" -> Pending,
          )
        for ((snippet, state) <- rules) it(snippet) { state match {
          case Pending => evalPending(snippet)
          case Ok => eval(snippet)
        }}
      }
      describe("elimination rules") {
        val rules: Map[String, TestStatus] = Map(
          // universal quantifier elimination
          "show (forall x. p x) ==> p t; proof term lambda f -> f t;"
          -> Pending,
          // existential quantifier elimination
          // TODO variable condition?
          """show exists x. a ==> (forall x. a ==> b) ==> b;
          proof term lambda (w,p) -> lambda f -> f w p;""" -> Pending,
          )
        for ((snippet, state) <- rules) it(snippet) { state match {
          case Pending => evalPending(snippet)
          case Ok => eval(snippet)
        }}
      }
    }
  }
}

sealed trait TestStatus;
case object Pending extends TestStatus;
case object Ok extends TestStatus;
