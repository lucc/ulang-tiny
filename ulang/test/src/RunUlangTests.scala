import org.scalatest.funspec.AnyFunSpec
import java.io.File
import scala.reflect.ClassTag

class RunUlangTests extends AnyFunSpec with PreloadLoader {

  val mock_stdout = new java.io.ByteArrayOutputStream()
  def testFiles(folder: String): Array[String] = {
    val res = getClass.getResource("/"+folder)
    if (res == null) Array.empty
    else new File(res.getFile()).listFiles(
      (_, name) => name endsWith ".u").map(_.getAbsolutePath)
  }
  def mkTest(executor: (String => Any)) =
    (input: String, pending: Boolean) => it(input) {
      if (pending) pendingUntilFixed(executor(input))
      else Console.withOut(mock_stdout)(executor(input))
    }
  def run(file: String, pending: Boolean = false) = mkTest(ulang.Exec.runFile)(file, pending)
  def eval(snippet: String, pending: Boolean = false) = mkTest(ulang.Exec.run)(snippet, pending)
  def failRun[E <: AnyRef](file: String, pending: Boolean = false)(implicit c: ClassTag[E]) =
    mkTest(file => assertThrows[E](ulang.Exec.runFile(file)))(file, pending)
  def failEval[E <: AnyRef](snippet: String, pending: Boolean = false)(implicit c: ClassTag[E]) =
    mkTest(snippet => assertThrows[E](ulang.Exec.run(snippet)))(snippet, pending)

  describe("run file") {
    for (testFile <- testFiles("tests"))   run(testFile)
    for (testFile <- testFiles("pending")) run(testFile, pending=true)
    for (testFile <- testFiles("failing/StackOverflowError"))
      failRun[StackOverflowError](testFile)
    for (testFile <- testFiles("failing/RuntimeException"))
      failRun[RuntimeException](testFile)
  }

  describe("pending snippets") {
    def e = eval(_, pending=true)
    // Schwichtenberg page 13
    e("""show (exists x. a x ==> b) ==> (forall x. a x) ==> b;
      proof term lambda (Witness x w p) -> lambda fa -> p (Inst fa w lambda x -> x);""")
    e("""//show (not (not (not a))) ==> not a;
      show (((a ==> False) ==> False) ==> False) ==> a ==> False;
      proof term lambda h3n -> lambda ha -> h3n (lambda h1n -> h1n ha);""")
    // automatic forall instantiation with alpha equivalence
    e("""show (a t /\ exists y. phi y) ==> (forall x. (a x /\ exists y. p y) ==> b x) ==> b t;
      proof term lambda ha hfa -> hfa ha;""")
    // weak disjunction from Schwichtenberg
    // TODO can we use a function to compute the formula to be proven?
    e("""define wDis a b := (a ==> False) /\ (b ==> False) ==> False;
      show a \/ b ==> wDis a b;
      proof term lambda hd (hna,hnb) -> (lambda (Left ha) -> hna ha
                                              | (Right hb) -> hnb hb) hd;""")
    // completeness check for destruction with lambda terms is still missing
    it("incomplete pattern match") { pendingUntilFixed {
      assertThrows {
        ulang.Exec.run("""show a \/ b ==> (a ==> c) ==> (b ==> c) ==> c;
      // this should fail because the Right case is missing
      proof term lambda (Left x)  -> (lambda p1 -> lambda p2 -> p1 x);""")
      }
    }}
  }

  describe("working snippets") {
    // proving or elimination
    eval("""show a \/ b ==> (a ==> c) ==> (b ==> c) ==> c;
      proof term lambda (Left x)  -> (lambda p1 -> lambda p2 -> p1 x)
                      | (Right x) -> (lambda p1 -> lambda p2 -> p2 x);""")
    // symmetry of \/
    eval("""show a \/ b ==> b \/ a;
         proof term lambda (Left x) -> Right x | (Right x) -> Left x;""")
    // proofs with match expressions
    // symmetry of /\
    eval("""show a /\ b ==> b /\ a;
      proof term lambda p -> match p with (x,y) -> (y,x);""")
    // symmetry of \/
    eval("""show a \/ b ==> b \/ a;
      proof term lambda ant -> match ant with (Left x) -> Right x
                                           | (Right x) -> Left x;""")
    // proof with all quantifier
    eval("show (forall x. p x) ==> p Foo; proof term lambda x -> Inst x Foo lambda x -> x;")
    // proving introduction rules for exists
    eval("show a ==> exists x. a; proof term (lambda a -> Witness x x a);")
    eval("show p x ==> exists y. p y; proof term (lambda a -> Witness y x a);")
    // Schwichtenberg page 13
    eval("""show (forall x.a x ==> b) ==> (exists x. a x) ==> b;
        proof term lambda fa -> lambda (Witness x w p) -> Inst fa w lambda hab -> hab p;""")
    eval("""show (forall x.a ==> b x) ==> a ==> forall x. b x;
        proof term lambda hfa -> lambda ha -> forall var. Inst hfa var lambda hab -> hab ha;""")
    eval("""show (a ==> forall x. b x) ==> forall x. a ==> b x;
        proof term lambda f -> forall var. lambda precond -> Inst (f precond) var lambda x -> x;""")
    // TODO why do I have to put "var" and not "x" here ----------------------^
    eval("""show ((exists x. a x) ==> b) ==> forall x.a x ==> b;
      proof term lambda f -> forall x. lambda ha -> f (Witness x x ha);""")

    // how to construct implications
    eval("""show ((a ==> b) ==> c) ==> b ==> c;
        proof term lambda h p -> Inst (lambda x -> p) a h;""")
    // similarly with a cut
    eval("""show ((a ==> b) ==> c) ==> b ==> c;
        proof term lambda h p -> Cut (a ==> b)
            (lambda q -> p)
            (lambda r -> h r);""")

    eval("""show (exists x. a ==> b x) ==> a ==> exists x. b x;
        proof term lambda (Witness x w hab) -> lambda ha -> Witness x w (hab ha);""")

    // reordering bound variables
    val proof1 = """proof term lambda faxy -> forall y. forall x.
                    Inst faxy x lambda fay -> Inst fay y lambda x -> x;"""
    eval("show (forall x y. a) ==> forall y x. a;"+proof1)
    eval("show (forall x. forall y. a) ==> forall y. forall x. a;"+proof1)
    val proof2 = """proof term lambda (Witness x w1 (Witness y w2 pt))
                               -> Witness y w2 (Witness x w1 pt);"""
    eval("show (exists x y. a x y) ==> exists y x. a x y;"+proof2)
    eval("show (exists x. exists y. a x y) ==> exists y. exists x. a x y;"+proof2)
    eval("""// show a ==> not not a;
            show a ==> (a ==> False) ==> False;
            proof term lambda ha haf -> haf ha;""")
    // testing automatic forall instantiation
    eval("show a t ==> (forall x. a x ==> b x) ==> b t; proof term lambda ha hfa -> hfa ha;")
    // weak exists from Schwichtenberg
    // TODO can we use a function to compute the formula to be proven?
    eval("""define wEx x phi := (forall x. phi ==> False) ==> False;
      show (exists x. a x) ==> (forall x. a x ==> False) ==> False;
      proof term lambda (Witness x w p) fa -> fa p;
      """)
    // weak disjunction from Schwichtenberg
    // TODO can we use a function to compute the formula to be proven?
    eval("""define wDis a b := (a ==> False) /\ (b ==> False) ==> False;
      show a \/ b ==> (a ==> False) /\ (b ==> False) ==> False;
      proof term lambda hd (hna,hnb) -> (lambda (Left ha) -> hna ha
                                              | (Right hb) -> hnb hb) hd;""")
    // nested application
    eval("""show (a ==> b ==> c) ==> (a ==> b) ==> a ==> c;
          proof term lambda habc hab ha -> habc ha (hab ha);""")
    // nested implication with multible cases and patterns
    eval("""show a \/ b ==> c \/ d ==> (a /\ c) \/ (a /\ d) \/ (b /\ c) \/ (b /\ d);
         proof term lambda (Left ha)  (Left hc)  -> Left (ha, hc)
                         | (Left ha)  (Right hd) -> Right (Left (ha, hd))
                         | (Right hb) (Left hc)  -> Right (Right (Left (hb, hc)))
                         | (Right hb) (Right hd) -> Right (Right (Right (hb, hd)));""")
    // use an assumption with alpha equivalence
    eval("""show forall p. (forall x. p x) ==> (forall y. p y);
      proof term forall p. lambda a -> a;""")
    // lambdas that can not be type infered can still be used with a Cut
    eval("""show (((a ==> False) ==> False) ==> False) ==> a ==> False;
      proof term lambda h3n ha ->
        Cut ((a ==> False) ==> False)
            (lambda h1n -> h1n ha)
        lambda h2n -> h3n h2n;""")
  }

  describe("rules") {
    describe("from propositional logic:") {
      describe("introduction rules") {
        // implication introduction / weakening
        eval("show a ==> b ==> a; proof term lambda x -> lambda y -> x;")
        // or introduction 1
        eval("""show a ==> a \/ b; proof term lambda x -> Left x;""")
        // or introduction 2
        eval("""show b ==> a \/ b; proof term lambda x -> Right x;""")
        // and introduction
        eval("""show a ==> b ==> a /\ b; proof term lambda x -> lambda y -> (x,y);""")
      }
      describe("elimination rules") {
          // implication elimination / modus ponens
          eval("""show (a ==> b) ==> a ==> b;
          proof term lambda f -> lambda x -> f x;""")
          eval("""show a ==> (a ==> b) ==> b;
          proof term lambda x -> lambda f -> f x;""")
          // or elimination
          eval("""show a \/ b ==> (a ==> c) ==> (b ==> c) ==> c;
          proof term lambda (Left x)  -> (lambda p1 -> lambda p2 -> p1 x)
                          | (Right x) -> (lambda p1 -> lambda p2 -> p2 x);""")
          // and elimination
          eval("""show a /\ b ==> (a ==> b ==> c) ==> c;
          proof term lambda (x,y) -> lambda f -> f x y;""")
      }
    }
    describe("from predicate logic:") {
      describe("introduction rules") {
        // universal quantifier introduction
        eval("show a ==> forall x. a; proof term lambda p -> forall x. p;")
        // existential quantifier introduction
        eval("show a t ==> exists x. a x; proof term lambda p -> Witness x t p;" )
        // universal quantifier introduction violating variable condition
        // it would work with "a" instead of "a x"
        val show = "show a x ==> forall x. a x;"
        val proof = "proof term lambda p -> forall x. p;"
        failEval[RuntimeException](show + proof) // Capturing variable x
      }
      describe("elimination rules") {
        // universal quantifier elimination
        eval("show (forall x. p x) ==> p t; proof term lambda f -> Inst f t (lambda x -> x);")
        // existential quantifier elimination
        val exElim = "show (exists x. a x) ==> (forall x. a x ==> b) ==> b;"
        val proof ="proof term lambda (Witness x w p) -> lambda f -> Inst f w lambda ff -> ff p;"
        eval(exElim + " " + proof)
        // existential quantifier elimination violating variable condition
        // it would work with "b" instead of "b x"
        val badExElim = "show (exists x. a x) ==> (forall x. a x ==> b x) ==> b x;"
        failEval[RuntimeException](badExElim + proof)
      }
    }
  }
}
