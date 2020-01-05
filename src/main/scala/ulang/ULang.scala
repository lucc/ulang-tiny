package ulang

object ULang {
  def main(args: Array[String]) = {
    val x = Id("x")
    val y = Id("y")
    val xs = Id("xs")
    val length = Id("length")
    val last = Id("last")

    val Zero = Tag("Zero")
    val Succ = Tag("Succ")
    val Nil = Tag("Nil")
    val Cons = Tag("Cons")

    val length_def = Lam(
      List(
        Case(
          List(Nil),
          Zero),
        Case(
          List(UnApp(UnApp(Cons, x), xs)),
          App(Succ, App(length, xs)))))

    val last_def = Lam(
      List(
        Case(
          List(UnApp(UnApp(Cons, x), Nil)),
          x),
        Case(
          List(UnApp(UnApp(Cons, x), xs)),
          App(last, xs))))

    import Eval._

    dyn += length -> norm(length_def, Map())
    dyn += last -> norm(last_def, Map())

    val zs = App(App(Cons, x), App(App(Cons, y), Nil))
    println(const(norm(App(length, zs), Map())))
    println(norm(App(last, zs), Map(y -> Tag("Y"))))
  }
}