package ulang

import arse._

trait Pretty {
  override def toString = Print.print(this)
}

object Print {
  import context._

  def print(name: String, args: List[Pretty], fixity: Fixity): String = (args, fixity) match {
    case (List(arg), _: Prefix) => "(" + name + " " + arg + ")"
    case (List(arg), _: Postfix) => "(" + arg + " " + name + ")"
    case (List(arg1, arg2), _: Infix) => "(" + arg1 + " " + name + " " + arg2 + ")"
  }
  
  def print(fun: Pretty, args: List[Pretty]): String = fun match {
    case Id(name, None) if isMixfix(name) =>
      print(name, args, mixfix(name))
    case _ => (fun :: args).mkString("(", " ", ")")
  }

  def print(expr: Expr): String = expr match {
    case Wildcard => "_"
    case Ite(test, left, right) => "if " + test + " then " + left + " else " + right
    case Lam(cases) => cases.mkString("lambda ", " | ", "")
    case Match(args, cases) => "match " + args.mkString(" ") + " with " + cases.mkString(" | ")
    case Let(eqs, body) => "let " + eqs.mkString(", ") + " in " + body
    case All(xs, body) => "forall " + xs.mkString(" ") + ". " + body
    case Ex(xs, body) => "exists " + xs.mkString(" ") + ". " + body
    case Apps(fun, args) => print(fun, args)
  }

  def print(cmd: Cmd): String = cmd match {
    case Defs(defs) => ???
    case Datas(names) => ???
    case Notation(fixs) => ???
    case Evals(exprs) => ???
    case Ind(cases, kind) => ???
    case Thm(assume, show, _) => print(assume, List(show))
  }

  def print(any: Val): String = any match {
    case Curry(fun, rargs, lex) => "[closure]"
    case Defer(expr, lex) => "[" + expr + "]"
    case Objs(fun, args) => print(fun, args)
  }

  def print(cs: Case): String = cs match {
    case Case(pats, body) => pats.mkString(" ") + " -> " + body
  }

  def print(bn: Case1): String = bn match {
    case Case1(pat, arg) => pat + " = " + arg
  }

  def assume(ant: List[Expr]): String = {
    ant.mkString("assume ", "; ", ";")
  }

  def show(suc: List[Expr]): String = {
    suc.mkString("show ", " \\/ ", ";")
  }

  def print(ant: List[Expr], suc: List[Expr]): String = {
    if (ant.isEmpty)
      show(suc)
    else
      assume(ant) + " " + show(suc)
  }

  def print(goal: Open): String = {
    val ant = goal.pre
    val suc = goal.suc
    print(ant, suc)
  }

  def format(proof: Proof, indent: String = ""): List[String] = proof match {
    case Closed =>
      List(indent + "qed")
    case goal: Open =>
      val first = indent + assume(goal.pre)
      val second = indent + show(goal.suc)
      val third = indent + "  sorry"
      first :: second :: third :: Nil
    case Step(prems, concl, tactic) =>
      val first = indent + assume(concl.pre)
      val second = indent + show(concl.suc)
      val third = indent + "proof " + tactic
      val rest = prems filterNot (_ == Closed) flatMap (format(_, indent + "  "))
      if (rest.isEmpty) {
        val fourth = indent + "  qed"
        first :: second :: third :: fourth :: Nil
      } else {
        first :: second :: third :: rest
      }
  }

  def print(tactic: Tactic): String = tactic match {
    case Auto => "auto"
    case Split(pat) => "split " + pat
    case Induct(pat, Least) => "induction " + pat
    case Induct(pat, Greatest) => "coinduction " + pat
  }
  
  def print(intro: Intro): String = {
    val Intro(rec, ant, suc) = intro
    (rec ++ ant).mkString(" /\\ ") + " ==> " + suc
  }

  def print(pretty: Pretty): String = pretty match {
    case Id(name, index) if isMixfix(name) => "(" + (name __ index) + ")"
    case Id(name, index) => name __ index
    case expr: Expr => print(expr)
    case any: Val => print(any)
    case cs: Case => print(cs)
    case bn: Case1 => print(bn)
    case goal: Open => print(goal)
    case cmd: Cmd => print(cmd)
    case intro: Intro => print(intro)
    case tactic: Tactic => print(tactic)
  }
}