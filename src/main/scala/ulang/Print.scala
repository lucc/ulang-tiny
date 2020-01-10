package ulang

import arse._

trait Pretty {
  override def toString = Print.print(this)
}

object Print {
  def print(fun: Pretty, args: List[Pretty]): String = (fun, args) match {
    case (Id(name, _: Prefix), List(arg)) => "(" + name + " " + arg + ")"
    case (Id(name, _: Postfix), List(arg)) => "(" + arg + " " + name + ")"
    case (Id(name, _: Infix), List(arg1, arg2)) => "(" + arg1 + " " + name + " " + arg2 + ")"
    case (fun, args) => (fun :: args).mkString("(", " ", ")")
  }

  def print(pat: Pat): String = pat match {
    case Wildcard => "_"
    case Strict(pat) => "!" + pat
    case UnApps(fun, args) => print(fun, args)
  }

  def print(expr: Expr): String = expr match {
    case Ite(test, left, right) => "if " + test + " then " + left + " else " + right
    case Lam(cases) => cases.mkString("\\ ", " | ", "")
    case Match(args, cases) => "match " + args.mkString(" ") + " with " + cases.mkString(" | ")
    case Let(eqs, body) => "let " + eqs.mkString(", ") + " in " + body
    case Binder(Id(name, Bindfix), cs) => "(" + name + " " + cs + ")"
    case Apps(fun, args) => print(fun, args)
  }

  def print(cmd: Cmd): String = cmd match {
    case Defs(defs) => ???
    case Datas(names) => ???
    case Notation(fixs) => ???
    case Evals(exprs) => ???
    case Fix(cases, kind) => ???
    case Thm(assume, show, _) => print(assume, List(show))
  }

  def print(any: Val): String = any match {
    case Curry(fun, rargs, lex) => "[closure]"
    case Defer(expr, lex, _) => "[" + expr + "]"
    case Objs(fun, args) => print(fun, args)
  }

  def print(cs: Case): String = cs match {
    case Case(pats, body) => pats.mkString(" ") + " -> " + body
  }

  def print(bn: Bind): String = bn match {
    case Bind(pat, arg) => pat + " = " + arg
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
      val first = indent + concl
      val second = indent + "proof " + tactic
      val rest = prems filterNot (_ == Closed) flatMap (format(_, indent + "  "))
      if (rest.isEmpty) {
        val third = indent + "  qed"
        first :: second :: third :: Nil
      } else {
        first :: second :: rest
      }
  }

  def print(tactic: Tactic): String = tactic match {
    case Auto => "auto"
    case Split(pat) => "split " + pat
    case Ind(pat, Least) => "induction " + pat
    case Ind(pat, Greatest) => "coinduction " + pat
  }

  def print(pretty: Pretty): String = pretty match {
    case Id(name, Nilfix) => name
    case Id(name, _) => "(" + name + ")"
    case pat: Pat => print(pat)
    case expr: Expr => print(expr)
    case any: Val => print(any)
    case cs: Case => print(cs)
    case bn: Bind => print(bn)
    case goal: Open => print(goal)
    case cmd: Cmd => print(cmd)
    case tactic: Tactic => print(tactic)
  }
}