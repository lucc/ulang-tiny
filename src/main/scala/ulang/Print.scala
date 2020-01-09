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
    case Apps(fun, args) => print(fun, args)
  }

  def print(cmd: Cmd): String = cmd match {
    case Defs(defs) => ???
    case Datas(names) => ???
    case Notation(fixs) => ???
    case Evals(exprs) => ???
    case Fix(cases, kind) => ???
    case Thm(assume, show) => print(assume, List(show))
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

  def print(ant: List[Expr], suc: List[Expr]): String = {
    if (ant.isEmpty)
      "show " + suc.mkString(" \\/ ")
    else
      "assume " + ant.mkString("", "; ", ";") + " show " + suc.mkString(" \\/ ")
  }

  def print(goal: Goal): String = {
    val eqs = goal.eqs map { case (l, r) => Eq(l, r) }
    val ant = goal.ant
    val suc = goal.suc
    print(eqs.toList ++ ant, suc)
  }

  def print(pretty: Pretty): String = pretty match {
    case Id(name, Nilfix) => name
    case Id(name, _) => "(" + name + ")"
    case pat: Pat => print(pat)
    case expr: Expr => print(expr)
    case any: Val => print(any)
    case cs: Case => print(cs)
    case bn: Bind => print(bn)
    case goal: Goal => print(goal)
    case cmd: Cmd => print(cmd)
  }
}