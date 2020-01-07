package ulang

import arse._

trait Pretty {
  override def toString = Printer.print(this)
}

object Printer {
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

  def print(cmd: Cmd): String = {
    ???
  }

  def print(any: Val): String = any match {
    case Curry(fun, rargs, lex) => "[closure]"
    case Defer(expr, lex, _) => "[" + expr + "]"
    case Objs(fun, args) => print(fun, args)
  }

  def print(cs: Case) = cs match {
    case Case(pats, body) => pats.mkString(" ") + " -> " + body
  }

  def print(bn: Bind) = bn match {
    case Bind(pat, arg) => pat + " = " + arg
  }

  def print(pretty: Pretty): String = pretty match {
    case Id(name, Nilfix) => name
    case Id(name, _) => "(" + name + ")"
    case pat: Pat => print(pat)
    case expr: Expr => print(expr)
    case any: Val => print(any)
    case cs: Case => print(cs)
    case bn: Bind => print(bn)
    // case cmd: Cmd => print(cmd)
  }
}