# ulang

![tests](https://github.com/gernst/ulang-tiny/actions/workflows/test.yml/badge.svg)

## Compilation

The ulang project can be compiled with [mill](http://www.lihaoyi.com/mill/).
Use `mill ulang.compile` to compile the source code.  Use `mill ulang.run
some-file.u` to run the interpreter on some ulang file.

There also is a rudimentary REPL. It can be run with `mill -i repl.run`.  It is
currently lacking all niceties one might expect from a REPL (command line
editing, history, completion; some of these can be remedied by using
[rlwrap](https://github.com/hanslub42/rlwrap)) and also requires the user to
type whole Ulang blocks (including keyword and terminating semicolon).

## Overview of the code

The source code in the ulang directory is an interpreter for the ulang language
written in scala.

- The top level of the interpreter is defined in `ulang/src/ulang/Exec.scala`.
  It will read in script files, parse them into a list of commands (in
  `Exec.parse`) and then execute these commands (in `Exec.exec`).
- The parser is defined in `ulang/src/ulang/Parse.scala`.  Note that it accepts
  Java/C++ like line comments starting with `//`.
