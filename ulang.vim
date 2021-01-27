" Vim syntax file for ulang
" Copy this file to a syntax/ folder in vim's runtimepath and add an
" autocommand to detect the syntax of ulang files to your filetype.vim:
"   autocmd BufRead,BufNewFile *.u   setfiletype ulang

if exists("b:current_syntax")
  finish
endif

let s:cpo_save = &cpo
set cpo&vim

syntax keyword ulangCommand define eval test data notation inductive coinductive proof
syntax keyword ulangCommand2 assume show
"syntax keyword ulangFixity infix infixr infixl prefix postfix
syntax keyword ulangTactic induction cases have case
syntax keyword ulangCommand3 qed use

syntax keyword ulangQuantifier forall exists
syntax match   ulangQuantifier /\./
syntax keyword ulangIf         if then else
syntax keyword ulangMatch      match with
syntax keyword ulangLet        let in
syntax keyword ulangLambda     lambda
syntax match   ulangLambda     /\s\zs->\||/

syntax region  ulangComment    start='//' end='$' contains=ulangTODO
syntax case ignore
syntax keyword ulangTODO       contained todo xxx fixme
syntax case match

highlight link ulangQuantifier Constant
highlight link ulangIf         ulangInlineConstruct
highlight link ulangMatch      ulangInlineConstruct
highlight link ulangLet        ulangInlineConstruct
highlight link ulangLambda     ulangInlineConstruct

syntax match ulangStatementTerminator /;/
syntax match ulangPrecedence /\[\(prefix\|infix[rl]\?\|postfix\)\s\+\d\+\]/
syntax match ulangType /\<[A-Z][A-Za-z]*/

" Link the defined syntax groups to predefined groups so that they will
" actually be highlighted.
highlight link ulangCommand             Keyword
highlight link ulangCommand2            Keyword
highlight link ulangInlineConstruct     Identifier
highlight link ulangTactic              Identifier
highlight link ulangCommand3            Keyword
highlight link ulangStatementTerminator Special
highlight link ulangPrecedence          String
highlight link ulangType                Type
highlight link ulangComment             Comment
highlight link ulangTODO                TODO

let b:current_syntax = "ulang"

let &cpo = s:cpo_save
unlet s:cpo_save
