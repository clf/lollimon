This is a prototype implementation of LolliMon.

The system is essentially Lolli extended with monadically encapsulated
synchronous connectives a la CLF, or if you prefer, CLF without terms.

The system additionally contains experimental support for affine
hypotheses (and an affine modality), and additive disjunction and
additive falsehood in the monad.

The implementation is done in OCaml (3.07+2 and up) and uses the
revised OCaml syntax. The code was written by Jeff Polakow.

--------------------------------------------------------

To start system (from lollimon/src directory):

  unix_prompt> ocaml camlp4r.cma
  
  # #use "main.ml";
  :
  :
  # go True;

If you want to turn off type-checking, use "go False" to start the system.

The interpreter recognizes the following commands:

  0) identifier : kind    : add declaration to user-defined signature

  0) identifier : type    : add declaration to user-defined signature

  1) any formula f        : try to prove f with current program context

  2) #ordered p           : preserve order of clauses for predicate p

  2) #fair p              : randomize order in which clauses of predicate p are 
                            selected for backchaining

  2) #cd "directory"      : cd to directory

  2) #pwd                 : print current working directory

  2) #include "file"      : load a program, contained in file

  2) #load "file"         : #clear followed by #include

  2) #query e l a f       : expect 'e' solutions to query 'f'. look for at most 'l' solutions;
                            attempt this query 'a' times.

  3) #context             : print the current program context (in logically compiled form).

  3) #signature           : prints the current user-defined signature

  3) #allsig              : prints the current user-defined signature and builtin signature

  4) #clear               : empties the program context and user-defined signature

  4) #clearctx            : empties the program context

  4) #clearsig            : empties the user-defined signature

  5) #assert f            : adds formula f to the unrestricted context

  5) #linear f            : adds formula f to the linear context

  5) #affine f            : adds formula f to the affine context

  6) #quit                : quits LolliMon interpreter

Formulas, and types, must end in a period.

Kind constructors: 'type', '->'.
E.g. 'list' has kind 'type -> type'.

Type constructors: '->', 'list', 'int', 'string', 'o' (for predicates).
Types can have prenex polymorphism, type variables are upper case identifiers.
E.g. '::' has type 'T -> list T -> list T'.

Built-in infix term constructors are: '+', '-', '::' and 'nil'.
The system also recognizes integers for use with '+' and '-'.

'x \ M' is the syntax for lambda terms 
where 'x' is a bound variable in 'M'.

Built-in infix formula contructors are:
 ':-', 'o-', '@-', '<=',     (lowest precedence)
 '-o', '-@', '=>',
 ';',
 ',', '&',
 '=', 'is', '>'        (highest precedence)

'-o' is linear implication, '=>' is unrestricted implication, '-@' is
affine implication, ';' is additive disjunction, ',' is multiplicative
conjunction, '&' is additive conjunction.

Built-in prefix formula constructors are:  '!', '@' 
which are the unrestricted and affine modalities.

':-' is equivalent to 'o-' and we encourage avoiding its use
in CLF encodings (it remains in the system for compatibility with
earlier Lolli programs).

Other built-in formulas are: 'top', 'one', 'zero', 'write', 'nl', 'once' 
where 'write' prints it's argument-- either a formula or a term
or a string constant (with basic escape sequences); and 'once' forces
a formula to be deterministic (i.e. 'once f' will produce at most one
proof of 'f').

--------------------------------------------------------

Notes:

  '#query e l a f' attempts to find (min 'e' 'l') solutions to query
'f'. If 'l' is 0 then the declaration is skipped. If 'e' is 0 (and 'l'
> 0) then the declaration succeeds if 'f' has no solution. If 'l'
> 'e' then the declaration fails if more than 'e' solutions exist. The
system will try this declaration at most 'a' times before really
failing. Thus Twelf's '%query 1 * q' = '#query 1 2 1 q'.

  By default, the system does not remember the order of clauses. Only
predicates which have been explicitly declared as ordered will 
necessarily be tried in order.

  All clauses in a program file will be loaded into the unrestricted
context unless the clause is preceded by '#linear', or '#affine'. 

  Program files may explicitly include other program files with the
'#include "file"' or '#load "file"' commands.

  If you interrupt execution with Ctrl-C, you will
drop back to the LolliMon top level, but the context will
be precisely in the state at which the program was interrupted.
Do #load again or #clear to obtain a clean state.


--------------------------------------------------------

Known Bugs:

  Support for user-declared type functions is unstable. The system will 
accept declarations such as 'pair: type -> type -> type.' but 
type-checking will be incorrect.

  Support for ';' and 'zero' in the monad is unstable. Using monadic clauses with 
';' or 'zero' occasionally causes strange system behavior.

  Saturation checking for open terms is experimental, and a bit unstable.

--------------------------------------------------------

Sample session (started from repository directory):

    LolliMon> #cd "/home/jp/lollimon/examples/lolli"
    LolliMon> #load "perm.lo"
    Looking for 2 solutions to query: perm (1 :: 2 :: nil) L
    :
    :
    Success.
    perm.lo is Ok.
    LolliMon> tp : type.
    LolliMon> a : tp.
    LolliMon> b : tp.
    LolliMon> perm (a::b::nil) L.
    Success 
    with [L := b :: a :: nil]
    More? y
    Success 
    with [L := a :: b :: nil]
    More? y
    Failure

    LolliMon> #quit

