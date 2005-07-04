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

  identifier : kind    : add declaration to user-defined signature

  identifier : type    : add declaration to user-defined signature

  any formula f        : try to prove f with current program context

  #fair p              : randomize order in which clauses of predicate p are 
                            selected for backchaining

  #cd "directory"      : cd to directory

  #pwd                 : print current working directory

  #include "file"      : load a program, contained in file

  #load "file"         : #clear followed by #include

  #query e l a f       : expect 'e' solutions to query 'f'. look for at most 'l' solutions;
                            attempt this query 'a' times.

  #context             : print the current program context (in logically compiled form).

  #signature           : prints the current user-defined signature

  #allsig              : prints the current user-defined signature and builtin signature

  #clear               : empties the program context and user-defined signature

  #clearctx            : empties the program context

  #clearsig            : empties the user-defined signature

  #assert f            : adds formula f to the unrestricted context

  #linear f            : adds formula f to the linear context

  #affine f            : adds formula f to the affine context

  #quit                : quits LolliMon interpreter

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

We also have universal and existential quantifiers represented by 'pi'
and 'sigma'. "forall x. p" for some formula "p" is conretely
represented as "pi x \ p x".

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

