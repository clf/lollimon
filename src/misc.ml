(***
Title: misc.ml

Description: Miscellaneous stuff

Author: Jeff Polakow
***)

value permute l = 
let rec perm res = fun [
  [] -> res |
  [h] -> [h::res] |
  [h::t] -> if Random.int 10 > 5 then perm [h::res] t else perm res (t@[h])
] in
perm [] l;

(*************************************** 
Miscellaneous stuff 
****************************************)
value traceLevel = ref 0;
value ps n s = if n <= traceLevel.val then do {print_string s; flush stdout} else ();
value nl = print_newline;

value soc = String.make 1;
value soi = string_of_int;
value ios = int_of_string;
value sob = string_of_bool;
value sof = string_of_float;

value rec remAssoc id = fun [
    [] -> [] |
    [(h as (id',_))::t] -> if id = id' then t else [h::remAssoc id t]
];

