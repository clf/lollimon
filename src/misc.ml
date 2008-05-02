(***
Title: misc.ml

Description: Miscellaneous stuff

Author: Jeff Polakow
***)

let permute l = 
let rec perm res x = match x with 
  [] -> res |
  [h] -> h :: res |
  h::t -> if Random.int 10 > 5 then perm (h::res) t else perm res (t @ [h])
 in
perm [] l

(*************************************** 
Miscellaneous stuff 
****************************************)
let traceLevel = ref 0
let psc n s = if n <= (!traceLevel) then (print_string (s()); flush stdout) else ()
let pss n s = if n <= (!traceLevel) then (print_string s; flush stdout) else ()
let nl = print_newline

let soc = String.make 1
let soi = string_of_int
let ios = int_of_string
let sob = string_of_bool
let sof = string_of_float

let rec remAssoc id x = 
  (match x with
    [] -> [] |
    (key,value) :: t -> 
      if id = key
      then t 
      else (key,value) :: remAssoc id t)

let x = 0
