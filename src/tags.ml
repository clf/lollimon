(***
Title: tags.ml

Description: Implementation of tag machinery for TF\

Author: Jeff Polakow
***)

(*************************************** 
Tags and lookup 
****************************************)

(***
  Linear Tags
***)
type availTyp = [Avail of int];
type tag = [Alias of ref (tag) | Val of (int * availTyp)];

value tag2str = fun [
  Alias _ -> "Alias" | 
  Val (x,Avail y) -> "Val ("^(soi x)^", Avail "^(soi y)^")"
];

value availVal = ref 0;
value newAvailVal () = do { incr availVal; Avail availVal.val };

value getval t = match t.val with [
  Val x -> x |
  _ -> raise (Failure "getval")
];

value longestChain = ref 0;
value tagLookup t = 
let currentChain = ref 0 in
let rec tagLookup t = match t.val with [
  Val _ -> (t,[]) |
  Alias l -> 
    let _ = incr currentChain in
    let (x,aliases) = tagLookup l in
    let new_aliases = 
      if x = l then aliases 
      else do { t.val := Alias x; [(t,l)::aliases] }
    in
    (x, new_aliases)
] in
let x = tagLookup t in
let _ = 
  if currentChain.val > longestChain.val then do {
    longestChain.val := currentChain.val; 
(*
    ps 0 ("new max chain of length: "^(soi currentChain.val)^"\n");
*)
    flush stdout
  }
  else () in
x;

value undoTagLookup aliases = 
let f (x,y) = x.val := Alias y in
List.iter f aliases
;

value withTags = ref 0;

(*************************************** 
Linear Tag Manipulations
****************************************)
value update f t kf ks = match t.val with [
  Val (num,avl) -> write t (Val (f num, avl)) kf ks |
  _ -> raise (Failure "update")
];

value update' f t = match t.val with [
  Val (num,avl) -> t.val := Val (f num, avl) |
  _ -> raise (Failure "update'")
];


value alias s d kf ks =
  let (snum,savl) = match s.val with [
                   Val (x,y) -> (x,y) | 
                   _ -> raise (Failure "alias 1")
                 ] in
  let (dnum,davl) = match d.val with [
                   Val (x,y) -> (x,y) | 
                   _ -> raise (Failure "alias 2")
                 ] in
  write s (Alias d) kf (fun kf1 ->
  write d (Val (dnum + snum, davl)) kf1 (fun kf2 ->
  ks kf2
  ))
;


(*************************************** 
  Context Formulae Tags

    the number with Unr is used by saturation checker-- it is used to
  prevent a disjunction from being broken down more than once.
***************************************)
type tagTyp = [Unr of int | Aff of ref float | Lin of ref (ref tag)];
value tagTyp2str = fun [
  Unr _ -> "Unr" |
  Aff n -> "Aff "^(string_of_float n.val) |
  Lin t -> "Lin "^(tag2str t.val.val)
];

value tagEq = fun [
  (Unr _, Unr _) -> True |
  (x,y) -> x = y
];
value tagEqCur x y = tagEq (x,y);

value isUnr = fun [Unr _ -> True | _ -> False];

value unrVal = ref 0;
value newUnrVal () = do { incr unrVal; Unr unrVal.val };












