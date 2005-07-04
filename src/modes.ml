type mode = [Unknown | Input | Output of bool];

value allModes = ref [];

value parseModes p = 
  let myfail () = raise (Stream.Error "Bad mode declaration") in
  let rec go = fun [
    Const "o" 0 [] -> parser [
      [: `(Kwd ".",_) :] -> [] |
      [: :] -> myfail ()
    ] |
    Const "->" 0 [_;typ] -> parser [ (*** Const with level -2 are just for mode checking ***)
      [: `(Kwd "+",_); `(Ident _,_); res = go typ :] -> [Const "+" (-2) []::res] |
      [: `(Kwd "-",_); `(Ident _,_); res = go typ :] -> [Const "-" (-2) []::res] |
      [: `(Kwd "*",_); `(Ident _,_); res = go typ :] -> [Const "*" (-2) []::res] |
      [: :] -> myfail ()
    ] |
    Const "pi" 0 [Lam _ typ []] -> go typ |
    _ -> myfail()
  ] in 
  try go (fst (List.assoc p mysignature.val))
  with [e -> myfail()]
;


exception BadMode of string;

(***
  checkMode should only be called right after (right after
  residuating) parsing so there shouldn't be any actual EVars in head
  or body
***)
value checkMode head body evars =
(*
let _ = ps 0 ("checkMode: "^(term2str head)^" | "^(term2str body)^"\n") in
*)
  let outputs = ref [] in
  let headName = ref "" in
  let sub = makeSub evars (Some (-1)) in (*** EVars with level -1 are just for mode checking ***)
  let rec doArgs f mode = fun [
    [] -> () |
    [tm::tms] -> 
      let (m,ms) = match mode with [
        None -> (Const "*" (-2) [],None) | 
        Some [m::ms] -> (m,Some ms) |
        _ -> raise (Failure "checkMode chkHead")
      ] in
      do {f m tm; doArgs f ms tms}
  ] in 
  let doEVar f m = (*** do something to each mode EVar ***)
    let rec go = fun [
      (e as (Lam _ _ [_::_] | ExpSub _ _ _)) -> go (expose e) |
      Var _ _ args -> List.iter go args | 
      Const c (-1) [] -> () | 
      Const c 0 args -> 
        let args' = (*** ignore implicit type variables for mode analysis ***)
          if useTypes.val then 
            let n = 
              try snd (List.assoc c (mysignature.val @ signature.val)) 
              with [Not_found -> try let _ = int_of_string c in 0
              with [_ -> raise (Failure ("checkMode undefined constant: "^c))
              ]] 
            in
            nthTail n args 
          else args 
        in 
        List.iter go args' |
      Lam _ dc [] -> go dc |
      EVar _ rf (-1) args -> do {
        f m rf; 
        List.iter go args
      } |
      e -> raise (Failure ("checkMode doEVar: "^(term2str' True e))) (*** there shouldn't be any real EVars ***)
    ] in go
  in
  let initEV m rf = match (m,rf.val) with [
(*
let _ = ps 0 ("initEV m="^(term2str m)^" rf="^(term2str (EVar "?" rf (-2) []))^"\n") in
*)
    (Const "-" -2 [], Open _) -> do {
      outputs.val := [rf::outputs.val]; 
      rf.val := Inst (Const "*" (-2) [])
    } | 
    (_, Open _) -> rf.val := Inst m | 
    _ -> ()
  ] in
  let rec chkHead = fun [ (*** initialize mode EVars using mode declaration ***)
    (e as (Lam _ _ [_::_] | ExpSub _ _ _)) -> chkHead (expose e) |
    Const c 0 args -> 
      let _ = headName.val := c in
      let mode = try Some (List.assoc c allModes.val) with [
        Not_found -> None
      ] in
      doArgs (doEVar (initEV)) mode args |
    _ -> raise (Failure "checkMode Head")
  ] in
  let chkArg c isGoal m rf = 
(*
let _ = ps 0 ("chkArg "^(sob isGoal)^" "^(term2str m)^" "^(term2str' True (EVar "?" rf (-2) []))^"\n") in
*)
  match (isGoal, m, rf.val) with [
    (True, Const "-" -2 [], _) -> rf.val := Inst (Const "+" (-2) []) | 
    (True, Const "+" -2 [], Inst (Const "+" -2 [])) -> () |
    (True, Const "+" -2 [], _) -> raise (BadMode c) |

    (False, Const "-" -2 [], Inst (Const "+" -2 [])) -> () |
    (False, Const "-" -2 [], _) -> raise (BadMode c) |

    _ -> ()
  ] in
  let rec chkBody isGoal = fun [
    (e as (Lam _ _ [_::_] | ExpSub _ _ _)) -> chkBody isGoal (expose e) |
    Const (c as ("pi" | "sigma")) 0 [e] -> match expose e with [
      Lam nm e [] -> 
        let isGoal' = if c = "pi" then isGoal else not isGoal in
        if isGoal' then chkBody isGoal e 
        else chkBody isGoal (Lam nm e [newEVar False nm (Some (-1))]) |
      _ -> raise (Failure "checkModes: bad pi")
    ] |
    Lam _ e [] -> chkBody isGoal e |
    Const ("!" | "@" | "{}") 0 [x] -> chkBody isGoal x |
    Const ("," | ";" | "&") 0 [x;y] -> do {
      chkBody isGoal x; chkBody isGoal y
    } |
    Const ("-o" | "=>" | "-@") 0 [x;y] -> (*** order of subgoals in clauses must be reversed ***)
      if isGoal then do {chkBody (not isGoal) x; chkBody isGoal y} 
      else do {chkBody isGoal y; chkBody (not isGoal) x} |  
    (me as Const c 0 args) -> 
(*
      let _ = ps 0 ("chkBody "^(sob isGoal)^": "^(term2str' True me)^"\n") in
*)
      let mode = try Some (List.assoc c allModes.val) with [
        Not_found -> None
      ] in
      doArgs (doEVar (chkArg c isGoal)) mode args |
    _ -> raise (Failure "checkMode chkBody")
  ] in 
  let isInst rf = match rf.val with [
    Inst (Const "+" -2 []) -> () |
    _ -> raise (BadMode headName.val)
  ] in
match expose (ExpSub head sub []) with [
  Const "{}" 0 [head'] -> do {
    chkBody True (ExpSub body sub []);
    chkBody False head'
  } |
  head' -> do {
    chkHead head';
    chkBody True (ExpSub body sub []);
    List.iter isInst outputs.val
  }
];
