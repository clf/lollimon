type mode = [Unknown | Input | Output of Bool];

value (allModes: ref (list (string * list mode))) = ref [];

value parseModes p = 
  let myfail () = raise (Stream.Error "Bad mode declaration") in
  let rec go = fun [
    Const "o" 0 [] -> parser [
      [: `(Kwd ".",_) :] -> [] |
      [: :] -> myfail ()
    ] |
    Const "->" 0 [_;typ] -> parser [
      [: `(Kwd "+",_); res = go typ :] -> [Input::res] |
      [: `(Kwd "-",_); res = go typ :] -> [Output False::res] |
      [: `(Kwd "*",_); res = go typ :] -> [Unknown::res] |
      [: :] -> myfail ()
    ] |
    _ -> myfail()
  ] in try
  go (fst (List.assoc p mysignature.val))
  with [e -> myfail()]
;

value isGround = 
let rec go bv = fun [
  (e as (Lam _ _ [_::_] | ExpSub _ _ _)) -> go bv (expose e) |
  Const _ _ args -> 
    List.fold_left (fun b tm -> b && go bv tm) True args |
  Lam _ dc [] -> go (bv + 1) dc |
  Var _ idx args -> 
    List.fold_left (fun b tm -> b && go bv tm) (idx <= bv) args |
  EVar _ _ _ _ -> False
] in
go 0;

value checkMode (head,body) =
let ctx = ref [] in
let rec doArgs f mode = fun [
  [] -> () |
  [tm::tms] -> 
    let (m,ms) = case mode of [
      None -> (Unknown,None) | 
      Some [m::ms] -> (m,Some ms) |
      _ -> raise (Failure "checkMode chkHead")
    ] in
    do {f m tm; doArgs f ms tms}
] in 
let doVar f = 
  let rec go bv = fun [
    (e as (Lam _ _ [_::_] | ExpSub _ _ _)) -> go bv (expose e) |
    Var _ idx args -> do {f idx; List.iter (go bv) args} | 
    Const _ _ args -> List.iter (go bv) args |
    Lam _ dc [] -> go bv dc |
    _ -> raise (Failure "checkMode addctx")
  ] in go 0
in
let addctx m idx =
  if idx <= bv then 
    if List.mem (idx,m) ctx.val then () else ctx.val := [(idx,m)::ctx.val];
  else ();
in
let chkHead = fun [
  Const c 0 args -> 
    let mode = try Some (List.assoc c allModes.val) with [
      Not_found -> None
    ] in
    doArgs (doVar (addctx mode)) args |
  _ -> raise (Failure "checkMode Head")
] in
let chkArg = fun [
  
] in
let rec chkBody isClause = fun [
  (e as (Lam _ _ [_::_] | ExpSub _ _ _)) -> chkBody isClause (expose e) |
  Const ("!" | "@" | "{}") 0 [x] -> chkBody isClause x |
  Const ("," | ";") 0 [x;y] -> do {
    chkBody isClause x; chkBody isClause y
  } |
  Const ("-o" | "=>" | "-@") 0 [x;y] -> do {
    chkBody (not isClause) x; chkBody isClause y
  } |
]
in do {
  chkHead head;
  chkBody True body
};







