(***
Title: index.ml

Description: Implementation of discrimination tree data structure
  for LolliMon.  

Author: Jeff Polakow
***)

type indexElm 'a = [
  Body |
  App | 
  Lam' of string |
  Const' of string and int | 
  Var' of int | 
  EVar' of bool and string and ref evopt and int and list term | 
  FreshEV of string and int and list (int * string) and list term | 
  FrEV of int and list (int * string) and list term |
  Alt of list (list (indexElm 'a)) |
  Leaf of list 'a
];

value list2str f sep = fun [
  [] -> "" |
  [h::t] -> (f h)^(list2str f sep t)
];

value rec indexElm2str f = fun [
  Body -> "Body" |
  App -> "@" |
  Lam' nm -> "Lam("^nm^")" |
  Const' c lvl -> c(*^"<"^(soi lvl)^">"*) |
  Var' i -> "(Var "^(soi i)^")" |
  EVar' inst nm rf lvl args -> 
    "(EVar' "^(sob inst)^" "^(term2str' True (EVar nm rf lvl args))^")" |
  FreshEV nm i evs args -> "(FEV "^nm^" "^(soi i)^(if evs = [] then "" else "("^(list2str (fun (i,nm') -> "("^(soi i)^","^nm'^")") " " evs)^")")^
                           "{"^(list2str (term2str' True) "," args)^"})" |
  FrEV i evs args-> "(FrEV "^(soi i)^(if evs = [] then "" else "("^(list2str (fun (i,nm') -> "("^(soi i)^","^nm'^")") " " evs)^")")^
                  "{"^(list2str (term2str' True) "," args)^"})" |
  Leaf x -> "Leaf("^(soi (List.length x)) (*^(list2str f " | " x)*)^")" |
  Alt alts -> "Alt"^(index2str f alts)
]
and idx2str f i = "["^(list2str (indexElm2str f) " " i)^"]" 
and index2str f i = "[" ^ (list2str (fun x -> x) ","  (List.map (idx2str f) i))^"]";


value flatterm (hd, bdy) =
let lookup id l = try Some (List.assoc id l) with [Not_found -> None] in
let evars = ref [] in
let rec apps n = if n > 0 then [App::apps (n-1)] else [] in
let rec go bvN inPrefix = 
fun [
  (t as ExpSub _ _ _) -> go bvN inPrefix (expose t) |
  (ev as EVar nm rf lvl args) -> match rf.val with [
    Open _ -> [EVar' False nm rf lvl args] |
    Inst tm -> go bvN inPrefix tm 
  ] |
  (t as Lam _ _ [_::_]) -> go bvN inPrefix (expose t) |
  Lam nm bdy [] -> [Lam' nm::go ((fst bvN) + 1,[nm::snd bvN]) False bdy] |
  Const "pi" 0 [lam] when inPrefix -> match expose lam with [
    Lam _ tm [] -> go bvN True tm |
    _ -> raise (Failure "flatterm: bad pi")
  ] |
  Const c lvl args -> 
    (apps (List.length args)) @ 
    [Const' c lvl::List.flatten (List.map (go bvN False) args)] | 
  Var nm idx args -> 
    if idx <= fst bvN then 
      (apps (List.length args)) @ 
      [Var' idx::List.flatten (List.map (go bvN False) args)]
    else 
    let rec getNewEVs = fun [
      [] -> [] |
      [EVar _ rf _ args'::args] -> match rf.val with [
        Open _ -> (getNewEVs args')@(getNewEVs args) |
        Inst tm -> getNewEVs [addArgs tm args'::args]
      ] |
      [(h as (Lam _ _ [_::_] | ExpSub _ _ _ ))::args] -> getNewEVs [expose h::args] |
      [Var nm i args'::args] -> 
        (if i > fst bvN && not (List.mem (i - fst bvN) evars.val) then
          do { evars.val := [i - fst bvN::evars.val]; [(i,nm)] }
         else []) @ (getNewEVs args') @ (getNewEVs args) |
      [Const _ _ args'::args] -> (getNewEVs args')@(getNewEVs args) |
      [_::args] -> getNewEVs args
    ] in 
    if List.mem (idx - fst bvN) evars.val then 
      [FrEV (idx - fst bvN) (getNewEVs args) args]
    else 
      do {
        evars.val := [idx - fst bvN::evars.val];
        [FreshEV nm (idx - fst bvN) (getNewEVs args) args]
      }
] in
let hd' = go (0,[]) True hd in
let bdy' = match bdy with [
  Some (bdy,lf) -> [Body::go (0,[]) False bdy] @ [Leaf [lf]] | 
  None -> []
] in
hd' @ bdy';

(*
value flatterm exp ((hd,bdy),v) = flatterm' exp (hd,Some (bdy,v));
*)

value rec sameArgs = fun [
  ([],[]) -> True |
  ([Var _ idx1 args1::t1],[Var _ idx2 args2::t2]) ->
    if idx1 = idx2 && sameArgs (args1,args2) then sameArgs (t1,t2) else False |
  ([h1::t1],[h2::t2]) -> if h1 = h2 then sameArgs (t1,t2) else False |
  _ -> False
];

value idxEq' shallow = fun [
  (FreshEV _ idx1 _ args1, FreshEV _ idx2 _ args2) -> 
    idx1 = idx2 && sameArgs (args1, args2) |
  (FrEV idx1 _ args1, FrEV idx2 _ args2) -> idx1 = idx2 && sameArgs (args1, args2) |
  (Lam' _, Lam' _) -> True |
  (EVar' inst1 _ rf1 _ args1, EVar' inst2 _ rf2 _ args2) ->
    rf1 == rf2 && inst1 = inst2 && sameArgs (args1, args2) |
  (x,y) -> x = y
];

value idxEq = idxEq' False;


value nextTrm fair (idx,env) kf ks =
let _ = ps 10 ("nextTrm: "^(idx2str 0 idx)^"\n") in
let rec goAlts bvN env x kf ks = match if fair then permute x else x with [
  [alt::alts] -> 
    go bvN env alt (fun [Fail _ -> goAlts bvN env alts kf ks | x -> kf x]) ks |
  [] -> kf (Fail "no more alts")
]  
and go bvN env x kf ks = match x with [
  [] -> kf (Fail "none") |
  [App::idx] -> 
    go bvN env idx kf (fun (tm1,(idx1,env1)) kf ->
    go bvN env1 idx1 kf (fun (tm2,(idx2,env2)) kf ->   
    ks (addArgs tm1 [tm2], (idx2,env2)) kf
    )) |
  [Lam' nm::idx] -> 
    go (fst bvN + 1,[nm::snd bvN]) env idx kf (fun (tm,(idx,env)) kf ->
    ks (Lam nm tm [], (idx,env)) kf
    ) |
  [Const' c lvl::idx] -> ks (Const c lvl [], (idx,env)) kf |
  [Var' i::idx] -> ks (Var (newEVarNm "x") i [], (idx,env)) kf |
  [FreshEV nm i evs args::idx] ->
    let newEVs = 
      [(i,newEVar False nm None) ::
       List.map (fun (i,nm') -> (i, newEVar False nm' None)) evs
      ] 
    in 
    let ev = addArgs (snd (List.hd newEVs)) args in
    let env = List.rev_append newEVs env in
    ks (ev, (idx,env)) kf |
  [FrEV i evs args::idx] ->
    let newEVs = List.map (fun (i,nm) -> (i, newEVar False nm None)) evs in 
    let ev = 
      try addArgs (List.assoc i env) args 
      with [Not_found -> raise (Failure "nextTrm EV")] 
    in
    let env = List.rev_append newEVs env in
    ks (ev, (idx,env)) kf |
  [EVar' False nm rf lvl args::idx] -> ks (EVar nm rf lvl args, (idx,env)) kf |
  [EVar' True nm rf lvl args::idx] -> go bvN env idx kf ks |
  [Alt alts] -> goAlts bvN env alts kf ks |
  x -> raise (Failure "nextTrm")
] in
go (0,[]) env idx kf ks;

value nextLeaf idx kf ks = 
let rec next lfs kf ks = match lfs with [
  [] -> kf (Fail "no more leaves") |
  [h::t] -> 
    ks h (fun msg -> match msg with [Fail _ -> next t kf ks | _ -> kf msg ])
] in
match idx with [
  [Leaf lfs] -> next lfs kf ks |
  _ -> raise (Failure "nextLeaf") 
];


value addPrefix t env = 
let rec go = fun [
  [] -> t |
  [(_,EVar nm _ _ _)::env] -> Const "pi" 0 [Lam nm (go env) []] |
  _ -> raise (Failure "addPrefix")
] in
go (List.sort (fun (x,_) (y,_) -> compare x y) env);


value showStr pred user all linear n idx f = 
if traceLevel.val >= n then 
(*
  let _ = match pred with [
    None -> ps 0 "showStr any pred\n" |
    Some c -> ps 0 ("showStr pred "^c^"\n")
  ] in
*)
  nextTrm False ([Alt idx],[]) (fun _ -> ()) (fun (hd,(idx,env)) kf ->
  match idx with [
    [Body :: x] -> nextTrm False (x,env) kf (fun (tm,(idx,env)) kf -> 
      let ok1 = match pred with [
        None -> True |
        Some c -> match expose hd with [Const c' _ _ -> c = c' | _ -> False] 
      ] in
      if not ok1 then kf (Fail "skip") else
      match idx with [
        [Leaf lf] -> nextLeaf idx kf (fun v kf -> do {
          if linear && (isUnr v) then () else match user with [
            None -> 
              ps n (term2str' True (normalize (addPrefix (Const "-o" 0 [tm;hd]) env))^
                  " -- "^(f v)^"\n") |
            Some (avl,al,ar) -> 
              let (ok,t) = match v with [
                Unr n -> (True,"") |
                Aff x -> (al < x.val && x.val <= ar, " -- Aff") |
                Lin x -> (snd (getval x.val) = avl, " -- Lin")
              ] in
              if ok then
                ps n (term2str' True (normalize (addPrefix (Const "-o" 0 [tm;hd]) env))^
                      t^"\n")
              else ()
          ];
          if all then kf (Fail "next") else ()
        }) |
        _ -> raise (Failure "show1")
      ]) |
    _ -> () (*raise (Failure "show2")*)
  ])
else ();


value env2sub offset env = 
let rec makeSVars res n = 
  if n = 0 then res else makeSVars (Sub (Var (newEVarNm "x") n []) res) (n - 1)
in
let rec makeSub = fun [
  [] -> Id 0 |
  [(_,v)::env] -> Sub v (makeSub env)
] in
makeSVars (makeSub (List.sort (fun (x,_) (y,_) -> compare x y) env)) offset;

value find fair idx tm kf ks =
  let showAlts = ref False in
  let qry = flatterm (tm,None) in
  let rec findAlt bvN ienv (alts,tm) kf ks = 
    let alts = if fair then permute alts else alts in
    match (alts,tm) with [
      ([alt::alts],tm) -> 
        find bvN ((alt,ienv),tm) 
          (fun [Fail _ -> findAlt bvN ienv (alts,tm) kf ks | x -> kf x]) 
          ks |
      ([],tm) -> kf (Fail "no more choices")
    ]
  and find bvN x kf ks = 
    let mkTrm tm env = ExpSub tm (env2sub (List.hd bvN) env) [] in
  match x with [
    (([Body :: bdy],env),([],_)) -> 
      nextTrm fair (bdy,env) kf (fun (tm, (idx', env')) kf -> 
      nextLeaf idx' kf (fun v kf ->
      ks (mkTrm tm env', v) kf
      )) |
    (([Alt alts],ienv),qry) -> findAlt bvN ienv (alts, qry) kf ks |
    (idx,(qry as ([EVar' False _ _ _ _::_],_))) ->
      nextTrm fair idx kf (fun (tm, idx') kf ->
      nextTrm False qry kf (fun (ev, qry') kf ->
      let kf' = fun [
        Fail msg -> do { ps 4 ("unify failed: "^msg^"\n"); kf (Fail msg) } |
        x -> kf x
      ] in
      unify (mkTrm tm (snd idx'), ev) kf' (fun kf ->
      find (List.tl bvN) (idx',qry') kf ks
      ))) |
    ((idx as ([(FreshEV _ _ _ _ | FrEV _ _ _ | EVar' _ _ _ _ _)::_],_)),qry) ->
      nextTrm fair idx kf (fun (ev, idx') kf ->
      nextTrm False qry kf (fun (tm, qry') kf ->
      let kf' = fun [
        Fail msg -> do { ps 4 ("unify failed: "^msg^"\n"); kf (Fail msg) } |
        x -> kf x
      ] in
      unify (mkTrm ev (snd idx'), mkTrm tm (snd qry')) kf' (fun kf ->
      find (List.tl bvN) (idx',qry') kf ks
      ))) |
    (([Lam' _::idx], ienv), ([Lam' _::qry], qenv)) -> 
       find [List.hd bvN + 1::List.tl bvN] ((idx, ienv), (qry, qenv)) kf ks |
    (([App::idx], ienv), ([App::qry], qenv)) -> 
       find [List.hd bvN::bvN] ((idx, ienv), (qry, qenv)) kf ks |
    (([h::t], ienv), ([h'::t'], qenv)) -> 
       if idxEq (h, h') then 
         find (List.tl bvN) ((t, ienv), (t', qenv)) kf ks 
       else 
         kf (Fail ("mismatch: "^(indexElm2str (fun x -> x) h)^", "^
                              (indexElm2str (fun x -> x) h'))) |
    _ -> kf (Fail "find fail")
  ] in
  findAlt [0;0] [] (idx.val,(qry,[])) kf ks;
  (*** second 0 is for the body of the clause ***)


value findIdx idx c = 
  let rec go = fun [
    [] -> None |
    [Alt alts] -> goAlt alts |
    [App::idx] -> go idx |
    [h::t] -> if h = c then Some t else None
  ]
  and goAlt = fun [
    [h::t] -> match go h with [None -> goAlt t | x -> x] |
    [] -> None
  ] in
  match go idx with [None -> [] | Some x -> x];


value allMon idx = 
  let idx = findIdx [Alt idx.val] (Const' "{}" 0) in
  let mkTrm tm env =  ExpSub tm (env2sub 0 env) [] in
  let res = ref [] in
  nextTrm False (idx,[]) (fun _ -> res.val) (fun (hd,(idx,env)) kf ->
  match idx with [
    [Body :: x] -> nextTrm False (x,env) kf (fun (tm,(idx,env)) kf -> 
      match idx with [
        [Leaf lf] -> nextLeaf idx kf (fun v kf -> do {
          res.val := [(mkTrm hd env, mkTrm tm env, v)::res.val];
          kf (Fail "next")
        }) |
        _ -> raise (Failure "allMon 1")
      ]) |
    _ -> raise (Failure "allMon 2")
  ])
;


value subset a b = 
let rec go = fun [
  [] -> True |
  [h::t] -> if List.exists (tagEqCur h) b then go t else False
] in
go a;

value rec insert' reverse idx (tm, isUnr, ordered) = 
(** let _ = ps 0 ("inserting: "^(index2str 0 [tm])^" ordered:"^(sob ordered)^"\n") in **)
let inj x = Some x in
let bind a f = match a with [
  None -> None |
  Some x -> f x
] in
let changed = ref False in
let rec insAlt (alts,tm) = 
  let alts = if reverse then List.rev alts else alts in
match (alts,tm) with [
  ([],tm) -> None |
  ([alt::alts], tm) -> match ins False (alt,tm) with [
    None -> 
      if ordered then do {
        changed.val := True;
        inj (if reverse then [alt::alts]@[tm] else [tm;alt::alts])
      }
      else bind (insAlt (alts,tm)) (fun x -> inj [alt::x]) |
    Some x -> inj (if reverse then (alts@[x]) else [x::alts])
  ]
] 
and ins noFail = fun [
  ([Alt alts],tm) -> match insAlt (alts,tm) with [
    Some x -> inj [Alt x] |
    None -> do { changed.val := True; inj [Alt [tm::alts]] }
  ] |
  ([Body :: gls],[Body :: gl]) -> bind (ins True (gls,gl)) (fun x -> inj [Body::x]) |
  ([Leaf lf],[Leaf lf']) ->
    if subset lf' lf && not ordered && isUnr then inj [Leaf lf]
    else do { changed.val := True; inj [Leaf (lf' @ lf)] } |
  ([EVar' False nm rf lvl args::t1], tm2) when isInst rf.val ->
    let tm1 = flatterm (EVar nm rf lvl args, None) in
    bind (ins True (tm1 @ t1, tm2)) (fun x -> inj [EVar' True nm rf lvl args::x]) |
  ([(h1 as EVar' True _ _ _ _)::t1], t2) -> bind (ins noFail (t1,t2)) (fun x -> inj [h1::x]) |
  ([h::t],[h'::t']) -> 
    if idxEq (h, h') then bind (ins True (t,t')) (fun x -> inj [h::x]) 
    else if noFail then 
      let alts = if reverse then [[h::t];[h'::t']] else [[h'::t']; [h::t]] in
      do {changed.val := True; inj [Alt alts]} 
    else None |
  _ -> raise (Failure "insert")
] in do {
  idx.val := 
    match ins False ([Alt idx.val], tm) with 
      [Some [Alt x] -> x | _ -> raise (Failure "insert1")];
  changed.val
};

value insert idx x =  insert' False idx x;
value insertR idx x= insert' True idx x;


value rec remelm v = fun [
  [] -> [] |
  [h::t] -> if h = v then t else [h::remelm v t]
];

value rec diffset x = fun [
 [] -> x |
 [h::t] -> diffset (remelm h x) t
];

value remove idx tm = 
let rec remAlt = fun [
  ([alt::alts],tm) -> match rem [] (alt,tm) with [
    None -> match remAlt (alts,tm) with [
      None -> None | 
      Some (x,x') -> Some ([alt::x],x')
    ] |
    Some ([],x) -> Some (alts,x) |
    Some (alt',x) -> Some ([alt'::alts],x)
  ] |
  ([],tm) -> None
] 
and rem buf = fun [ 
  ([Leaf idxLf],[Leaf tmLf]) -> match diffset idxLf tmLf with [
    [] -> Some ([],buf@[Leaf tmLf]) |
    lf -> Some (buf@[Leaf lf],buf@[Leaf tmLf])
  ] |
  ([Leaf _::_],_) -> raise (Failure "rem: non-terminal Leaf") |
  ([Alt alts],tm) -> match remAlt (alts, tm) with [
    None -> None |
    Some ([],x') -> Some (buf,buf@x') |
    Some ([x],x') -> Some (buf@x,buf@x') |
    Some (x,x') -> Some (buf@[Alt x],buf@x')
  ] |
  ([(h1 as EVar' True _ rf1 _ _)::t1], [(h2 as EVar' True _ rf2 _ _)::t2])
  when rf1 == rf2 -> 
    rem (buf @ [h1]) (t1,t2) | 
  ([(h1 as EVar' True nm1 rf1 lvl1 args1)::t1], [(EVar' False _ rf2 _ args2)::t2])
  when rf1 == rf2 && sameArgs (args1, args2) ->
    let t1' = nextTrm False (t1,[]) 
      (fun msg -> raise (Failure ("remove nextTrm: "^(fail2str msg))))
      (fun (_,(t1',_)) kf -> t1')
    in
    rem (buf @ [EVar' False nm1 rf1 lvl1 args1]) (t1', t2) |
  ([(h1 as EVar' True _ _ _ _)::t1], t2) -> rem (buf@[h1]) (t1,t2) |
  ([h::t],[h'::t']) -> if idxEq' True (h, h') then rem (buf@[h]) (t,t') else None |
  _ -> None
] in
match remAlt (idx.val,tm) with [
  Some (idx',x) -> do { idx.val := idx'; Some x } |
  None -> do {
    ps 0 ("Couldn't remove: "); 
    showStr None None True False 0 [tm] tagTyp2str;
    ps 0 ((index2str 0 [tm])^"\n");
    ps 0 "From context:\n ";
    showStr None None True False 0 idx.val tagTyp2str;
    ps 0 "\n"; 
    ps 0 ((index2str 0 idx.val)^"\n");
    None 
  }
]; 


(********************************* Testing stuff *********************
value flat iQ t v = let (tm,_,_) = testb False t in flatterm' iQ ((tm,None),v);

value ins idx t v = 
  let (tm,_,_) = testb False t in 
  let changed = insert idx (List.hd (resid tm),v) in
  do { ps 0 ("changed: "^(string_of_bool changed)^"\n"); idx.val };

value rem idx t v = 
  let (tm,_,_) = testb False t in 
  let (hd,gl) = List.hd (resid tm) in
  do { ignore (remove idx ((hd,gl),v)); idx.val };

value fnd idx t = 
  let (qry,_,evars) = testb True t in 
  let subQ = makeSub (Id 0) False evars in
  find idx (ExpSub qry subQ []) (fun _ -> None) (fun (tm,v) kf -> 
  Some (term2str (ExpSub qry subQ []), qry, subQ, term2str tm, tm, v));

value optStr f = fun [None -> "None" | Some x -> "Some "^(f x)];
**************************************************************************)



