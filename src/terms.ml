(***
Title: terms.ml

Description: Implementation of lambda calculus with explicit
  substitutions and higer-order pattern unification. Also has the
  builtin signature for LolliMon.

Author: Jeff Polakow
***)

value debug = ref False;

type term = [
  Var of string and int and list term |
  EVar of string and ref evopt and int and list term |
  Const of string and int and list term |
  Lam of string and term and list term |
  ExpSub of term and sub and list term 
]
and evopt = [Inst of term | Open of list int]
and sub = [ Id of int | Sub of term and sub | Comp of sub and sub ];

value isInst = fun [
  Inst _ -> True |
  _ -> False
];

type failure = [
  Fail of string | 
  FFail of failure | (** for failing out of forward chaining **)
  Problem of string (** A problem occurred from which we fail gracefully **)
];
value rec fail2str = fun [
  Fail s -> "Fail: "^s |
  FFail f -> "FFail( "^(fail2str f)^" )" |
  Problem s -> "Problem: "^s
];

value ffail kf x = kf (FFail x);

value rec addArgs x a = match x with [
  Var nm vid args -> Var nm vid (args @ a) |
  EVar nm rf lvl args -> EVar nm rf lvl (args @ a) |
  Const c lvl args -> Const c lvl (args @ a) |
  Lam nm e args -> Lam nm e (args @ a) |
  ExpSub t s args -> ExpSub t s (args@a)
];

value rec exposeSub = fun [
  (sb1, Id 0) -> sb1 |
  (Id 0, sb2) -> sb2 |
  (Id n, Id n') -> Id (n+n') |
  (Id n, Sub _ sb2) -> exposeSub (Id (n-1), sb2) |
  (Id n, Comp sb1 sb2) -> exposeSub (Id n, exposeSub (sb1,sb2)) |
  (Sub t sb1, sb2) -> Sub (ExpSub t sb2 []) (Comp sb1 sb2) |
  (Comp sb1 sb2, sb3) -> exposeSub (sb1,(Comp sb2 sb3))
];

value rec lookupSub nm id = 
let rec go id = fun [
  Id n -> Var nm (id + n) [] |
  Sub t sub -> if id = 1 then t else go (id - 1) sub |
  Comp sb1 sb2 -> go id (exposeSub (sb1,sb2))
] in go id;

value subArgs sub args = List.map (fun x -> ExpSub x sub []) args;

value rec pushSub sub = fun [
  Var nm id args -> addArgs (lookupSub nm id sub) (subArgs sub args) |
  Lam nm e args -> 
    Lam nm (ExpSub e (Sub (Var nm 1 []) (Comp sub (Id 1))) []) (subArgs sub args) |
  EVar nm rf lvl args -> match rf.val with [
    Open _ -> EVar nm rf lvl (subArgs sub args) |
    Inst t -> addArgs (pushSub sub t) (subArgs sub args)
  ] |
  ExpSub t (Id 0) args -> addArgs (pushSub sub t) (subArgs sub args) |
  ExpSub t sub' args -> addArgs (pushSub (Comp sub' sub) t) (subArgs sub args) |
  Const nm lvl args -> Const nm lvl (subArgs sub args)
];

value rec expose = fun [
  Const nm lvl args -> Const nm lvl args |
  Var nm id args -> Var nm id args |
  (me as EVar nm rf -1 args) -> me | (*** This is a special EVar for mode-checking ***)
  EVar nm rf lvl args -> match rf.val with [
    Open _ -> EVar nm rf lvl args |
    Inst tm' -> expose (addArgs tm' args)
  ] |
  Lam nm t [] -> Lam nm t [] |
  Lam nm t [a::args] -> expose (ExpSub t (Sub a (Id 0)) args) |
  ExpSub (Lam nm t []) sub [a::args] -> expose (ExpSub t (Sub a sub) args) | 
  ExpSub t (Id 0) args -> expose (addArgs t args) |
  ExpSub t s args -> expose (addArgs (pushSub s t) args)
];


value rec normalize tm = match tm with [
  Const nm lvl args -> Const nm lvl (List.map normalize args) |
  Var nm id args -> Var nm id (List.map normalize args) |
  EVar nm rf lvl args -> match rf.val with [
    Open _ -> EVar nm rf lvl (List.map normalize args) |
    Inst tm' -> normalize (addArgs tm' args)
  ] |
  Lam nm t [] -> Lam nm (normalize t) [] |
  Lam nm t [a::args] -> normalize (ExpSub t (Sub a (Id 0)) args) |
  ExpSub (Lam nm t []) sub [a::args] -> normalize (ExpSub t (Sub a sub) args) | 
  ExpSub t s args -> normalize (addArgs (pushSub s t) args)
];


value close quant (t,ty,vars) = 
let rec go = fun [
  [] -> t |
  [v::vs] -> Const quant 0 [Lam v (go vs) []] 
] in
(go vars, ty, List.length vars);


value evarIDCounter = ref 0;
value newEVarNm nm = 
  let _ = incr evarIDCounter in
try 
  let undr = String.rindex nm '_' in
  let base = String.sub nm 0 undr in
(*
  let num = int_of_string (String.sub nm (undr + 1) ((String.length nm) - undr - 1)) in
*)
  base^"_"^(soi evarIDCounter.val)
with [_ -> nm^"_"^(soi evarIDCounter.val)];

type stampToggle = [FromEVar | FromVar];
value timeStamp = ref 0;
value readStamp = fun [
  FromEVar -> timeStamp.val |
  FromVar -> do {incr timeStamp; timeStamp.val}
];

value newParam nm = let n = readStamp FromVar in
  Const (nm^(string_of_int n)) n [];

value newEVar' prime nm nopt = 
  let n = match nopt with [None -> readStamp FromEVar | Some n -> n] in
  let nm' = if prime then (newEVarNm nm) else nm in
  let rf = ref (Open []) in
  (EVar nm' rf n [], (rf,nm'));

value newEVar prime nm nopt = fst (newEVar' prime nm nopt);


value makeSub evs lvl = 
let rec go = fun [
  [] -> Id 0 |
  [h::t] -> Sub (newEVar False h lvl) (go t)
] in go (List.rev evs);

(*************************************** 
Built-in terms (including formulas)
****************************************)

(*** 
infix binary operators recognized by parser 

True is right associative. False is left associative.
***)
value infixOps = [ 
  [("o-",False); ("@-",False); ("<=",False); (":-",False)]; (* lowest precedence *)
  [("-o",True); ("-@",True); ("=>",True)];
  [(";",True)];
  [(",",True); ("&",True)];
  [("=",True); ("is",True); (">",True)];
  [("+",True); ("-",True)];
  [("*",True)];
  [("::",True)];
  [(":",True)];
  [("->",True)]             (*  highest precedence, except built-in application *)
];

value infixTrms = [
  [("+",True);("-",True)];
  [("*",True)];
  [("::",True)]             
];

value rec findOp op = fun [
  [] -> None |
  [ops::rest] -> try
    let ass = List.assoc op ops in 
    Some ([ops::rest],ass,(List.length infixOps) - (List.length rest) - 1) 
    with [Not_found -> findOp op rest]
];


value kindC = Const "kind" 0 [];
value typeC = Const "type" 0 [];
value oC = Const "o" 0 [];
value intC = Const "int" 0 [];
value listC ty = Const "list" 0 [ty];
value arrowC ty1 ty2 = Const "->" 0 [ty1;ty2];

value (mysignature : ref (list (string * (term * int)))) = ref [];
value (signature : ref (list (string * (term * int)))) = ref [
  ("type", ( kindC, 0)); 
  ("o", ( typeC, 0));
  ("->", ( arrowC typeC (arrowC typeC typeC), 0));

  ("string", (typeC, 0));

  ("int", ( typeC, 0));
  ("+", ( arrowC intC (arrowC intC intC), 0));
  ("-", ( arrowC intC (arrowC intC intC), 0));
  ("*", ( arrowC intC (arrowC intC intC), 0));

  ("list", ( arrowC typeC typeC, 0));
  ("nil", ( Const "pi" 0 [Lam "T" (listC (Var "T" 1 [])) []], 1));
  ("::", ( Const "pi" 0 [Lam "T" (arrowC (Var "T" 1 []) (arrowC (listC (Var "T" 1 [])) (listC (Var "T" 1 [])))) []], 1));

  ("top", ( oC, 0));
  ("one", ( oC, 0));
  ("zero", ( oC, 0));

  ("once", ( arrowC oC oC, 0));
  ("!", ( arrowC oC oC, 0));
  ("@", ( arrowC oC oC, 0));
  ("{}", ( arrowC oC oC, 0));

  ("=>", ( arrowC oC (arrowC oC oC), 0));
  ("-@", ( arrowC oC (arrowC oC oC), 0));
  ("-o", ( arrowC oC (arrowC oC oC), 0));
  (",", (arrowC oC (arrowC oC oC), 0));
  ("&", ( arrowC oC (arrowC oC oC), 0));
  (";", ( arrowC oC (arrowC oC oC), 0));

  ("=", ( Const "pi" 0 [Lam "T" (arrowC (Var "T" 1 []) (arrowC (Var "T" 1 []) oC)) []], 0));

  ("is", ( arrowC intC (arrowC intC oC), 0));
  (">", (  arrowC intC (arrowC intC oC), 0));
(*** polymorphic versions-- remember to change tfplus.ml if turning these on ***
  ("is", ( Const "pi" 0 [Lam "T" (arrowC (Var "T" 1 []) (arrowC (Var "T" 1 []) oC)) []], 0));
  (">", ( Const "pi" 0 [Lam "T" (arrowC (Var "T" 1 []) (arrowC (Var "T" 1 []) oC)) []], 0));
***)

  ("write", ( Const "pi" 0 [Lam "T" (arrowC (Var "T" 1 []) oC) []], 0));
  ("write_lctx", ( oC, 0));
  ("write_ctx", ( oC, 0));
  ("write_pred", ( Const "pi" 0 [Lam "T" (arrowC (Var "T" 1 []) oC) []], 0));
  ("nl", ( oC, 0));

  ("pi", ( Const "pi" 0 [Lam "T" (arrowC (arrowC (Var "T" 1 []) oC) oC) []], 0));
  ("sigma", (Const "pi" 0 [Lam "T" (arrowC (arrowC (Var "T" 1 []) oC) oC) []], 0))
];

(*************************************** 
Term pretty printer
****************************************)

value list2strGen oneSep f join a = match a with [
  [] -> "" |
  [h::t] -> (if oneSep then join^(f h) else f h) ^
            (List.fold_left (fun s t -> s ^ join ^ (f t)) "" t)
];
value list2str f join a = list2strGen True f join a;

value rec nthTail n l = if n = 0 then l else nthTail (n-1) (List.tl l);

value term2str'' newNames exp tm =
  let maxPrec = 10000 in (** this number should be big enough **)
  let rec t2s bvars nest prec = 
    let opar op_prec = if nest || prec > op_prec then  "(" else "" in
    let cpar op_prec = if nest || prec > op_prec then  ")" else "" in
  fun [
    Var nm vid [] -> 
      let nm' = if newNames then List.nth bvars (vid - 1) else nm in
      nm'^(if exp then "<"^(soi vid)^">" else "") |
    Var nm vid args -> 
      let nm' = if newNames then List.nth bvars (vid - 1) else nm in
      (opar maxPrec) ^ nm'^(if exp then "<"^(soi vid)^">" else "") ^ " " ^
      (t2sLst bvars prec args) ^ (cpar maxPrec) |

    EVar nm rf lvl [] -> match rf.val with [ 
        Open cids -> nm^(if exp then "("^(list2str soi ", " cids)^")" else "") |
        Inst t -> t2s bvars nest prec t
    ] |
    EVar nm rf lvl args -> (opar maxPrec) ^ 
      (match rf.val with [ 
         Open cids -> 
           nm^(if exp then "("^(list2str soi ", " cids)^")" else "") ^ 
           " " ^(t2sLst bvars prec args) ^ (cpar maxPrec) | 
         Inst t -> t2s bvars nest prec (addArgs t args)
      ]) |

    Const "pi" _ [f] -> (opar 0) ^ "pi " ^ (t2s bvars False 0 f) ^ (cpar 0) |
    Const "sigma" _ [f] -> (opar 0) ^ "sigma " ^ (t2s bvars False 0 f) ^ (cpar 0) |

    Const "{}" _ [f] -> (opar maxPrec) ^ "{" ^ (t2s bvars False 0 f) ^ "}" ^ (cpar maxPrec) |

    Const c -1 [] -> if exp then "\""^c^"\"" else c | (*** -1 means string ***)
 
    Const c 0 args -> 
      let args' = 
        if useTypes.val then 
          let n = if exp then 0 else
            try snd (List.assoc c (mysignature.val @ signature.val)) 
                with [Not_found -> try let _ = int_of_string c in 0
                with [_ -> if c = "kind" then 0 
                           else raise (Failure ("term2str undefined constant: "^c))
                ]] 
          in
          nthTail n args 
        else args 
      in
      match (findOp c infixOps, args') with [
        (Some (ops, assoc, prec), [x; y]) -> 
          (opar prec) ^ (t2s bvars False (prec+1) x) ^ " "^c^" " ^ (t2s bvars False prec y) ^ (cpar prec) |
        _ -> 
          if args' = [] then c 
          else (opar maxPrec) ^ c ^ " " ^ (t2sLst bvars prec args') ^ (cpar maxPrec)
      ] |

    Const c _ [] -> "<<"^c^">>" | (** constant is a parameter, i.e. level > 0 **)
    Const c _ args -> (opar maxPrec) ^ "<<"^c^">>" ^ (t2sLst bvars prec args) ^ (cpar maxPrec) |

    Lam nm e [] -> 
      let (nm',bvars') = 
        if newNames then let nm'' = newEVarNm "x" in (nm'', [nm''::bvars]) 
        else (nm,bvars) 
      in
      (opar maxPrec) ^ (nm'^" \ ") ^ (t2s bvars' False 0 e) ^ (cpar maxPrec) |
    (rdx as Lam nm e args) -> 
      if not exp && not newNames then t2s bvars nest prec (expose rdx) else
      let (nm',bvars') = 
        if newNames then let nm'' = newEVarNm "x" in (nm'', [nm''::bvars]) 
        else (nm,bvars) 
      in
      (opar maxPrec) ^ "(" ^ nm' ^ " \ " ^ (t2s bvars' False 0 e) ^ ") " ^ 
      (t2sLst bvars' prec args) ^ (cpar maxPrec) |

    (t as ExpSub tm sub args) -> 
      if not exp then t2s bvars nest prec (expose t) else
       (opar maxPrec) ^ (t2s bvars True prec tm) ^ "[" ^ (sub2str bvars sub) ^ "]" ^ 
         (t2sLst bvars prec args) ^ (cpar maxPrec)
  ]
  and sub2str bvars = fun [
     Id n -> "Id "^(soi n) | 
     Sub t s -> (t2s bvars False 0 t)^" | " ^ (sub2str bvars s) | 
     Comp s1 s2 -> sub2str bvars (exposeSub (s1,s2))
  ]
  and t2sLst bvars prec = fun [
    [] -> "" |
    [h] -> t2s bvars True prec h |
    [h::t] -> 
      let tm = t2s bvars True prec h in 
      let tms = t2sLst bvars prec t in
      tm ^ " " ^ tms 
  ] in
t2s [] False 0 tm;

value term2str' = term2str'' False;
value term2str = term2str' False;

(*************************************** 
Printing final bindings for EVars
****************************************)

value rec evarBind2str = fun [
  Id 0 -> "" |
  Sub (EVar nm rf lvl []) sub -> match sub with [
    Id 0 -> match rf.val with [
      Inst t -> nm ^ " := " ^ (term2str (normalize t)) |
          _ -> nm
    ] |
    sub -> (match rf.val with [
       Inst t -> nm ^ " := " ^ (term2str (normalize t)) |
           _ -> nm
     ]) ^ ";  " ^ (evarBind2str sub) 
  ] |
  _ -> raise (Failure "evarBind2str")
]; 


(*************************************** 
Evaluation of integer terms
***************************************)
value eval t = 
let rec ev = fun [
  Const "+" 0 [a;b] -> ev a + ev b |
  Const "-" 0 [a;b] -> ev a - ev b |
  Const "*" 0 [a;b] -> ev a * ev b |
  Const n 0 [] -> int_of_string n |
  (t as ExpSub _ _ []) -> ev (expose t) |
  t -> raise (Failure "int_of_string")
] in
Const (soi (ev t)) 0 [] ;


(*************************************** 
Unification

  This is somewhat experimental and (at the moment) unstable.

  The goals of this code are: 
    1) correct unification results, 
    2) efficient algorithm (i.e. minimizing term traversals)
    3) maximizing code reuse

These goals are not all achieved, but it's a start.

****************************************)

value constraintId = ref 0;
value newConstraintId () = do {incr constraintId; constraintId.val};

value (constraints : ref (list (int * (term * term)))) = ref [];
value constraints2str () = 
  let rec go = fun [
    [] -> "" |
    [(_,(tm1,tm2))] -> (term2str tm1)^" = "^(term2str tm2) |
    [(_,(tm1,tm2))::cs] -> (term2str tm1)^" = "^(term2str tm2)^", "^(go cs)
  ] in
  go constraints.val;

value addConstraint tm1 tm2 rfs kf ks = 
  let cid = newConstraintId () in
  let rec go rfs kf ks = match rfs with [
    [] -> ks kf |
    [(rf,nm)::rfs] -> match rf.val with [
      Open cids -> let _ = ps 4 ("adding constr "^(soi cid)^" to "^nm^"\n") in 
                   write rf (Open [cid::cids]) kf (fun kf -> go rfs kf ks) |
      _ -> raise (Failure "addConstraint")
    ]
  ] in
  go rfs kf (fun kf ->
  let _ = ps 4 ("adding constraint "^(soi cid)^": "^
                (term2str' True  (normalize tm1))^" = "^(term2str' True (normalize tm2))^"\n") 
  in 
  write constraints [(cid, (tm1, tm2))::constraints.val] kf ks)
;

value remConstraint cid kf ks = 
  let newCs = remAssoc cid constraints.val in
  write constraints newCs kf ks;


value rec abstract body = fun [
  [] -> body |
  [Var nm _ []::args] -> Lam nm (abstract body args) [] |
  [Const nm _ []::args] -> Lam nm (abstract body args) [] |
  [(p1 as ExpSub _ _ _)::args] -> abstract body [expose p1::args] |
  _ -> raise (Failure "abstract")
]; 


(***
  checks arguments of EVars to make sure we only deal with patterns.
  creates a new EVar and constraint if necessary.
  ??? do we need to do some sort of occurs check specifically here ???
***)
value chkEVar ev kf ks = match ev with [
  EVar nm rf lvl args ->
    let rfs = ref [(rf,nm)] in
    let rec go args' addConstr = fun [
      [] -> 
        if addConstr then 
          let (ev',(rf',nm')) = newEVar' True nm (Some lvl) in
          addConstraint ev (addArgs ev' args') [(rf',nm')::rfs.val] kf (ks True nm' rf' args')
        else ks False nm rf args' kf |
      [x::args] -> match expose x with [
        (v as Var nm _ []) -> 
          if List.mem v args then go args' True args 
          else go [v::args'] addConstr args |
        (c as Const nm lvlc []) -> 
          if lvlc > lvl then
            if List.mem c args then go args' True args 
            else go [c::args'] addConstr args
          else go args' True args |
        EVar nm rf _ _ -> do { rfs.val := [(rf,nm)::rfs.val]; go args' True args } |
        _ -> go args' True args
      ]
    ] in
    go [] False args |
  _ -> raise (Failure "chkEVar")
];


value rec findArg targ args = 
let rec go n = fun [
  [] -> None |
  [(p as ExpSub _ _ _)::args] -> go n [expose p::args] |
  [Var nm id []::args] -> 
     match targ with [
       Var _ id' [] -> if id = id' then Some (n,nm) else go (n+1) args | 
       _ -> go (n+1) args
     ] |
  [Const c lvlc []::args] ->
     match targ with [
       Const nm lvl [] -> if c = nm then Some (n,nm) else go (n+1) args | 
       _ -> go (n+1) args
     ] |
  _ -> raise (Failure "findArg")
] in
go 1 args;

value flexflexEq nm rf lvl args1 args2 kf ks = 
let rec go usedArgs n = fun [
  ([],[]) -> ks (addArgs (newEVar True nm (Some lvl)) usedArgs) kf |
  ([p1::args1],[p2::args2]) -> match (expose p1,expose p2) with [
    (p1,p2) ->
      let newArgs = if p1 = p2 then [Var nm n []::usedArgs] else usedArgs in 
      go newArgs (n+1) (args1,args2)
  ] | 
  _ -> kf (Fail "flexflexEq 2")
] in
go [] 1 (args1, args2);

value flexflexNeq lvl1 args1 nm2 lvl2 args2 kf ks =
let rec go usedArgs1 usedArgs2 n2 = fun [
  [] -> let newEV = newEVar True nm2 (Some lvl2) in 
        ks (addArgs newEV usedArgs1,addArgs newEV usedArgs2) kf |
  [(p1 as ExpSub _ _ _)::args2'] -> go usedArgs1 usedArgs2 n2 [expose p1::args2'] |
  [(c as Const nm lvlc _)::args2'] -> 
    if lvlc > lvl1 then match findArg c args1 with [
      None -> go usedArgs1 usedArgs2 (n2+1) args2' |
      Some (n1,nm) -> go [Var nm n1 []::usedArgs1] [Var nm n2 []::usedArgs2] (n2 + 1) args2'
    ]
    else go [c::usedArgs1] [Var nm n2 []::usedArgs2] (n2 + 1) args2' |
  [(v as Var nm _ _)::args2'] -> match findArg v args1 with [
      None -> go usedArgs1 usedArgs2 (n2+1) args2' |
      Some (n1,nm) -> go [Var nm n1 []::usedArgs1] [Var nm n2 []::usedArgs2] (n2 + 1) args2'
  ] |
  _ -> raise (Failure "flexflexNeq")
] in
go [] [] 1 args2;

value rec raisedArgs lvl2 args1 = 
let rec go args2 = fun [
  [] -> args2 |
  [(c as Const _ lvlc _)::args] -> 
      if lvlc <= lvl2 then go [c::args2] args else go args2 args |
  [(v as Var _ _ _)::args] -> go args2 args |
  [(p as ExpSub _ _ _)::args] -> go args2 [expose p::args] |
  _ -> raise (Failure "raisedArgs")
] in 
go [] args1;

(***
  Term1 (left side) of unification pair is an EVar. Term 2 (right side) is arbitrary.

  readTerm traverses term 2, pruning and raising where necessary and returns to its
continuation a version of term 2 suitable for instantiating the body of term 1 with.

  The continuation of readTerm should abstract it's argument (i.e. the modified term 2) 
over the original paramenters for term 1.
***)
value rec readTerm sameOK nm1 rf1 lvl1 args1 tm kf ks = 
  let rec rA res args1 args2 kf ks = match args2 with [
    [] -> ks res kf |
    [a::args2] -> rT False args1 a kf (fun v kf1 -> rA (res@[v]) args1 args2 kf1 ks)
  ] 
  and rT sameOK args1 tm kf ks =
  match expose tm with [
    Const nm lvl2 args2 -> 
      if lvl2 > lvl1 then match findArg (Const nm lvl2 []) args1 with [
	None -> kf (Fail "readTerm Const") |
	Some (n,nm) -> rA [] args1 args2 kf (fun newArgs kf1 -> ks (Var nm n newArgs) kf1)
      ] 
      else rA [] args1 args2 kf (fun newArgs kf1 -> ks (Const nm lvl2 newArgs) kf1)  |

    Var nm id args2 -> match findArg (Var nm id []) args1 with [
      None -> kf (Fail "readTerm Var") |
      Some (n,nm) -> rA [] args1 args2 kf (fun newArgs kf1 -> ks (Var nm n newArgs) kf1)
    ] |

    Lam nm tm [] -> rT False [Var nm 1 []::subArgs (Id 1) args1] tm kf (fun v kf1 -> ks (Lam nm v []) kf1) |

    (ev2 as EVar nm2 rf2 lvl2 args2) -> 
      chkEVar ev2 kf (fun _ nm2 rf2 args2 kf -> 
        if rf1 == rf2 then 
          if sameOK then flexflexEq nm1 rf1 lvl1 args1 args2 kf ks
          else kf (Fail "readTerm occurs check")
        else 
        if lvl2 > lvl1 then (*** raise rf2 ***)
          let args = raisedArgs lvl2 args1 in
          let (newEV',(rf2',nm2')) = newEVar' True nm2 (Some lvl1) in
          let newEV = addArgs newEV' args in
          writeEV True nm2 rf2 newEV kf (fun kf -> 
          flexflexNeq lvl1 args1 nm2 lvl1 (List.append args2 (List.rev args)) kf (fun (ev1,ev2) kf ->
          writeEV True nm2' rf2' (abstract ev2 (List.append args args2)) kf (ks ev1)))
        else
          flexflexNeq lvl1 args1 nm2 lvl2 args2 kf (fun (ev1,ev2) kf ->
          writeEV True nm2 rf2 (abstract ev2 args2) kf (ks ev1))
      ) |

    _ -> raise (Failure ("readTerm: "^(term2str tm)))
  ] in
rT sameOK args1 tm kf ks

and unify (tm1, tm2) kf ks =
  let _ = ps 3 ("unify " ^ (term2str' True (normalize tm1)) ^ " and " ^ (term2str' True (normalize tm2)) ^ "\n") in
  let rec andall args kf ks = match args with [
    ([],[]) -> ks kf |
    ([a1::args1],[a2::args2]) -> 
      unify (a1, a2) kf (fun kf -> andall (args1,args2) kf ks) |
    _ -> kf (Fail "unify- unequal arg list to constants\n")
  ] in
  match (expose tm1, expose tm2) with [
    (Const c1 _ args1, Const c2 _ args2) -> 
      if c1 = c2 then andall (args1,args2) kf ks 
      else kf (Fail "unify- constant clash\n") |

    (Var _ id1 args1, Var _ id2 args2) ->
      if id1 = id2 then andall (args1,args2) kf ks
      else kf (Fail "unify- bound var clash\n") |

    (Lam _ e1 [], Lam _ e2 []) -> unify (e1, e2) kf ks |


    (***
      final write shouldn't wake up constraints?
    ***)
    ((t1 as EVar nm1 rf1 lvl1 args1), (t2 as EVar nm2 rf2 lvl2 args2)) -> 
      if lvl1 >= lvl2 then chkEVar t1 kf (fun isNewEV nm1 rf1 args1 kf -> 
        readTerm True nm1 rf1 lvl1 args1 t2 kf (fun v kf -> 
        writeEV isNewEV nm1 rf1 (abstract v args1) kf ks
        ))
      else chkEVar t2 kf (fun isNewEV nm2 rf2 args2 kf ->
        readTerm True nm2 rf2 lvl2 args2 t1 kf (fun v kf -> 
        writeEV isNewEV nm2 rf2 (abstract v args2) kf ks
        )) |

    ((t1 as EVar nm1 _ lvl1 _), t2) -> 
      chkEVar t1 kf (fun isNewEV nm1 rf1 args1 kf ->
      readTerm False nm1 rf1 lvl1 args1 t2 kf (fun v kf -> 
      writeEV isNewEV nm1 rf1 (abstract v args1) kf ks
      )) |

    (t2, (t1 as EVar nm1 _ lvl1 _)) -> 
      chkEVar t1 kf (fun isNewEV nm1 rf1 args1 kf ->
      readTerm False nm1 rf1 lvl1 args1 t2 kf (fun v kf -> 
      writeEV isNewEV nm1 rf1 (abstract v args1) kf ks
      )) |

    (t1,t2) -> do {
        kf (Fail "unify- main\n")
      }
  ]

and wake cids kf ks = match cids with [
  [] -> let _ = ps 4 "nothing more to wake\n" in ks kf |
  [cid::cids] -> 
    try 
      let x = List.assoc cid constraints.val in
      let _ = ps 4 ("waking up constraint "^(soi cid)^"\n") in
      unify x (*(List.assoc cid constraints.val) *)
        (fun msg -> let _ = ps 4 ("Constraint "^(soi cid)^" failed.\n") in kf msg) 
        (fun kf -> 
          let _ = ps 4 ("Constraint "^(soi cid)^" succeeded.\n") in
          remConstraint cid kf (fun kf ->
          wake cids kf ks
        ))
    with [Not_found -> wake cids kf ks] 
]

and writeEV isNewEV nm rf v kf ks = 
let _ = ps 4 ("writing EVar "^nm^" "^(term2str' True (normalize v))^"\n") in
let cids = match rf.val with [Open x -> x | _ -> raise (Failure "writeEV")] in 
let propagate cs e kf ks = 
  let rec propArgs args kf ks = match args with [
    [] -> ks kf |
    [a::args] -> prop a kf (fun kf -> propArgs args kf ks)
  ] and
  prop e kf ks = match e with [
    EVar nm rf lvl args -> match rf.val with [
      Open cs' -> write rf (Open (cs' @ cids)) kf (fun kf -> propArgs args kf ks) |
      Inst e' -> propArgs args kf (fun kf -> prop e' kf ks)
    ] |
    Const nm lvl args -> propArgs args kf ks |
    Var nm id args -> propArgs args kf ks |
    Lam nm e args -> propArgs args kf (fun kf -> prop e kf ks) |
    (e as ExpSub _ _ _) -> prop (expose e) kf ks
  ] in
  prop e kf ks
in
let ks' = if isNewEV then ks else (fun kf -> wake cids kf ks) in
propagate cids v kf (fun kf ->
write rf (Inst v) kf ks')
;

