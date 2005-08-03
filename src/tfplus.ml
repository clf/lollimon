(***
Title: tfplus.ml

Description: Implementation of operational semantics of LolliMon
  proof search using tag-frame fast (TF\) resource management
  system. TF\ system uses the memory location interpretation of
  tags and treats the context as a piece of state to be modified as
  proof search proceeds.


Author: Jeff Polakow
***)

(*************************************** 
Residuate program clause into logically compiled form 
****************************************)
value noResid = ["one";"zero";","; ";"; "sigma"; "!"; "@"; ">"; "=";
"is"];

value residuate' forwardChain chkModeOpt dc tag = 
  let newEVs = ref [] in
  (***
    resid returns a list of ((head,body),isOrdered). A list is necessary
  due to &. EVars are just open bound variables. This is inherited from
  input argument.
  ***)
  let rec resid dc =
  let _ = ps 3 ("Residuating: "^(term2str' True dc)^"\n") in
  match expose dc with [
    Const "-o" 0 [gl; dc] -> 
      let f = fun [
        ((hd, Const "one" 0 []),ordered) -> ((hd, gl),ordered) |
        ((hd, gl'),ordered) -> ((hd, Const "," 0 [gl'; gl]),ordered)
      ] in
      List.map f (resid dc) |

    Const "=>" 0 [gl; dc] -> 
      let f = fun [
        ((hd, Const "one" 0 []),ordered) -> ((hd, Const "!" 0 [gl]),ordered) |
        ((hd, gl'),ordered) -> ((hd, Const "," 0 [gl'; Const "!" 0 [gl]]),ordered)
      ] in
      List.map f (resid dc) |

    Const "-@" 0 [gl; dc] -> 
      let f = fun [
        ((hd, Const "one" 0 []),ordered) -> ((hd, Const "@" 0 [gl]),ordered) |
        ((hd, gl'),ordered) -> ((hd, Const "," 0 [gl'; Const "@" 0 [gl]]),ordered)
      ] in
      List.map f (resid dc) |

    Const "&" 0 [dc1; dc2] -> List.append (resid dc1) (resid dc2) |

    Const "pi" 0 [dc'] -> match expose dc' with [
      Lam nm dc [] -> do {newEVs.val := newEVs.val @ [nm] ; resid dc} |
      _ -> raise (Failure "resid bad pi")
    ] |

    (a as Const c 0 args) when not (List.mem c noResid) -> 
      [((a, Const "one" 0 []), not (c = "{}" || forwardChain || List.mem c unOrderedPreds.val))] |
(*
      [((a, Const "one" 0 []), not (c = "{}" || forwardChain))] |
*)
(*
      [((a, Const "one" 0 []),List.mem c orderedPreds.val && not (c = "{}"))] |
*)

    f -> raise (Failure "resid") 
  ] in
  let dc' = resid dc in
do {
  match chkModeOpt with [
    None -> () |
    Some evars -> List.iter (fun ((hd,bdy),_) -> checkMode hd bdy (evars @ newEVs.val)) dc'
  ];
  List.map (fun ((hd,bdy),ord) -> (flatterm (hd,Some (bdy,tag)), isUnr tag, ord)) dc'
};
value residuate = residuate' False None;
value residuateF = residuate' True None;

(*************************************** 
Formula Context
****************************************)

value ctx = ref ([] : list (list (indexElm tagTyp)));

value showLin user n = do {
  showStr None user True (if n < 4 then True else False) n ctx.val tagTyp2str;
  ps n "\n"
};

value pushCtx dcs kf ks = 
  let rec go res = fun [
    [] -> res |
    [h::t] -> 
      let changed = insert ctx h in
      go (if changed then [h::res] else res) t
  ] in
  let pushed = go [] dcs in
  ks (pushed != []) (fun msg -> do { 
    List.iter (fun (x,_,_) -> ignore (remove ctx x)) pushed; 
    kf msg 
  })
;

value popCtx dcs kf ks =
  let rec go res = fun [
    [] -> res |
    [(h as (tm,_,_))::t] -> 
      let res' = match remove ctx tm with [Some _ -> [h::res] | None -> res] in
      go res' t
  ] in
  let popped = go [] dcs in
  ks (fun msg -> do { 
    List.iter (fun x -> ignore (insert ctx x)) popped; 
    kf msg 
  })
;


(*************************************** 
TF\ derivation rules

  Note that the formula context is just sitting in the global
reference, ctx, and isn't explicitly passed around.
****************************************)

type breakTagTyp = [Unrestricted | Affine | Linear];

value rec solve al ar dl dr s d gl kf ks = 
let kf msg = do { ps 4 ("Failed goal: "^(term2str' True gl)^"\n"); kf msg} in
let _ = ps 4 ("\nSolving goal: "^(term2str' True gl)^"\n") in
let _ = ps 5 ("s="^(tag2str s.val)^" d="^(tag2str d.val)^
              "   al="^(sof al)^" ar="^(sof ar)^"\n") in
let _ = showLin None 4 in
match gl with [
  Var _ _ _ -> raise (Failure "bound variable goal") | 
  EVar _ _ _ _ -> kf (Problem "variable goal") |
  Lam _  _ [] -> kf (Problem "lambda as goal") |

  Lam _ _ _ -> solve al ar dl dr s d (expose gl) kf ks |
  ExpSub _ _ _ -> solve al ar dl dr s d (expose gl) kf ks |

  gl -> 
  let _ = 
    if traceLevel.val > 3 then () 
    else do {
      ps 1 ("\nSolving goal: "^(term2str' True (normalize gl))^"\n");
      ps 2 ("s="^(tag2str s.val)^" d="^(tag2str d.val)^
            "   al="^(sof al)^" ar="^(sof ar)^"\n");
      showLin None 2
   }
  in
  let kf = 
    if traceLevel.val > 3 then kf 
    else
    (fun msg -> do {
      ps 1 ("Failed goal: "^(term2str' True (normalize gl))^"\n"); 
      kf msg
    })
  in
  match gl with [

  Const "top" 0 [] -> alias s d kf (ks True) |

  Const "one" 0 [] -> 
    if (fst (getval s) = 0) then ks False kf 
    else kf (Fail "unused strict resources\n") |

  Const "zero" 0 [] -> kf (Fail "zero\n") |

  Const "pi" 0 [gl'] -> match expose gl' with [
    (gl'' as Lam nm _ _) -> solve al ar dl dr s d (addArgs gl'' [newParam nm]) kf ks |
    _ -> kf (Problem ("Bad pi: "^(term2str gl)))
  ] |

  Const "sigma" 0 [gl'] -> match expose gl' with [
    (gl'' as Lam nm _ _) -> solve al ar dl dr s d (addArgs gl'' [newEVar True nm None]) kf ks |
    _ -> kf (Problem ("Bad sigma: "^(term2str gl)))
  ] |

  Const ";" 0 [gl1; gl2] -> 
    solve al ar dl dr s d gl1 (fun [Fail _ -> solve al ar dl dr s d gl2 kf ks | x -> kf x]) ks |

  Const "!" 0 [gl] -> 
    if (fst (getval s) = 0) then 
      let l = ref (Val (0,newAvailVal())) in
      let delta = ar +. (dl -. ar) /. 2.0 in
      solve ar delta dl dr l d gl kf (fun _ kf1 -> ks False kf1) 
    else kf (Fail "bang with unused strict resources\n") |

  Const "@" 0 [gl] -> 
    if (fst (getval s) = 0) then 
      let l = ref (Val (0,newAvailVal())) in
      solve al ar dl dr l d gl kf (fun _ kf1 -> ks False kf1) 
    else kf (Fail "affine with unused strict resources\n") |

  Const "=>" 0 [dc; gl] -> try
    let dc' = residuate dc (newUnrVal()) in
    pushCtx dc' kf (fun changed kf -> 
    solve al ar dl dr s d gl kf (fun v kf -> 
    if changed then popCtx dc' kf (ks v) else ks v kf)) 
  with [Failure "resid" -> kf (Problem ("Unrestricted assumed formula: "^(term2str dc)))] |

  Const "-@" 0 [dc; gl] -> try
    let newRef = ref ar in
    let dc' = residuate dc (Aff newRef) in
    pushCtx dc' kf (fun changed kf -> 
    solve al ar dl dr s d gl kf (fun v kf -> 
    popCtx dc' kf (ks v))) 
  with [Failure "resid" -> kf (Problem ("Affine assumed formula: "^(term2str dc)))] |

  Const "-o" 0 [dc; gl] -> try
    let newRef = ref s in
    let dc' = residuate dc (Lin newRef) in
    pushCtx dc' kf (fun changed kf ->
    update (fun x -> x + 1) s kf (fun kf -> 
    solve al ar dl dr s d gl kf (fun v kf -> 
    popCtx dc' kf (fun kf ->
    update (fun x -> x - 1) d kf (ks v)
    ))))
  with [Failure "resid" -> kf (Problem ("Linear assumed formula: "^(term2str dc)))] |

  Const "," 0 [g1; g2] -> 
    let l = ref (Val (0,snd (getval s))) in
    let delta = dl +. (dr -. dl) /. 2.0 in
    solve al ar delta dr l d g1 kf (fun v kf ->
      if v then
        write l (Val (0,snd (getval s))) kf (fun kf ->
        solve al ar dl delta l d g2 kf (fun _ kf -> 
        alias s d kf (ks True) 
        ))
      else solve al ar dl delta s d g2 kf ks
    ) |

  Const "&" 0 [g1; g2] ->
    let l = ref (Val (0, newAvailVal())) in
    let _ = incr withTags in
    let old_avl = snd (getval s) in
    let delta = dl +. (dr -. dl) /. 2.0 in
    let epsilon = delta +. (dr -. delta) /. 2.0 in
    solve al ar dl delta s l g1 kf (fun v kf -> 
      if v then 
        write l (Val (fst (getval l), old_avl)) kf (fun kf -> 
        solve al delta epsilon dr l d g2 kf ks)
      else solve al delta epsilon dr l d g2 kf (fun _ kf -> ks False kf)
    )
  |

  Const "is" 0 [a; b] -> try
    if (fst (getval s) = 0) then unify (a, eval b) kf (ks False) 
    else kf (Fail "Eval unused strict resources\n")
  with [ Failure "int_of_string" -> 
    kf (Problem ("Non-integer 'is' argument: "^(term2str a)))
  ] |

  Const ">" 0 [a; b] -> 
    if (fst (getval s) = 0) then 
      match (expose a, expose b) with [
        (Const n1 0 [], Const n2 0 []) -> 
          try 
            if (int_of_string n1) > (int_of_string n2) then ks False kf
            else kf (Fail "Gt")
          with [Failure "int_of_string" -> kf (Problem "Non-integer > argument")] |
        _ -> kf (Problem "Non-integer > argument")
      ]
    else kf (Fail "Gt unused strict resources\n") |

  Const "=" 0 [a; b] -> 
    if (fst (getval s) = 0) then unify (a, b) kf (fun kf1 -> ks False kf1) 
    else kf (Fail "Eq unused strict resources\n") |

  Const "nl" 0 [] -> 
    if (fst (getval s) = 0) then do {ps 0 "\n"; ks False kf}
    else kf (Fail "Nl unused strict resources\n") |

  Const "write" 0 [a] -> 
    if fst (getval s) = 0 then do {
      ps 0 (term2str a); ks False kf
    } 
    else kf (Fail "Write unused strict resources\n") |

  Const "write_lctx" 0 [] -> 
    if fst (getval s) = 0 then do {
      ps 0 ("Linear context is:\n");
      showLin (Some (snd (getval s),al,ar)) 0; 
      ks False kf
    } 
    else kf (Fail "Write_lctx unused strict resources\n") |

  Const "write_ctx" 0 [] -> 
    if fst (getval s) = 0 then do {
      ps 0 ("Context is:\n");
      showStr None (Some (snd (getval s),al,ar)) True False 0 ctx.val tagTyp2str; 
      ks False kf
    } 
    else kf (Fail "Write_ctx unused strict resources\n") |

  Const "write_pred" 0 [arg] -> 
    let p = match expose arg with [
      Const c _ _ -> c | _ -> raise (Failure ("write_pred "^(term2str arg)))
    ] in  
    if fst (getval s) = 0 then do {
      ps 0 ("Clauses of "^p^":\n");
      showStr (Some p) (Some (snd (getval s),al,ar)) True False 0 ctx.val tagTyp2str; 
      ks False kf
    } 
    else kf (Fail "Write_ctx unused strict resources\n") |

  Const "once" 0 [gl'] -> 
    solve al ar dl dr s d gl' 
      (fun [FFail x -> kf x | x -> kf x]) 
      (fun v kf -> ks v (ffail kf)) |


  (*********** begin code for monadic goal ***********)
  (targ as Const "{}" 0 [goal]) -> 
    let aliases = ref [] in
    (***
      Need to remove any added assumptions upon solving monadic goal.
    ***)
    let rec popCtx' d hds kf ks = match hds with [
      [] -> ks kf |
      [(frmKnd,hd)::hds'] -> 
(*
let f (x,_,_) = ps 0 ("removing "^(sob (frmKnd = Linear))^" "^(idx2str 0 x)^"\n") in
let _ = List.iter f hd in
let _ = ps 0 "--\n" in
*)
        popCtx hd kf (fun kf -> 
          if frmKnd = Linear then 
            update (fun x -> x - 1) d kf (fun kf -> popCtx' d hds' kf ks)
          else
            popCtx' d hds' kf ks)
    ] in
    (***
      Originally, in the older version, tag modifications during forward
    chaining were redundantly backtracked. This version attempts to not do 
    that in the code commented as risky.

      Context additions are handled the same as in the older version. I
    think there is redundant backtracking here as well, however it's not
    as clear as for tag modifications since the new pieces of context must
    be removed after the monadic goal succeeds.
    ***)
    let rec forward al ar dl dr s d goal again addedFrms clauses banned kf ks = 
    match clauses with [
      [] -> 
        if again then 
          forward al ar dl dr s d goal False addedFrms (permute (allMon ctx)) banned kf ks
        else 
(*
let _ = ps 0 ("solving monadic goal: "^(term2str goal)^"\n") in
*)
          solve al ar dl dr s d goal (ffail kf) (ks addedFrms) |

      [(a',gl',tKnd)::cls] -> 
        let delta = dl +. (dr -. dl) /. 2.0 in
        let newTag = ref (Val (0,snd (getval s))) in
        let dOld = fst (getval d) in
        let kf' x = 
(*
let _ = ps 0 ("forward failed with: "^(fail2str x)^"\n") in
*)
          match x with [
          Fail x -> forward al ar dl dr s d goal again addedFrms cls banned kf ks |
          x -> kf x
          ] 
        in
        let ks' clsTyp v kf =
          let unrId = match tKnd with [Unr n -> Some n | _ -> None] in
          let linDel = dOld != fst (getval d) in
          if v then
            write newTag (Val (0,snd (getval s))) kf (fun kf ->
            breakdown al ar dl delta newTag d a' again linDel clsTyp goal addedFrms cls unrId banned kf 
              (fun addFrms _ kf -> alias s d kf (ks addFrms True)))
          else breakdown al ar dl delta s d a' again linDel clsTyp goal addedFrms cls unrId banned kf ks
        in
        match tKnd with [
          Unr n -> 
(*
let _ = ps 0 ("trying to apply monadic clause: "^(term2str gl')^" -o "^(term2str a')^"\n") in
*)
            if not (List.mem n banned) then
              solve al ar delta dr newTag d gl' kf' (ks' Unrestricted) 
            else
              forward al ar dl dr s d goal again addedFrms cls banned kf ks |
          Aff n -> 
            if al < n.val && n.val <= ar then
              let nOld = n.val in
              let _ = n.val := dr in (** this is risky, but I think ok **)
              solve al ar delta dr newTag d gl' 
                (fun msg -> do {n.val := nOld; kf' msg})
                (ks' Affine)
            else 
              forward al ar dl dr s d goal again addedFrms cls banned kf ks |
          Lin tRef ->
            let (l,new_aliases) = tagLookup tRef.val in
            let _ = aliases.val := new_aliases @ aliases.val in
            if snd (getval l) = snd (getval s) then
              let changes trV d l = do {
                tRef.val := trV;
                update' (fun x -> x + 1) d;
                update' (fun x -> x - 1) l
              } in
              let tRefOld = tRef.val in (** ditto **)
              let dOld = d.val in
              let lOld = l.val in
              let _ = changes d d l in
              solve al ar delta dr newTag d gl' 
                (fun msg -> do {changes tRefOld l d; kf' msg})
                (ks' Linear)
            else
              forward al ar dl dr s d goal again addedFrms cls banned kf ks
        ]
    ]
    and breakdown al ar dl dr s d frm again linDel clsTyp goal addFrms0 cls unrId banned kf ks = 
      let _ = ps 1 ("Breaking down: "^(term2str' True frm)^"\n") in
      let banIt = ref False in
      let isDisjunct = ref False in
      let rec bd al ar dl dr s d tagTyp frm addedFrms changed kf ks = 
      match frm with [
       [] -> 
(*
let _ = ps 0 ("breakdown empty, changed="^(sob changed)^", addedFrms=[]:"^(sob (addedFrms=[]))^" banIt.val="^(sob banIt.val)^" linDel="^(sob linDel)^" isDisjunct.val="^(sob isDisjunct.val)^"\n") in
*)
         if not (isDisjunct.val || linDel || changed) && clsTyp = Unrestricted then 
           kf (Fail "Try Again") 
         else 
           let again' = changed || again || linDel in
           let newBanned = match unrId with [
             None -> banned |
             Some n -> if not linDel && banIt.val then [n::banned] else banned
           ] in
           forward al ar dl dr s d goal again' (addedFrms) cls newBanned kf ks |
       [Var _ _ _::_] -> raise (Failure "bound variable monadic conclusion") | 
       [Lam _  _ []::_] -> kf (Problem "lambda as monadic conclusion") |
       [(frm as Lam _ _ _)::rest] -> 
         bd al ar dl dr s d tagTyp [(expose frm)::rest] addedFrms changed kf ks |
       [(frm as ExpSub _ _ _)::rest] -> 
         bd al ar dl dr s d tagTyp [(expose frm)::rest] addedFrms changed kf ks |
       [(ev as EVar _ rf _ _)::rest] -> match rf.val with [
         Open _ -> kf (Problem "variable monadic conclusion") |
         Inst frm -> bd al ar dl dr s d tagTyp [(expose ev)::rest] addedFrms changed kf ks
       ] |
       [Const "," 0 [frm1;frm2]::rest] -> 
         if not (tagTyp = Linear) then 
           kf (Problem "tried to assume tensor underneath modality") 
         else
           bd al ar dl dr s d tagTyp [frm1::[frm2::rest]] addedFrms changed kf ks |
       [Const "one" 0 []::rest] -> bd al ar dl dr s d tagTyp rest addedFrms changed kf ks |

       [Const "zero" 0 []::rest] -> 
          (*** 
            Monadic goal is solved, so resume backtracking.
          ***)
          ks (addedFrms) True (ffail kf) |

       [Const "sigma" 0 [frm']::rest] -> 
          match expose frm' with [
            (frm'' as Lam nm _ _) -> 
              bd al ar dl dr s d tagTyp 
                [(addArgs frm'' [newParam nm])::rest] addedFrms changed kf ks |
            _ -> kf (Problem "bad sigma")
          ] |
       [Const "!" 0 [frm]::rest] -> 
         bd al ar dl dr s d Unrestricted [frm::rest] addedFrms changed kf ks |
       [Const "@" 0 [frm]::rest] -> 
         bd al ar dl dr s d Affine [frm::rest] addedFrms changed kf ks |

       [(c as Const ";" 0 [frm1;frm2])::rest] -> 
          let _ = do{ isDisjunct.val := True; banIt.val := True } in
          let l = ref (Val (0, newAvailVal())) in
          let _ = incr withTags in
          let oldAvl = snd (getval s) in
          let delta = dl +. (dr -. dl) /. 2.0 in
          let epsilon = delta +. (dr -. delta) /. 2.0 in
          (***
            Set addedFrms to [] in first branch to ensure that all the 
          current added formulas stick around for second branch.
          ***)
          bd al ar dl delta s l tagTyp [frm1::rest] [] changed kf (fun aFs v kf ->
(*
let _ = ps 0 "second branch of ;\n" in
*)
            let kf' = fun [FFail x -> kf x | x -> kf x] in
          if v then 
            write l (Val (fst (getval l), oldAvl)) kf' (fun kf -> 
            popCtx' l aFs kf (fun kf ->
            bd al delta epsilon dr l d tagTyp [frm2::rest] addedFrms changed kf ks))
          else 
            popCtx' l aFs kf' (fun kf ->
            bd al delta epsilon dr l d tagTyp [frm2::rest] addedFrms changed kf
               (fun aFs _ -> ks aFs False))) |

        [frm::rest] -> try
          let _ = banIt.val := match tagTyp with [Unrestricted -> banIt.val && True | _ -> False] in
          let frmTag = match tagTyp with [
            Unrestricted -> newUnrVal() |
            Affine -> Aff (ref ar) |
            Linear -> Lin (ref s)
          ] in
          let frm' = residuateF frm frmTag in
          let _ = ps 3 ("monadic add: "^(term2str' True frm)^"\n") in
          pushCtx frm' kf (fun changed' kf -> 
(*
let f (x,_,_) = ps 0 ("adding "^(idx2str 0 x)^"\n") in
let _ = if changed' then List.iter f frm' else () in
*)
            let addedFrms' = 
              if changed' then [(tagTyp, frm')::addedFrms] else addedFrms 
            in
            if tagTyp = Linear then 
              update (fun x -> x + 1) s kf (fun kf ->
              bd al ar dl dr s d Linear rest addedFrms' (changed || changed') kf ks)
            else
              bd al ar dl dr s d Linear rest addedFrms' (changed || changed') kf ks
          )
        with [
          Failure "resid" -> 
            kf (Problem ("Assumed monadic formula: "^(term2str frm)))
        ] 
      ] in
      bd al ar dl dr s d Linear [frm] addFrms0 False kf ks
    in
    forward al ar dl dr s d goal False [] (permute (allMon ctx)) []
      (fun msg -> do {
        (***
          Monadic goal failed. Change FFail to allow normal backtracking.
        ***)
	undoTagLookup aliases.val; 
	kf (match msg with [FFail x -> x | x -> x])
      }) 
      (fun addFrm v kf -> 
        (*** 
          Monadic goal succeeded. Get rid of local hypotheses. 
        ***)
        popCtx' d addFrm kf (ks v)
      ) |
  (*********** end of code for monadic goal ***********)

  (targ as Const nm _ _) ->
let myN = 1 in 
let _ = ps myN ("solving atom: "^(term2str targ)^"\n") in
    (****
      I'm not sure tag lookup is really undone correctly...
    ***)
    let aliases = ref [] in
    let kf' msg = do { undoTagLookup aliases.val; ps myN (fail2str msg); ps myN ("\nback to solving atom: "^(term2str targ)^"\n"); kf msg } in
    let fair = (List.mem nm fairPreds.val) in
    find fair ctx targ kf' (fun (gl', tKnd) kf ->
      let _ = ps myN (
        " trying clause "^(term2str' True targ)^":- "^(term2str' True gl')^
        (if traceLevel.val > 3 then " with tag="^(tagTyp2str tKnd) else "")^"\n") 
      in
    match tKnd with [
      Unr n -> solve al ar dl dr s d gl' kf ks |
      Aff n ->
        if al < n.val && n.val <= ar then
          write n dr kf (fun kf ->
          solve al ar dl dr s d gl' kf ks)
        else kf (Fail "unavailable affine choice\n") |
      Lin tRef -> 
        let (l,new_aliases) = tagLookup tRef.val in
        let () = aliases.val := new_aliases @ aliases.val in
        if snd (getval l) = snd (getval s) then
          write tRef d kf (fun kf ->
          update (fun x -> x + 1) d kf (fun kf ->
          update (fun x -> x - 1) l kf (fun kf ->
          solve al ar dl dr s d gl' kf ks
          )))
        else kf (Fail "unavailable linear choice\n")
    ]) |

_ -> raise (Failure "solve")
]
];
