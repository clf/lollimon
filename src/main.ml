(*****
Title: main.ml

Description: Main file for LolliMon. Contains top-level interactive
  loop. This is written in OCaml using the revised syntax.

Author: Jeff Polakow

*****)

(*** flag to turn off type checking ***)
value useTypes = ref False;

(*** list of predicates whose clause order should be remembered ***)
value unOrderedPreds = ref [];
value fairPreds = ref [];



(*************************************** 
Backtrackable (OCaml) state change 
****************************************)

value write t v kf ks = let old = t.val in do {
  t.val := v;
  ks (fun msg -> do {t.val := old; kf msg})
};


(*************************************** 
Load up all "module" code
****************************************)

#use "misc.ml";

#use "tags.ml";

#use "terms.ml";

#use "newparser.ml";

#use "modes.ml";

#use "index.ml";

#use "tfplus.ml";

(*************************************** 
Main loop
****************************************)

value query (f,_,evars) linRefs affRefs auto = 
let s = ref (Val (List.length linRefs, newAvailVal())) in
let d = ref (Val (0, newAvailVal())) in 
let init s d = do {
  constraintId.val := 0; constraints.val := [];
  longestChain.val := 0;
  withTags.val := 0;
  availVal.val := 0;
  List.iter (fun r -> r.val := s ) linRefs;
  List.iter (fun n -> n.val := 1.0 ) affRefs
} in
let sub = makeSub evars None in
let solns = ref 0 in
let attempt = ref 1 in
let rec ks v kf = match auto with [
  None -> do {
    ps 0 "Success\n";
    if constraints.val = [] then () else ps 0 ("constraints: "^(constraints2str())^"\n");
(*
    if evars = [] then ps 0 "\n"
    else 
*)
    do {
      ps 0 ("with ["^(evarBind2str sub)^"]\n");
      ps 0 "More? ";
      if read_line() = "y" then kf (Fail "retry") else (ps 0 "\n")
    }  
  } |
  Some (expect,tries,maxAttempt) -> do {
    incr solns;
    ps 0 ("Attempt "^(soi attempt.val)^", Solution "^(soi solns.val)^
          " with ["^(evarBind2str sub)^"]\n");
    if solns.val > expect then do {
      ps 0 "Too many solutions.\n";
      kf (FFail (Fail "too many solutions"))
    }
    else if solns.val = tries then ps 0 "Success.\n"
    else kf (Fail "next solution")
  }
] in
let rec kf = fun [
  Fail s -> match auto with [
    None -> ps 0 ("Failure"^(if traceLevel.val > 1 then  "- "^s else "")^"\n\n") |
    Some (expect,tries,maxAttempt) ->
      if expect = solns.val then ps 0 "Success.\n" 
      else if attempt.val < maxAttempt then do {
        solns.val := 0; 
        incr attempt;
        let s = ref (Val (List.length linRefs, newAvailVal())) in
        let d = ref (Val (0, newAvailVal())) in 
        init s d;
        solve 0.0 1.0 2.0 3.0 s d (ExpSub f sub []) kf ks 
      }
      else do {
        ps 0 ("Failed to find "^(soi (min expect tries))^" solutions within "^
              (soi maxAttempt)^" attempts.\n");
        raise Stream.Failure
      }
  ] |
  FFail (Fail "too many solutions") -> match auto with [
    None -> raise (Failure "query got an FFail 1") |
    Some (expect,tries,maxAttempt) ->
      if attempt.val < maxAttempt then do {
        solns.val := 0; 
        incr attempt;
        let s = ref (Val (List.length linRefs, newAvailVal())) in
        let d = ref (Val (0, newAvailVal())) in 
        init s d;
        solve 0.0 1.0 2.0 3.0 s d (ExpSub f sub []) kf ks 
      }
      else do {
        ps 0 ("Failed to find "^(soi (min expect tries))^" solutions within "^
              (soi maxAttempt)^" attempts.\n");
        raise Stream.Failure
      }
  ] |
  FFail s -> raise (Failure "query got an FFail 2") |
  Problem s -> do {
    ps 0 ("Query aborted due to: "^s^"\n\n");
    raise Stream.Failure
  }
] in
let _ = init s d in
let q = ExpSub f sub [] in
let _ = match auto with [
  None -> () |
  Some (expect,tries,attempt) ->
    ps 0 ("Looking for "^(soi (min expect tries))^
          " solutions to query: "^(term2str q)^"\n") 
] in
solve 0.0 1.0 2.0 3.0 s d q kf ks 
;


exception BadFile;

value rec readFile file lin aff =
  let filePos = ref (0,0) in
  let posStr () = "\""^file^"\"(row "^(soi (fst filePos.val))^
                  ", col "^(soi (snd filePos.val))^")" 
  in
  let linRefs = ref [] in 
  let affRefs = ref [] in 
  let addedFrms = ref [] in
  let rec parseFileLine fstr = 
    let _ = match Stream.peek fstr with [None -> () | Some (_,p) -> filePos.val := p] in 
    match Stream.npeek 4 fstr with [
      [(Kwd "#linear",_)::_] -> 
        do { Stream.junk fstr; Some (Linear, Query (parseTrmLine False fstr)) } |
      [(Kwd "#affine",_)::_] -> 
        do { Stream.junk fstr; Some (Affine, Query (parseTrmLine False fstr)) } |

      [(Kwd "#query",_); (Ident expect,_); (Ident soln,_); (Ident tries,_)] -> do { 
        Stream.junk fstr; Stream.junk fstr; Stream.junk fstr; Stream.junk fstr;
        let q = parseTrmLine True fstr in
        if (ios soln > 0) then
          query q (linRefs.val@lin) (affRefs.val@aff) 
                (Some (ios expect,ios soln,ios tries))
        else ();
        parseFileLine fstr
      } | 

      [(Kwd "#mode",_); (Ident p,_)::_] -> do {
        Stream.junk fstr; Stream.junk fstr; 
        let modes = try parseModes p fstr with [Stream.Error _ -> raise (Stream.Error ("Bad mode declaration at "^(posStr())))] in
        allModes.val := [(p,modes)::allModes.val]; 
        parseFileLine fstr
      } |

      [(Kwd "#unordered",_); (Ident c,_); (Kwd ".",_)::_] -> do { 
        Stream.junk fstr; Stream.junk fstr; Stream.junk fstr; 
        unOrderedPreds.val := [c::unOrderedPreds.val];
        parseFileLine fstr
      } |
      [(Kwd "#fair",_); (Ident c,_); (Kwd ".",_)::_] -> do { 
        Stream.junk fstr; Stream.junk fstr; Stream.junk fstr; 
        fairPreds.val := [c::fairPreds.val];
        parseFileLine fstr
      } |
      [(Kwd "#load",_); (String file',_); (Kwd ".",_)::_] -> 
        let _ = do {
          fairPreds.val := []; unOrderedPreds.val := []; ctx.val := []; mysignature.val := []; allModes.val := []
        } in
        let thisdir = Sys.getcwd() in
        let _ = Sys.chdir (Filename.dirname file') in 
        let newfile = Filename.basename file' in
        let newdir = Sys.getcwd() in
        let _ = ps 0 ("[Loading file "^Filename.concat newdir newfile^"]\n") in
        let (lRefs', aRefs') = readFile newfile [] [] in 
        let _ = ps 0 ("[Closing file "^Filename.concat newdir newfile^"]\n\n") in
        let _ = Sys.chdir thisdir in
        do { 
	  Sys.chdir thisdir;
          Stream.junk fstr; Stream.junk fstr; Stream.junk fstr; 
          linRefs.val := lRefs';
          affRefs.val := aRefs';
          parseFileLine fstr
      } |
      [(Kwd "#include",_); (String file',_); (Kwd ".",_)::_] -> 
        let thisdir = Sys.getcwd() in
        let _ = Sys.chdir (Filename.dirname file') in 
        let newfile = Filename.basename file' in
        let newdir = Sys.getcwd() in
        let _ = ps 0 ("[Including file "^Filename.concat newdir newfile^"]\n") in
        let (lRefs', aRefs') = readFile newfile (linRefs.val@lin) (affRefs.val@aff) in 
        let _ = ps 0 ("[Closing file "^Filename.concat newdir newfile^"]\n\n") in
        let _ = Sys.chdir thisdir in
        do { 
          Stream.junk fstr; Stream.junk fstr; Stream.junk fstr; 
          linRefs.val := lRefs' @ linRefs.val;
          affRefs.val := aRefs' @ affRefs.val;
          parseFileLine fstr
      } |
      [_::_] -> Some (Unrestricted, parseInput file False fstr) |
      [] -> None
    ] 
  in
  let addIt tKnd tm evars = 
    let ins tg =
      let frms' = residuate' False (Some evars) tm tg in 
      let _ = List.iter (fun x -> ignore (insertR ctx x)) frms' in
      addedFrms.val := [frms'::addedFrms.val] 
    in
    match tKnd with [
      Linear -> 
        let newRef = ref (ref (Val (0, Avail 0))) in
        let _ = ins (Lin newRef) in
        linRefs.val := [newRef::linRefs.val] |
      Affine -> 
        let newRef = ref 1.0 in
        let _ = ins (Aff newRef) in
        affRefs.val := [newRef::affRefs.val] |
      Unrestricted ->  ins (newUnrVal ())
    ] 
  in
  let rec go fstr =
    match parseFileLine fstr with [
      None -> do { Stream.empty fstr } |
      Some x -> match x with [
        (isLin, Query (f,ty,evs)) -> do { addIt isLin f evs; go fstr } |
        (_, Decl c (ty,_,n)) ->
          let n' = if isPred ty then 0 else n in 
          do { mysignature.val := [(c,(ty,n'))::mysignature.val]; go fstr }
      ]
    ]
  in
  let fch = open_in file in
  let oldSig = mysignature.val in
  let rejectFile () = do {
    mysignature.val := oldSig; 
    let rem (x,_,_) = ignore (remove ctx x) in
    List.iter rem (List.flatten addedFrms.val);
    close_in fch; 
    raise BadFile
  } in
do {
  try do {
    go (lexer (Stream.of_channel fch));
    ps 0 (file^" is Ok.\n");
  } 
  with [
    Stream.Error e -> do {
      ps 0 (e^"\n\n"); 
      rejectFile()
    } |
    Stream.Failure -> do {
      ps 0 ("Bad File: "^(posStr())^"\n"); 
      rejectFile() 
    } |
    BadMode nm -> do {
      ps 0 ("Bad mode for "^nm^" at "^(posStr())^"\n");
      rejectFile()
    } |
    e -> do {close_in fch; raise e}
  ];
  close_in fch;
  (linRefs.val, affRefs.val)
};


value go useTypesFlag = 
let _ = unOrderedPreds.val := [] in
let _ = fairPreds.val := [] in
let _ = traceLevel.val := 0 in
let _ = useTypes.val := useTypesFlag in
let _ = ctx.val := [] in
let _ = mysignature.val := [] in
let _ = allModes.val := [] in
let rec go lin aff =
  let parseCmd = parser [
    [: `(Kwd "#quit",_) :] -> () |

    [: `(Kwd "#cd",_); `(String dir,_) :] -> 
      do {Sys.chdir dir; go lin aff} |

    [: `(Kwd "#pwd",_) :] -> 
      do {ps 0 ((Sys.getcwd ())^"\n"); go lin aff} |

    [: `(Kwd "#mode",_); `(Ident p,_); modes = parseModes p :] -> 
      do { allModes.val := [(p,modes)::allModes.val]; go lin aff } |

    [: `(Kwd "#unOrdered",_); `(Ident p,_) :] -> 
      do { unOrderedPreds.val := [p::unOrderedPreds.val]; go lin aff } |

    [: `(Kwd "#fair",_); `(Ident p,_) :] -> 
      do { fairPreds.val := [p::fairPreds.val]; go lin aff } |

    [: `(Kwd "#trace",_); `(Ident n,_) :] -> 
      do { traceLevel.val := (int_of_string n); go lin aff } |

    [: `(Kwd "#signature",_) :] -> do { 
        List.iter (fun x -> ps 0 ((decl2str x)^".\n")) (List.rev mysignature.val); 
        ps 0 "\n";
        go lin aff 
      } |
    [: `(Kwd "#allsig",_) :] -> do { 
        List.iter (fun x -> ps 0 ((decl2str x)^".\n")) 
                  (signature.val @ (List.rev mysignature.val)); 
        ps 0 "\n";
        go lin aff 
      } |

    [: `(Kwd "#contextl",_) :] -> 
      do { showStr None None True True 0 ctx.val tagTyp2str; ps 0 "\n"; go lin aff } |
    [: `(Kwd "#context",_) :] -> 
      do { showStr None None True False 0 ctx.val tagTyp2str; ps 0 "\n"; go lin aff } |

    [: `(Kwd "#clear",_) :] -> do { 
      fairPreds.val := []; unOrderedPreds.val := []; ctx.val := []; allModes.val := []; mysignature.val := []; go [] []
    } |
    [: `(Kwd "#clearctx",_) :] -> do { ctx.val := []; go [] []} |
    [: `(Kwd "#clearsig",_) :] -> do { mysignature.val := []; go lin aff} |

    [: `(Kwd "#include",_); `(String file,_) :] ->
      let thisdir = Sys.getcwd() in
      let _ = Sys.chdir (Filename.dirname file) in 
      let newfile = Filename.basename file in
      let newdir = Sys.getcwd() in
      let _ = ps 0 ("[Including file "^Filename.concat newdir newfile^"]\n") in
      let (lin',aff') = 
        try readFile newfile lin aff with [Sys_error s -> do{ ps 0 (s^"\n\n"); ([], [])}] in
      let _ = ps 0 ("[Closing file "^Filename.concat newdir newfile^"]\n\n") in
      let _ = Sys.chdir thisdir 
      in
      go (lin @ lin') (aff @ aff')
     |

    [: `(Kwd "#load",_); `(String file,_) :] -> do {
      fairPreds.val := []; unOrderedPreds.val := []; ctx.val := []; mysignature.val := []; allModes.val := [];
      let thisdir = Sys.getcwd() in
      let _ = Sys.chdir (Filename.dirname file) in 
      let newfile = Filename.basename file in
      let newdir = Sys.getcwd() in
      let _ = ps 0 ("[Loading file "^Filename.concat newdir newfile^"]\n") in
      let (lin',aff') = 
        try readFile newfile [] [] with [Sys_error s -> do{ ps 0 (s^"\n\n"); ([], [])}] in
      let _ = ps 0 ("[Closing file "^Filename.concat newdir newfile^"]\n\n") in
      let _ = Sys.chdir thisdir 
      in
      go lin' aff'
    } |

    [: `(Kwd "#assert",_); (f,ty,evars) = parseTrmLine False :] -> do {
      List.iter (fun x -> ignore (insert ctx x)) (residuate' False (Some evars) f (newUnrVal()));
      go lin aff
    } |

    [: `(Kwd "#linear",_); (f,ty,evars) = parseTrmLine False :] ->
      let sref = ref (ref (Val (0,Avail 1))) in
      do {
        List.iter (fun x -> ignore (insert ctx x)) (residuate' False (Some evars) f (Lin sref));
        go [sref::lin] aff
      } |

    [: `(Kwd "#affine",_); (f,ty,evars) = parseTrmLine False :] ->
      let rf = ref 1.0 in
      do {
        List.iter (fun x -> ignore (insert ctx x)) (residuate' False (Some evars) f (Aff rf));
        go lin [rf::aff]
      } |

    [: `(Kwd "#query",_); `(Ident expect,_); `(Ident tries,_); `(Ident attempt,_); 
       q = parseTrmLine True :] -> 
      do { query q lin aff (Some (ios expect,ios tries,ios attempt)); go lin aff } |

    [: inp = parseInput "" True :] -> match inp with [
      Query q -> do {query q lin aff None; go lin aff} |
      Decl c (ty,_,n) -> 
        let n' = if isPred ty then 0 else n in
        if useTypes.val then do { 
          mysignature.val := [(c,(ty,n'))::mysignature.val]; 
          go lin aff
        }
        else do { ps 0 "Ignoring declaration...\n"; go lin aff}
    ]
  ] in
  let _ = timeStamp.val := 0 in
  let _ = evarIDCounter.val := 0 in
  let _ = ps 0 ("LolliMon"^(if useTypes.val then "" else "_untyped")^"> ") in 
  let _ = flush stdout in
  try 
    parseCmd (lexer (Stream.of_channel stdin)) 
  with [ 
    Stream.Error e -> do { ps 0 (e^"\n\n"); go lin aff } |
    Failure "int_of_string" -> 
         do { ps 0 ("Did not find expected integer argument, " ^ 
                    "ignoring...\n\n");
              go lin aff } |
    Failure e -> raise (Failure e) |
    _ -> do { ps 0 ("Ignored previous...\n\n"); go lin aff }
  ]
in
go [] [];
