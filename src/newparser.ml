(***
Title: newparser.ml

Description: Parser and and type-checker for LolliMon

Author: Jeff Polakow
***)

(*** 
Lexer
***)
#use "mylexer.ml";

(***
 "is" should be lexed as an identifier, but marked as a Kwd (because it's infix)
***)
value lexer = make_lexer ["is"] [
"#quit"; "#cd"; "#pwd"; 
"#trace"; 
"#ordered"; "#fair"; "#mode";
"#query"; 
"#context"; "#clearctx"; "#contextl";
"#allsig"; "#signature"; "#clearsig"; 
"#include"; "#clear"; "#load";
"#affine"; "#linear"; "#assert";
".";
"("; ")"; 
"->"; ":"; 
"\\"; 
"{"; "}"; 
"-o"; "o-"; ":-"; 
"::"; "+"; "-"; "*";
"=>"; "<="; 
"-@"; "@-"; 
","; 
"&"; 
";"; 
"!"; "@";
">"; "="
(***** 
these will just be regular constants as far as parsing is concerned 

"is";
"pi"; "sigma";
"write"; "nl"; 
"one"; "top"; "zero";
"once"
*****)
];


(***
Parsing
***)
value curFile = ref "";

value tyerr (row,col) s = raise (Stream.Error ("Type error \""^curFile.val^"\"(row "^(soi row)^", col "^(soi col)^"): "^s));
value tyerrClash pos ty1 ty2 = tyerr pos ("expected "^(term2str ty1)^", found "^(term2str ty2));

value newTVar = fun [
  None ->  newEVar True "Tv" (Some 0) |
  Some nm -> newEVar False nm (Some 0)
];

value rec eqTyp tm1 tm2 = 
  (* let _ = ps 0 ("eqType: "^(term2str tm1)^" and "^(term2str tm2)^"\n") in *)
  not useTypes.val || unify (tm1,tm2) (fun _ -> False) (fun _ -> True);

value rec isTyp ty = match (expose ty) with [
  Const "kind" 0 [] -> True |
  Const "type" 0 [] -> True |
  _ -> False
];

value rec isPred ty = match (expose ty) with [
  Const "o" 0 [] -> True |
  Const "->" 0 [_;ty] -> isPred ty |
  Const "pi" 0 [Lam "T" ty []] -> isPred ty |
  _ -> False
];

value decl2str (c,(ty,n)) = 
let rec inst ty = match expose ty with [
  Const "pi" 0 [ty] -> match expose ty with [
      (ty as Lam nm _ _) -> inst (addArgs ty [newTVar (Some nm)]) |
      x -> raise (Failure ("decl2str "^(term2str x)))
    ] |
  ty -> ty
] in
c^" : "^(term2str (inst ty))(*^" <"^(soi n)^">"*);


value isUpper x = 'A' <= x && x <= 'Z';

type parseState = {valIdx : mutable list (string * term); valEvr : mutable list string};
value parseVars = {valIdx = []; valEvr = []};

value makeVar vn =
  let vid = (List.length parseVars.valIdx) + 1 in 
  let tv = newTVar None in
  do {
    parseVars.valIdx := parseVars.valIdx @ [(vn,tv)];
    parseVars.valEvr := [vn::parseVars.valEvr];
    (Var vn vid [], tv)
  };

value bindTVars tm = 
let rec go tvs = fun [
  EVar nm rf lvl args -> 
    let (v,tvs) = 
      try (List.assoc rf tvs, tvs) 
      with [Not_found -> let v = fst (makeVar nm) in (v,[(rf,v)::tvs])] 
    in
    addArgs v (List.map (go tvs) args) |
  Var nm lvl args -> Var nm lvl (List.map (go tvs) args) |
  Const nm lvl args -> Const nm lvl (List.map (go tvs) args) |
  Lam nm t [] -> Lam nm (go tvs t) [] |
  _ -> raise (Failure "bindTVars")
] in
go [] (normalize tm);

value parseTrmLine' isDecl isGoal strm = 
  let _ = do {
    parseVars.valIdx := []; parseVars.valEvr := []; 
    constraints.val := []; constraintId.val := 0
  } in

  let getTyp c = 
    let rec go tvars = fun [
      (Const "pi" 0 [t]) -> 
        let tv = newTVar None in 
        go (tvars@[tv]) (expose (addArgs t [tv])) |
      (t as Const _ _ _) -> (normalize t, tvars) |
      t -> raise (Failure ("bad type decl-- "^c^" : "^(term2str' True t)))
    ] in
    if not useTypes.val then (typeC,[]) else
    go [] (fst (List.assoc c (mysignature.val @ signature.val)))
  in

  let lookup v = 
    let rec go n = fun [
      [] -> None |
      [(h,ty)::t] -> if h = v then Some (n,ty) else go (n+1) t
    ] in
    go 1 
  in

  let findId pos vn = match lookup vn parseVars.valIdx with [
    None -> 
      if isUpper vn.[0] then let (v,ty) = makeVar vn in (v, ty, pos)
      else try 
        let (ty,tvars) = getTyp vn in 
        let tArgs = if isPred ty then [] else tvars in 
        (Const vn 0 tArgs, ty, pos)
        with [Not_found -> try let _ = int_of_string vn in (Const vn 0 [], intC, pos)
        with [_ -> tyerr pos (vn^" is not declared.")
        ]]
    |
    Some (vid,ty) -> (Var vn vid [], ty, pos)
  ] in

  (***
    check types of arguments to a binary function (i.e. infix operator)
  ***)
  let checkTy2 posop op (x,tyx,posx) (y,tyy,posy) = 
  if not useTypes.val then (Const op 0 [x;y], typeC, posop) else
  (*** BEGIN HACK: allows user defined type constructors by overloading '->' ***)
  if op = "->" &&  tyx = kindC then
    if eqTyp tyy kindC then (Const op 0 [x;y], kindC, posop)
    else tyerrClash posy kindC tyy
  (*** END OF HACK ***)
  else
  try match getTyp op with [
    (Const "->" 0 [ty1; Const "->" 0 [ty2; ty3]], tvars) -> 
      if eqTyp tyx ty1 then 
        if eqTyp tyy ty2 then 
          let tArgs = if isPred ty3 then [] else tvars in
          (Const op 0 (tArgs@[x;y]), ty3, posop)
        else tyerrClash posy ty2 tyy 
      else tyerrClash posx ty1 tyx |
    (ty,tvars) -> tyerr posop ("infix operator "^op^" declared with type "^(term2str ty))
  ] with [
    Not_found -> tyerr posop (op ^ " not declared")
  ] in

  (***
    check type of argument to a function
  ***)
  let checkTy1 posop op (x,tyx,posx) = 
  if not useTypes.val then (Const op 0 [x], typeC, posop) else
  try match getTyp op with [
    (Const "->" 0 [ty1; ty2], tvars) ->
      if eqTyp tyx ty1 then 
        let tArgs = if isPred ty2 then [] else tvars in
        (Const op 0 (tArgs@[x]), ty2, posop) 
      else tyerrClash posx ty1 tyx |
    (ty,tvars) -> tyerr posop ("operator "^op^" declared with type "^(term2str ty))
  ] with [
    Not_found -> tyerr posop (op ^ " not declared")
  ] in

  let rec parseTerm = fun [
    [] -> parser [ [: s = parseSimple; t = parseArgs [] s :] -> t] |
    [ops::ops'] -> parser [ [: s = parseTerm ops'; t = parseArgs [ops::ops'] s :] -> t ]
  ]
  and parseRight x op pos ops = parser [
    [: y = parseTerm ops :] -> checkTy2 pos op x y |
    [: :] -> tyerr pos (op^" has a missing or bad argument")
  ]
  and parseLeft x op pos ops = parser [
    [: y = parseTerm (List.tl ops); 
       z = let (x',y',op') = match op with [
             (":-" | "o-") -> (y,x,"-o") |
             "<=" -> (y,x,"=>") |
             "@-" -> (y,x,"-@") |
             op -> (x,y,op)
           ] in 
           parseArgs ops (checkTy2 pos op' x' y') 
    :] -> z |
    [: :] -> tyerr pos (op^" missing argument")
  ]
  and parseArgs ops (x as (tmx,tyx,posx)) = parser [
    [: `(Kwd op,pos) when findOp op ops != None; 
       y = match findOp op ops with [
	 None -> raise (Failure ("bad operator "^op)) |
	 Some (ops,assoc,prec) ->
           if assoc then parseRight x op pos ops else parseLeft x op pos ops
       ]
    :] -> y |
    [: (args,ty) = parseAppArgs tyx posx :] -> (addArgs tmx args, ty, posx) |
    [: :] -> x
  ]
  and parseAppArgs ty pos = parser [
    [: (tmx,tyx,posx) = parseSimple; (args, ty') =
       let ty1 = newTVar None in
       let ty2 = newTVar None in
       if eqTyp ty (Const "->" 0 [ty1;ty2]) then 
         if eqTyp tyx ty1 then parseAppArgs ty2 pos else tyerrClash posx ty1 tyx
       else tyerrClash pos (Const "->" 0 [ty1;ty2]) ty
    :] -> ([tmx::args],ty') |
    [: :] -> ([],ty)
  ]
  and parseSimple = parser [
    [: `(Ident v,posv); x = parser [ 
	[: `(Kwd "\\",_); (tm,ty,pos) = do {
	      parseVars.valIdx := [(v,newTVar None)::parseVars.valIdx];
	      parseTerm infixOps
            }
	:] -> let vty = match lookup v parseVars.valIdx with
                [ Some (_,ty) -> ty | None -> raise (Failure "parseSimple") ]
              in
              let _ = parseVars.valIdx := List.tl parseVars.valIdx in
              (Lam v tm [], Const "->" 0 [vty; ty], posv) |
	[: :] -> findId posv v
      ]
    :] -> x |
    [: `(String s,pos) :] -> (Const s (-1) [], Const "string" 0 [], pos) |
    [: `(Kwd "(",_); (tm,ty,pos) = parseTerm infixOps; `(Kwd ")",_) :] -> (tm,ty,pos) |
    [: `(Kwd "{",pos); t = parseTerm infixOps; `(Kwd "}",_) :] -> checkTy1 pos "{}" t |
    [: `(Kwd "@",pos); t = parseTerm infixTrms :] -> checkTy1 pos "@" t |
    [: `(Kwd "!",pos); t = parseTerm infixTrms :] -> checkTy1 pos "!" t
  ]
  in

  try
  parser [ [: (tm,ty,pos) = parseTerm infixOps; `(Kwd ".",_) :] ->
    if constraints.val = [] then
    if not useTypes.val || (isDecl && isTyp ty) || (not isDecl && (expose ty) = oC) then 
      (***
        we're not using types, or 
        we have a declaration of a valid type, or 
        we have a query of type 'o'.
      ***)
      let tm = if isGoal then tm else bindTVars tm in
      (tm, ty, parseVars.valEvr)  
    else if isDecl then tyerr pos "Bad type." else tyerrClash pos oC ty
    else tyerr pos "Unresolved constraints."
  ] strm
  with [Stream.Error "" -> raise (Stream.Error (curFile.val^" missing final '.'"))]
;

value parseTrmLine = parseTrmLine' False;

value testb isGoal s = parseTrmLine isGoal (lexer (Stream.of_string s));
value test isGoal s = close "pi" (testb isGoal s);

type inputTyp = [ Decl of string and (term * term * int) | Query of (term * term * list string)];

value parseInput file isGoal strm = 
let _ = curFile.val := file in
match Stream.npeek 2 strm with [
  [ (Ident c,_); (Kwd ":",_) ] -> do { 
    Stream.junk strm; Stream.junk strm; 
    Decl c (close "pi" (parseTrmLine' True False strm))
  } |
  _ -> Query (parseTrmLine isGoal strm)
];

value testi isGoal s = parseInput "" isGoal (lexer (Stream.of_string s));




