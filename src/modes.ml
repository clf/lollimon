type mode = [Unknown | Input | Output];

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
      [: `(Kwd "-",_); res = go typ :] -> [Output::res] |
      [: `(Kwd "*",_); res = go typ :] -> [Unknown::res] |
      [: :] -> myfail ()
    ] |
    _ -> myfail()
  ] in try
  go (fst (List.assoc p mysignature.val))
  with [e -> myfail()]
;

