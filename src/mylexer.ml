(***********************************************************************)
(*                                                                     *)
(*                           Objective Caml                            *)
(*                                                                     *)
(*              Xavier Leroy, projet Cristal, INRIA Rocquencourt       *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../LICENSE.     *)
(*                                                                     *)
(***********************************************************************)

(****
 significantly modified by Jeff Polakow and Pablo Lopez in September 2004 
****)

type token = [
  Kwd of string | 
  Ident of string | 
  String of string
];

(* The string buffering machinery *)

value initial_buffer = String.create 32;

value buffer = ref "" (*initial_buffer*);
value bufpos = ref 0;

value reset_buffer () = bufpos.val := 0; 
(*do { buffer.val := initial_buffer; bufpos.val := 0 };*)

value store c = do {
  if bufpos.val >= String.length buffer.val then
    let newbuffer = String.create (2 * bufpos.val) in 
    do {
      String.blit buffer.val 0 newbuffer 0 bufpos.val; 
      buffer.val := newbuffer
    }
  else ();
  String.set buffer.val bufpos.val c;
  incr bufpos
};

value get_string () =
  let s = String.sub buffer.val 0 bufpos.val in 
(*  let _ = buffer.val := initial_buffer in *)
  do { reset_buffer(); s}
;

(* The lexer *)

exception BadChar of string;

value make_lexer keyId keywords input =
  let row = ref 1 in 
  let col = ref 0 in
  let chkNl c = if c = '\010' then do { incr row; col.val := 0 } else () in

  let err e = raise (Stream.Error (e^" at row "^(soi row.val)^" col "^(soi col.val))) in
  let fail () = do {
    ps 0 ("Lexer failed at row "^(soi row.val)^" col "^(soi col.val)^"\n"); 
    raise Stream.Failure
  } in

  let kwd_table = Hashtbl.create 17 in
  let _ = List.iter (fun s -> Hashtbl.add kwd_table s (Kwd s)) keywords in

  let ident_or_keyword id =
    try Hashtbl.find kwd_table id with [ Not_found -> 
      if List.mem id keyId then Kwd id else Ident id 
    ]
  in
  let keyword_or_error c =
    let s = String.make 1 c in
    try Hashtbl.find kwd_table s with [
      Not_found -> err ("Illegal character " ^ s)
    ]
  in

  let myjunk strm = do {incr col; Stream.junk strm} in

  let rec next_token (strm__ : Stream.t _) =
    match Stream.peek strm__ with [
      Some (c as ' ' | '\010' | '\013' | '\009' | '\026' | '\012') ->
        do { myjunk strm__; chkNl c; next_token strm__ }
    | Some '"' -> 
        let _ = myjunk strm__ in
        let s = strm__ in 
        do { reset_buffer (); Some (String (string s),(row.val,col.val)) }
    | Some '(' -> 
        do { myjunk strm__; maybe_comment strm__ }
    | Some '#' -> 
        do { myjunk strm__; reset_buffer(); store '#'; Some (ident strm__,(row.val,col.val))}
    | Some c ->
        let _ = do { myjunk strm__; reset_buffer(); store c } in
        match Stream.peek strm__ with [
          Some c1 -> do {
            store c1;
            if c = '-' && '0' <= c1 && c1 <= '9' then 
              do { myjunk strm__; Some (ident strm__, (row.val,col.val)) }
            else
            try 
              let res = Some (Hashtbl.find kwd_table (get_string()),(row.val,col.val)) in
              do { myjunk strm__; res }
            with [
              Not_found -> do {
                reset_buffer(); 
                store c;
                try 
                  Some (Hashtbl.find kwd_table (get_string()),(row.val,col.val))
                with [
                  Not_found -> match c with [
                      ('A'..'Z' | 'a'..'z' | '_' | '0'..'9' | '\'' | '^') -> 
                        do { reset_buffer(); store c; Some (ident strm__,(row.val,col.val)) }
                    | _ -> err ("Illegal character "^(String.make 1 c))
                  ]
                ]
              }
            ]
          } |
          None -> do {
            try Some (Hashtbl.find kwd_table (get_string()),(row.val,col.val)) with [
             Not_found -> match c with [
                 ('A'..'Z' | 'a'..'z' | '_' | '0'..'9' | '\'') -> 
                    do { reset_buffer (); store c; Some (ident strm__,(row.val,col.val)) }
               | _ -> err ("Illegal character "^(String.make 1 c))
            ]]
          }
      ]
    | _ -> None
  ]

  and ident (strm__ : Stream.t _) =
    match Stream.peek strm__ with [
      Some (c as 'A'..'Z' | 'a'..'z' | '_' | '0'..'9' | '\'') -> 
        do { myjunk strm__; store c; ident strm__ }
    | _ -> (ident_or_keyword (get_string ()))
  ]

  and string (strm__ : Stream.t _) =
    match Stream.peek strm__ with [
      Some '"' -> do { myjunk strm__; get_string () }
    | Some '\\' ->
        let _ = myjunk strm__ in
        let c = try escape strm__ 
                with [ Stream.Failure -> err "lexing error" ]
        in
        let s = strm__ in 
        do { store c; string s }
    | Some c -> 
         let _ = myjunk strm__ in
         let s = strm__ in 
         do { chkNl c; store c; string s }
    | _ -> fail()
  ]

  and escape (strm__ : Stream.t _) =
    match Stream.peek strm__ with [
      Some 'n' -> do { myjunk strm__; '\n' }
    | Some 'r' -> do { myjunk strm__; '\r' }
    | Some 't' -> do { myjunk strm__; '\t' }
    | Some ('0'..'9' as c1) -> do {
        myjunk strm__;
        match Stream.peek strm__ with [
          Some ('0'..'9' as c2) -> do {
            myjunk strm__;
            match Stream.peek strm__ with [
              Some ('0'..'9' as c3) -> do {
                myjunk strm__;
                Char.chr
                  ((Char.code c1 - 48) * 100 + (Char.code c2 - 48) * 10 +
                     (Char.code c3 - 48))
              }
            | _ -> err "lexing error"
            ]
          }
        | _ -> err "lexing error"
        ]
      }
    | Some c -> do { myjunk strm__; c }
    | _ -> fail()
  ]

  and maybe_comment (strm__ : Stream.t _) =
    match Stream.peek strm__ with [
      Some '*' ->
        let _ = myjunk strm__ in
        let s = strm__ in 
        do { comment s; next_token s }
    | _ -> Some (keyword_or_error '(',(row.val,col.val))
    ]

  and comment (strm__ : Stream.t _) =
    match Stream.peek strm__ with [
      Some '(' -> do { myjunk strm__; maybe_nested_comment strm__ }
    | Some '*' -> do { myjunk strm__; maybe_end_comment strm__ }
    | Some c -> do { myjunk strm__; chkNl c; comment strm__ }
    | _ -> fail ()
    ]

  and maybe_nested_comment (strm__ : Stream.t _) =
    match Stream.peek strm__ with [
      Some '*' -> 
        let _ = myjunk strm__ in 
        let s = strm__ in 
        do { comment s; comment s }
    | Some c -> do { myjunk strm__; chkNl c; comment strm__ }
    | _ -> fail()
    ]

  and maybe_end_comment (strm__ : Stream.t _) =
    match Stream.peek strm__ with [
      Some ')' -> do { myjunk strm__; () }
    | Some '*' -> do { myjunk strm__; maybe_end_comment strm__ }
    | Some c -> do { myjunk strm__; chkNl c; comment strm__ }
    | _ -> fail()
    ]
  in

  Stream.from (fun count -> do { buffer.val := initial_buffer; next_token input })
;
