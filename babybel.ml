open Ast_mapper
open Asttypes
open Parsetree

exception Scanning_error of Lexing.position * string
exception Syntax_error of Lexing.position

let file_name = "unknown"

let sigma : Sf.signature ref = ref []

(* Parsing *)

let parser menhir_parser lexbuf =
  let position = ref (Sflexer.initial_pos file_name) in
  let lexer () =
    let ante_position = !position in
    let post_position, token = Sflexer.main_scanner !position lexbuf in
    let () = position := post_position in (* Lexing.({!position with pos_lnum = !position.pos_lnum + nlines;}) in *)
    (token, ante_position, post_position) in
  let revised_parser = MenhirLib.Convert.Simplified.traditional2revised menhir_parser
  in try
       revised_parser lexer
    with
      | Sflexer.Error x -> raise (Scanning_error (!position, x))
      | Sfparser.Error  -> raise (Syntax_error !position)

let parse p s =
  let lexbuf = Ulexing.from_utf8_string s in
  parser p lexbuf

(* Session management *)

let session_file_name = "session.bb"

let save_session (s : Sf.signature) : unit =
  let f = open_out_bin session_file_name in
  Marshal.to_channel f !sigma [] ;
  close_out_noerr f

let load_session unit : unit =
  try
    let f = open_in_bin session_file_name in
    sigma := Marshal.from_channel f ;
    (* print_string "Session file loaded\n" ; *)
    close_in_noerr f
  with _ -> print_string "No session loaded\n" ; ()

(* The rewriter *)

let babybel_mapper (argv : string list) : Ast_mapper.mapper =
  { default_mapper with
    expr = (fun mapper expr ->
  	    match expr with
  	    | { pexp_desc = Pexp_constant (Const_string (s, Some "def")) } ->
	       let sigma' = parse Sfparser.decls s in
	       sigma := sigma' @ !sigma ;
	       save_session !sigma ;
	       Astgen.decls_to_ast sigma'
  	    | { pexp_desc = Pexp_constant (Const_string (s, Some "term")) } ->
	       load_session() ;
	       let m = Index.index !sigma [] (parse Sfparser.term_expr s) in
	       Astgen.nor_to_ast m
  	    | other -> default_mapper.expr mapper other)
  ; pat = (fun mapper pat ->
	   match pat with
	   | { ppat_desc = Ppat_constant (Const_string (s, Some "p"))} ->
	      load_session () ;
	      let m = Index.index !sigma [] (parse Sfparser.term_expr s) in
	      Astgen.nor_to_pat_ast m
	   | other -> default_mapper.pat mapper other)
  }

let () = register "babybel_mapper" babybel_mapper
