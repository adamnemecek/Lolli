(* Uses the generated lexer and parser to export parsing functions *)

signature PARSE =
sig

structure Absyn : ABSYN

exception Parse_EOF
exception Parse_Error of string

val module_parse : string -> 
			(string * string list * string list 
				* (string list * Absyn.Terms.term) list)
val query_parse : string -> (string list * Absyn.Terms.term)
val term_parse :  string -> (string list * Absyn.Terms.term)
val file_parse : string -> 
			(string * string list * string list 
				* (string list * Absyn.Terms.term) list)
val stream_query_parse : instream -> (string list * Absyn.Terms.term)
val stream_term_parse : instream -> (string list * Absyn.Terms.term)

end  (* signature PARSE *)


functor Parse (structure Absyn : ABSYN
	       structure Interface : INTERFACE
	       structure Parser : PARSER
	          sharing type Parser.arg = Interface.arg
	          sharing type Parser.pos = Interface.pos
		  sharing type Parser.result = Absyn.parse_result
	       structure Tokens : Fol_TOKENS
	          sharing type Tokens.token = Parser.Token.token
		  sharing type Tokens.svalue = Parser.svalue) : PARSE =
struct

structure Absyn = Absyn

exception Parse_EOF
exception Parse_Error of string

val EOF_token = Tokens.EOF(!Interface.line,!Interface.line)

fun make_stream init_token (reader : int -> string) =
    let val stream = Parser.makeLexer reader
	val _ = Interface.init_line ()
	val (next_token,_) = Parser.Stream.get(stream)
     in if Parser.sameToken(next_token,EOF_token)
	   then raise Parse_EOF
	   else Parser.Stream.cons(init_token(!Interface.line,!Interface.line),
  		     		   stream)
    end

fun module_stream (reader) = make_stream Tokens.PARSEMODULE reader
fun query_stream (reader) = make_stream Tokens.PARSEQUERY reader
fun term_stream (reader) = make_stream Tokens.PARSETERM reader


fun string_reader string =
 let val already = ref false
  in (fn (n:int) => if (!already) then "" else ( already := true ; string ))
 end

fun parse (look_ahead,stream) =
  Parser.parse(look_ahead, stream, Interface.error, Interface.nothing)
  handle Parser.ParseError => raise Parse_Error("Fatal parsing error")

fun extract_module (Absyn.Parsed_Module(module),_) = module
  | extract_module _ = raise Parse_Error("Internal parsing problem")

fun extract_query (Absyn.Parsed_Query(query),_) = query
  | extract_query _ = raise Parse_Error("Internal parsing problem")

fun extract_term (Absyn.Parsed_Term(term),_) = term
  | extract_term _ = raise Parse_Error("Internal parsing problem")

fun module_parse s =
		 extract_module (parse(30, module_stream (string_reader s)))
fun query_parse s = extract_query (parse(30, query_stream (string_reader s)))
fun term_parse s = extract_term (parse(30, term_stream (string_reader s)))


fun file_parse s =
  let val dev = open_in s
      val m_stream = module_stream (fn i => input_line dev)
   in extract_module(parse(30, m_stream)) end

fun stream_query_parse input_stream =
  let val q_stream = query_stream (fn i => input_line input_stream)
   in extract_query(parse(0, q_stream)) end

fun stream_term_parse input_stream =
  let val t_stream = term_stream (fn i => input_line input_stream)
   in extract_term(parse(0, t_stream)) end

end  (* functor Parse *)
