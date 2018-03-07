signature ABSYN =
  sig
    structure Terms : TERMS

    datatype parse_result =
        Parsed_Module of string * string list * string list 
			   * (string list * Terms.term) list
      | Parsed_Query of string list * Terms.term
      | Parsed_Term of string list * Terms.term

    type aterm
    type avarbind

    val close_module : string list * string list * aterm list 
			 -> string * string list * string list 
				   * (string list * Terms.term) list
    val close_term : aterm -> string list * Terms.term

    val mk_appl : aterm * aterm -> aterm
    val mk_zerop : string -> aterm
    val mk_unop : string * aterm -> aterm
    val mk_binop : string * aterm * aterm -> aterm
    val mk_ternop : string * aterm * aterm * aterm -> aterm

    val mk_varbind : string -> avarbind
    val mk_abst : avarbind * aterm -> aterm
    val mk_quant : string * aterm -> aterm
    val mk_int : int -> aterm
    val mk_string : string -> aterm
    val mk_lcid : string -> aterm
    val mk_ucid : string -> aterm

  end  (* signature ABSYN *)

