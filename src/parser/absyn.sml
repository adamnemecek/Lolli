functor Absyn (structure Terms : TERMS) : ABSYN =
struct

structure Terms = Terms
open Terms

datatype parse_result =
    Parsed_Module of string * string list * string list 
 			    * (string list * Terms.term) list
  | Parsed_Query of string list * term
  | Parsed_Term of string list * term

type aterm = string list -> string list -> string list * term
type avarbind = string list -> string list -> string list * varbind


fun close_module (modname::params,locals,ats) =
	  (modname,params,locals, map (fn at => at (locals @ params) nil) ats)

fun close_term at = at nil nil

fun mk_appl (at1,at2) = fn bvars => fn freevars =>
        let val (fvs1,t1) = at1 bvars freevars
            val (fvs2,t2) = at2 bvars fvs1
	 in (fvs2, Terms.Appl(t1,t2)) end

fun mk_lcid (vname) =
      fn bvars => fn freevars =>
         (freevars,if (exists (fn bv => vname = bv) bvars)
		      then Bvar(vname)
		      else Const(Name vname))

fun mk_ucid (vname) =
      fn bvars => fn freevars =>
         (if (exists (fn bv => vname = bv) bvars)
			       orelse (exists (fn fv => vname = fv) freevars)
			      then freevars
			      else vname::freevars ,
	  Bvar(vname))

fun mk_zerop ope            = mk_lcid ope
fun mk_unop  (ope,t)        = mk_appl(mk_lcid ope,t)
fun mk_binop (ope,t1,t2)    = mk_appl(mk_appl(mk_lcid ope,t1),t2)
fun mk_ternop (ope,t1,t2,t3) = mk_appl(mk_appl(mk_appl(mk_lcid ope,t1),t2),t3)


fun mk_int i = fn bvars => fn freevars => (freevars, Const (Int i))

fun mk_string s = fn bvars => fn freevars => (freevars, Const (String s))

fun mk_varbind (vname) = fn bvars => fn freevars => (freevars,Varbind vname)

fun mk_abst (vbind,t) = 
      fn bvars => fn freevars =>
	 let val (fvs1,vbnd as Varbind vname) = vbind bvars freevars
      	     val (fvs2,at) = t (vname::bvars) fvs1
         in (fvs2,Abst(vbnd,at)) end

fun mk_quant (qname,abstr) = mk_unop (qname,abstr)

end  (* functor Absyn *)
