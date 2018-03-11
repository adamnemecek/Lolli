	
(* Version of TERMS for hereditary Harrop formulas *)

signature TERMS =
sig

datatype term = 
     Bvar of string             (* Bound Variables *)
  |  Evar of string * int * term list 
			        (* Logic Variables , Stamped , Depends on *)
  |  Uvar of string * int	(* Parameters , Stamped *)
  |  Const of sign_entry	(* Constants *)
  |  Appl of term * term        (* Applications *)
  |  Abst of varbind * term    	(* Abstractions *)

and sign_entry			(* Simplified version of ELF signature *)
    = Name of string
    | Int of int		  (* integers *)
    | String of string		  (* strings *)

and varbind = Varbind of string (* Variable binders *)

type substitution

exception Illegal of string
exception Internal of string

val empty_substitution : substitution
val is_empty_substitution : substitution -> bool
val new_evar : varbind -> term list -> term
val new_uvar : varbind -> term
val shadow : varbind -> varbind -> bool
val subst : term -> varbind -> term -> term
val unify : term -> term -> (substitution -> unit) -> substitution -> unit

val project_substitution : term list -> substitution -> substitution
val makestring_term : term -> string
val print_term : outstream -> term -> unit
val makestring_clause : term -> string
val print_clause : outstream -> term -> unit
val makestring_raw : term -> string
val print_raw : outstream -> term -> unit
val makestring_substitution : substitution -> string
val print_substitution : substitution -> unit
val makestring_varbind : varbind -> string
val generalize: term -> substitution -> term
val dereference : term -> substitution -> term
val eval_exp : term -> term
val term_to_int : term -> int
end  (* signature TERMS *)

functor Terms () : TERMS =
struct

datatype term = 
     Bvar of string             (* Bound Variables *)
  |  Evar of string * int * term list 
			        (* Logic Variables , Stamped , Depends on *)
  |  Uvar of string * int	(* Parameters , Stamped *)
  |  Const of sign_entry	(* Constants *)
  |  Appl of term * term        (* Applications *)
  |  Abst of varbind * term    	(* Abstractions *)

and sign_entry			(* Simplified version of ELF signature *)
    = Name of string
    | Int of int		  (* integers *)
    | String of string		  (* strings *)

and varbind = Varbind of string (* Variable binders *)

type substitution = (term * term) list

val empty_substitution = nil

fun is_empty_substitution nil = true
  | is_empty_substitution _   = false

exception Illegal of string
exception Internal of string


datatype associativity = In | Left | Right | None

fun fixity "="    = In
  | fixity "=:="  = In
  | fixity "=\\=" = In
  | fixity "=<"   = In
  | fixity ">="   = In
  | fixity "<"    = In
  | fixity ">"    = In
  | fixity "is"   = In
  | fixity "+"    = Left
  | fixity "-"    = Left
  | fixity "*"    = Left
  | fixity "/"    = Left
  | fixity "::"   = Right
  | fixity _      = None

fun mst_varbind (Varbind(name)) = name

and mst_name "cut" = "!"
  | mst_name name =
	let fun rec_mn nil = nil
	      | rec_mn (ch::tail)  = 
			if (((ch >= "a") andalso (ch <= "z")) orelse
			    ((ch >= "A") andalso (ch <= "Z")) orelse
			    ((ch >= "0") andalso (ch <= "9")) orelse
			    (ch = "_"))
			then (ch::(rec_mn tail))
			else ("^"::ch::(rec_mn tail))
	in (implode (rec_mn (explode name))) end

and mst_const (Name name)  = mst_name name
  | mst_const (String s)   = "\"" ^ s ^ "\""
  | mst_const (Int i)      = Int.toString(i)

and mst_raw (Bvar(vname)) = mst_name vname
(*| mst_raw (Evar(vname,stamp,_)) = "?" ^ vname ^ makestring stamp *)
  | mst_raw (Evar(vname,stamp,_)) =  vname ^ "_" ^ Int.toString(stamp)
  | mst_raw (Uvar(vname,stamp)) = "!" ^ vname ^ Int.toString(stamp)
  | mst_raw (Const c) = mst_const c
  | mst_raw (Abst(x,M)) = "(" ^ mst_varbind x ^ " \\ " ^ mst_raw M ^ ")" 
  | mst_raw (M as Appl(M1,M2)) = "(" ^ mst_raw M1 ^ " " 
					^ mst_raw M2 ^ ")" 
  | mst_raw _ = raise Illegal " Match: mst_raw"

and mst_term _ p (Bvar(vname)) = mst_name vname
(*| mst_term _ p (Evar(vname,stamp,_)) = "?" ^ vname ^ makestring stamp *)
  | mst_term _ p (Evar(vname,stamp,_)) = (mst_name vname) ^ "_" 
					 		  ^ Int.toString(stamp)
  | mst_term _ p (Uvar(vname,stamp)) = "!" ^ (mst_name vname) 
					   ^ Int.toString(stamp)
  | mst_term _ p (Const c) = mst_const c
  | mst_term q p (Appl(Const(Name "forall"), Abst(x,M))) =
        parens 30 p ("forall " ^ mst_varbind x ^ " \\ " ^ mst_term q 40 M)
  | mst_term q p (Appl(Const(Name "exists"), Abst(x,M))) =
        parens 30 p ("exists " ^ mst_varbind x ^ " \\ " ^ mst_term q 40 M)
  | mst_term q p (Appl(Const(Name "dcgcodebracket"),M)) =
	("[" ^ mst_term q 0 M ^ "]")
  | mst_term q p (Appl(Const(Name "bang"),M)) =
	("{" ^ mst_term q 0 M ^ "}")
  | mst_term q p (Appl(Appl(Const(Name ";"),M),N)) =
        parens 50 p (mst_term q 50 M ^ "; " ^ mst_term q 40 N)
  | mst_term q p (Appl(Appl(Const(Name "&"),M),N)) =
	parens 60 p (mst_term q 60 M ^ " & " ^ mst_term q 50 N)
  | mst_term q p (Appl(Appl(Const(Name ","),M),N)) =
	parens 70 p (mst_term q 70 M ^ " , " ^ mst_term q 60 N)
  | mst_term q p (Appl(Appl(Const(Name "-o"),M),N)) =
	if q 
	  then parens 80 p (mst_term false 80 M ^ " -o " ^ mst_term true 70 N)
	  else parens 80 p (mst_term false 70 N ^ " :- " ^ mst_term true 80 M)
  | mst_term q p (Appl(Appl(Const(Name "=>"),M),N)) =
	if q 
	  then parens 80 p (mst_term false 80 M ^ " => " ^ mst_term true 70 N)
	  else parens 80 p (mst_term false 70 N ^ " <= " ^ mst_term true 80 M)
  | mst_term q p (Appl(Appl(Const(Name "-->"),M),N)) =
	parens 80 p (mst_term false 70 N ^ " --> " ^ mst_term true 80 M)
  | mst_term q p (Appl(Appl(Const(Name "--o"),M),N)) =
        parens 90 p (mst_term q 90 M ^ " --o " ^ mst_term q 80 N)
  | mst_term q p (Appl(Appl(Appl(Const(Name "guard"),M),N1),N2)) =
        parens 100 p (mst_term q 90 M ^ " -> " ^ 
		      mst_term q 90 N1 ^ " | " ^ mst_term q 90 N2)
  | mst_term q p (Appl(t as Appl(Const(Name Op),M),N)) =
      (case (fixity Op) 
	of In    => parens 110 p (mst_term q 100 M ^ " " ^ Op ^ " " ^ 
				  mst_term q 110 N)
	 | Left  => parens 120 p (mst_term q 110 M ^ " " ^ Op ^ " " ^ 
				  mst_term q 120 N)
	 | Right => parens 130 p (mst_term q 130 M ^ " " ^ Op ^ " " ^ 
				  mst_term q 120 N)
	 | None  => parens 140 p (mst_term q 130 t ^ " " ^ 
				  mst_term q 140 N))
(*
	 | None  => parens 140 p (Op ^ " " ^ mst_term q 130 M ^ " " ^ 
				  mst_term q 140 N))
*)
  | mst_term q p (Appl(M,N)) = parens 140 p (mst_term q 130 M ^ " " ^  
					     mst_term q 140 N)
  | mst_term _ p (Abst(x,M0)) = 
	raise Internal(" in mst_term: What's this lambda term doing here (" ^
			makestring_varbind x ^ " \\ " ^ 
			makestring_term M0 ^ ")?")
  | mst_term _ _ _ = raise Internal(" Match: mst_term")

and parens q p str = if q <= p then "(" ^ str ^ ")" else str

and makestring_term M = mst_term true 0 M
and makestring_clause M = mst_term false 0 M
and makestring_raw M = mst_raw M
and makestring_varbind (Varbind(x)) =
       mst_varbind (Varbind(x))

fun print_term ostream M = output(ostream, makestring_term M)
fun print_clause ostream M = output(ostream, makestring_clause M)
fun print_raw  ostream M = output(ostream, makestring_raw M)

fun makestring_substitution nil = ""
  | makestring_substitution ((evar,t)::rest) =
     (case evar of Evar(_,_,_) => makestring_term evar
		| M => raise Internal
			       (" in makestring_substitution: Non-Evar (" ^
				makestring_term M ^ ").")) ^
     " <- " ^ makestring_term t ^
     (case rest of nil => "" | _ => (" ,\n" ^ makestring_substitution rest))

val print_substitution = print o makestring_substitution



local val varcount = ref 0
in
 fun new_evar (Varbind(vname)) uvars =
   ( varcount := !varcount + 1;
     Evar(vname,!varcount,uvars) )

 fun new_uvar (Varbind(vname)) =
   ( varcount := !varcount + 1;
     Uvar(vname,!varcount) )
end  (* val varcount *)

fun shadow (Varbind(vname1)) (Varbind(vname2)) = (vname1 = vname2)

fun subst s (x as Varbind(vname)) t =
    let fun sb (t as Bvar(bvname)) = if vname = bvname then s else t
          | sb (Appl(t1,t2)) = Appl(sb t1,sb t2)
	  | sb (t as Abst(v,t1)) = if shadow x v then t else Abst(v,sb t1)
	  | sb t = t
         in sb t end

(* val lookup : term -> substitution -> term opt *)
fun lookup (Evar(_,stamp,_)) subst =
  let fun lk nil = NONE
        | lk ((Evar(_,tstamp,_),t)::tail) =
             if stamp = tstamp then SOME t else lk tail
        | lk ((s,t)::tail) = 
	     raise Internal(" in lookup: substitution maps a non-Evar (" ^
			    makestring_term s ^ "," ^ makestring_term t ^ ").")
       in lk subst end
  | lookup s subst = raise Internal(" in lookup: argument is not an Evar (" ^
			    makestring_term s ^ ").")

fun same_evar (s as Evar(_,stamp1,_)) t subst = 
  let fun se (t as Evar(_,stamp2,_)) =
                (case (lookup t subst)
                   of NONE => (stamp1 = stamp2)
	            | SOME t0 => se t0)
        | se _ = false
       in se t end
  | same_evar s _ _ = 
	raise Internal(" in same_evar: argument is not an Evar (" ^
		       makestring_term s ^ ").")

fun init_seg uvars1 uvars2 = length uvars1 <= length uvars2

fun extended_occurs_check (s as Evar(_,stamp1,uvars1)) t sc subst =
  let fun eoc (t as Evar(x,stamp2,uvars2)) sc subst = 
                (case (lookup t subst)
	           of NONE => if (stamp1 = stamp2)
			         then ()
				 else if init_seg uvars2 uvars1
					 then sc subst
					 else sc ((t,new_evar (Varbind(x)) 
							      uvars1)::subst)
	            | SOME t0 => eoc t0 sc subst)
        | eoc (Appl(t1,t2)) sc subst = eoc t1 (fn newsubst => 
						     eoc t2 sc newsubst) subst
        | eoc (Uvar(_,stamp2)) sc subst =
	     if exists (fn (Uvar(_,stamp1)) => (stamp1 = stamp2)
			 | uv => raise
			       Internal(" in eoc: Evar depends on non-Uvar (" ^
					makestring_term uv ^ ")."))
		       uvars1
		then sc subst
		else ()
	| eoc (Abst (x,t)) sc subst = eoc t sc subst
	| eoc _ sc subst = sc subst
       in eoc t sc subst end
  | extended_occurs_check s _ _ _ = 
	raise Internal(" in eoc: argument is not an Evar (" ^
			makestring_term s ^ ").")

(*Do we need a Bvar case in unify  now that we may encounter them in active
     terms? I don't think we do yet, as we will not be unifying within
     lambda terms yet. *)

fun unify (s as Evar _) t sc subst = unify_evar s t sc subst
  | unify s (t as Evar _) sc subst = unify_evar t s sc subst
  | unify (Const(Name cname1)) (Const(Name cname2)) sc subst =
       if cname1 = cname2 then (sc subst) else ()
  | unify (Const(String s1)) (Const(String s2)) sc subst =
       if s1 = s2 then (sc subst) else ()
  | unify (Const(Int i1)) (Const(Int i2)) sc subst =
       if i1 = i2 then (sc subst) else ()
  | unify (Uvar(_,stamp1)) (Uvar(_,stamp2)) sc subst =
       if stamp1 = stamp2 then (sc subst) else ()
  | unify (Appl(s1,s2)) (Appl(t1,t2)) sc subst =
       unify s1 t1 (fn newsubst => unify s2 t2 sc newsubst) subst
  | unify (Abst(x1,M1)) (Abst(x2,M2)) _ _ = 
	raise Illegal(": Unification of Lambda Terms not defined (" ^
			"(" ^ makestring_varbind x1 ^ " \\ " ^ 
			      makestring_term M1 ^ ")" ^ " = " ^
			"(" ^ makestring_varbind x2 ^ " \\ " ^ 
			      makestring_term M2 ^ ")" ^ " ).")
  | unify _ _ sc subst = ()

and unify_evar s t sc subst =
       case (lookup s subst)
          of NONE => if same_evar s t subst
			then sc subst  		       (* x = x *)
			else extended_occurs_check s t
			       (fn newsubst => sc ((s,t)::newsubst))
			       subst
	   | SOME s0 => unify s0 t sc subst

fun dereference s subst =
    let fun deref (s as Evar _) =
	       (case (lookup s subst)
		  of NONE => s
		   | SOME s0 => deref s0)
          | deref (Appl(s1,s2)) = Appl(deref s1, deref s2)
	  | deref (Abst(x,t)) = Abst(x,deref t)
          | deref s = s
      in deref s end

fun project_substitution evars subst = 
    let fun prc acc_subst nil = acc_subst
	  | prc acc_subst ((bdevar,t)::tail) =
	      if exists (fn evar => bdevar = evar) evars
		 then prc ((bdevar,dereference t subst)::acc_subst) tail
		 else prc acc_subst tail
        in prc nil subst end

local fun delete h nil = nil
      | delete h (h1::t) = 
		if (h = h1) then (delete h t) else (h1::(delete h t))
    fun delete_dups nil = nil
      | delete_dups (h::t) = (h::(delete_dups (delete h t)))
    fun convert_evars (Evar(vname,stamp,_)) =  
		let val newname = vname ^ "_" ^ Int.toString(stamp)
		in (Bvar(newname),[newname]) end
      | convert_evars (Abst(v,t1)) = 
		let val (new_t1,vars1) = convert_evars t1 
		in (Abst(v,new_t1),vars1) end
      | convert_evars (Appl(t1,t2)) = 
		let val (new_t1,vars1) = convert_evars t1
                    val (new_t2,vars2) = convert_evars t2
		in (Appl(new_t1,new_t2),vars1 @ vars2) end
      | convert_evars t = (t,[])
    fun elaborate t nil = t
      | elaborate t (v::vs) = 
	 	(Appl(Const(Name "forall"), Abst(Varbind(v),elaborate t vs)))
in fun generalize t subst  = 
		let val (new_t,vars) = convert_evars (dereference t subst)
		in elaborate new_t (delete_dups vars) end 
end


datatype value = IntV of int | Func of value -> value

fun exp_to_value (Const(Name "+")) = 
               Func (fn (IntV(e1)) => Func(fn (IntV(e2)) => (IntV(e1 + e2))))
  | exp_to_value (Const(Name "-")) = 
               Func (fn (IntV(e1)) => Func(fn (IntV(e2)) => (IntV(e1 - e2))))
  | exp_to_value (Const(Name "*")) = 
               Func (fn (IntV(e1)) => Func(fn (IntV(e2)) => (IntV(e1 * e2))))
  | exp_to_value (Const(Name "/")) = 
               Func (fn (IntV(e1)) => Func(fn (IntV(e2)) => (IntV(e1 div e2))))
  | exp_to_value (Const(Int i))   = IntV i
  | exp_to_value (c as Const _)    = 
	raise Illegal ("a non-integer constant (" ^ makestring_term c ^").")
  | exp_to_value (Appl(s,t))  = 
	let val (Func f) = (exp_to_value s) in f (exp_to_value t) end
  | exp_to_value (b as Bvar _) = 
	raise Illegal("an unbound Bvar (" ^ makestring_term b ^").")
  | exp_to_value (e as Evar _) = 
	raise Illegal("an unbound Evar (" ^ makestring_term e ^").")
  | exp_to_value (t) = 
	raise Illegal("an illegal value (" ^ makestring_term t ^").")
fun eval_exp e = let val (IntV i) = exp_to_value e in Const (Int i) end

fun term_to_int (Const(Int i)) = i
  | term_to_int (c as Const _)    = 
	raise Illegal ("in term_to_int: argument contains a non-integer " ^
			" constant (" ^ makestring_term c ^").")
  | term_to_int t = raise Illegal(" in term_to_int: non-Const argument (" ^
				      makestring_term t ^ ").")

end  (* functor Terms *)


