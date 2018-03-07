signature TERMS_TO_PROPS =
  sig
    structure Props : PROPOSITIONS

    exception Illegal of string
    exception Internal of string

    val term_to_gform : Props.Terms.substitution ->
				Props.Terms.term -> Props.gform
    val term_to_dform : Props.Terms.substitution ->
				Props.Terms.term -> Props.dform
    val term_to_rform : Props.Terms.substitution ->
				Props.Terms.term -> Props.rform
    val clauses_to_dform : (string list * Props.Terms.term) list 
				-> Props.dform
    val query_to_goal : string list * Props.Terms.term
			  -> Props.Terms.term list * Props.gform
  end  (* signature TERMS_TO_PROPS *)

functor Terms_To_Props (structure Props : PROPOSITIONS) : TERMS_TO_PROPS =
struct

structure Props = Props
open Props
structure Terms = Terms
open Terms

exception Illegal of string
exception Internal of string

fun rigid_head (Const _) = true
  | rigid_head (Uvar _) = true
  | rigid_head (Appl(M,_)) = rigid_head M
  | rigid_head (Evar(_,_,_)) = false
  | rigid_head _ = false

(* We don't need this at the moment, but will later when we do l-lambda
fun head_beta_normalize (M as (Bvar _)) = M
  | head_beta_normalize (M as (Evar(_,_,_,ref NONE))) = M
  | head_beta_normalize (M as (Evar(_,_,_,ref (SOME M0)))) =
       head_beta_normalize M0
  | head_beta_normalize (M as (Uvar _)) = M
  | head_beta_normalize (M as (Const _)) = M
  | head_beta_normalize (Appl(M1,M2)) =
      let val normal_M1 = head_beta_normalize M1 in
      (case normal_M1
	 of (Abst(vbd,body)) =>
	    head_beta_normalize (Sb.renaming_apply_sb (Sb.term_sb vbd M2) body)
	  | _ => Appl(normal_M1,M2))
      end
  | head_beta_normalize (M as (Abst _)) = M
*)


fun ttg subst M = ttg_norm subst (dereference M subst)
and ttd subst M = ttd_norm subst (dereference M subst)
and ttr subst M = ttr_norm subst (dereference M subst)

and ttg_norm _ (Const((Name "true"))) = Gone
  | ttg_norm _ (Const((Name "erase"))) = Gtrue
  | ttg_norm S (Appl(Const((Name "bang")),M)) = Gbang(ttg S M)
  | ttg_norm S (Appl(Appl(Const((Name ";")),M),N)) = Goplus(ttg S M,ttg S N)
  | ttg_norm S (Appl(Appl(Const((Name "&")),M),N)) = Gwith(ttg S M,ttg S N)
  | ttg_norm S (Appl(Appl(Const((Name ",")),M),N)) = Gtensor(ttg S M,ttg S N)
  | ttg_norm S (Appl(Appl(Const((Name "-o")),M),N)) = Glinimpl(ttd S M,ttg S N)
  | ttg_norm S (Appl(Appl(Const((Name "--o")),t),M)) = Glinload(t,ttg S M)
  | ttg_norm S (Appl(Appl(Const((Name "=>")),M),N)) = Glinimpl(Dbang(ttr S M),
  							       ttg S N)
  | ttg_norm S (Appl(Const((Name "exists")),M)) = Gexists(ttg_abst S M)
  | ttg_norm S (Appl(Const((Name "forall")),M)) = Gall(ttg_abst S M)
  | ttg_norm S (Appl(Appl(Appl(Const(Name "guard"),M),N1),N2)) =
       Gguard (ttg S M, ttg S N1, ttg S N2)
  | ttg_norm S M = let val M0 = (dereference M S) 
			in if rigid_head M0 then Gatom(M0) else Gflex(M) end

and ttd_norm S (Const(Name "true")) = Done
  | ttd_norm S (Const(Name "erase")) = 
	raise Illegal(": Cannot add erase to bounded context.")
  | ttd_norm S (Appl(Const(Name "bang"),M)) = Dbang(ttr S M)
  | ttd_norm S (Appl(Appl(Const(Name ","),M),N)) = Dtensor(ttd S M,ttd S N)
  | ttd_norm S (T as Appl(Appl(Const(Name "&"),M),N)) = Dresource(ttr S T)
  | ttd_norm S (T as Appl(Appl(Const(Name "-o"),M),N)) = Dresource(ttr S T)
  | ttd_norm S (T as Appl(Appl(Const(Name "--o"),t),M)) = 
 	raise Illegal (": Cannot use --o at clause level.")
  | ttd_norm S (T as Appl(Appl(Const(Name "=>"),M),N)) = Dresource(ttr S T)
  | ttd_norm S (Appl(Const(Name "exists"),M)) = 
	raise Illegal(": Cannot use existential at bounded clause level.")
  | ttd_norm S (T as Appl(Const(Name "forall"),M)) = Dresource(ttr S T)
  | ttd_norm S (Appl(Appl(Appl(Const(Name "guard"),M),N1),N2)) =
	raise Illegal(": Cannot use guard at bounded clause level.")
  | ttd_norm S M = let val M0 = (dereference M S) 
			in if rigid_head M0
				then Dresource(ttr S M0) else Dflex(M) end

and ttr_norm S (Const(Name "true")) = 
	raise Illegal (": Cannot add true to unbounded context.")
  | ttr_norm S (Const(Name "erase")) = 
	raise Illegal (": Cannot add erase to unbounded context.")
  | ttr_norm S (Appl(Const(Name "bang"),M)) = 
	raise Illegal (": Cannot add !'ed formula to unbounded context.")
  | ttr_norm S (Appl(Appl(Const(Name ","),M),N)) = 
	raise Illegal (": Cannot add tensor'ed formula to unbounded context.")
  | ttr_norm S (Appl(Appl(Const(Name "&"),M),N)) = Rwith(ttr S M,ttr S N)
  | ttr_norm S (Appl(Appl(Const(Name "-o"),M),N)) = Rlinimpl(ttg S M,ttr S N)
  | ttr_norm S (Appl(Appl(Const(Name "--o"),t),M)) = 
 	raise Illegal (": Cannot use --o at clause level.")
  | ttr_norm S (Appl(Appl(Const(Name "=>"),M),N)) = Rlinimpl(Gbang(ttg S M),
							     ttr S N)
  | ttr_norm S (Appl(Const(Name "exists"),M)) = 
	raise Illegal(": Cannot use existential at unbounded clause level.")
  | ttr_norm S (Appl(Const(Name "forall"),M)) = Rall(ttr_abst S M)
  | ttr_norm S (Appl(Appl(Appl(Const(Name "guard"),M),N1),N2)) =
	raise Illegal(": Cannot use guard at unbounded clause level.")
  | ttr_norm S M = let val M0 = (dereference M S) 
			in if rigid_head M0 then Ratom(M0) else Rflex(M) end


and ttg_abst S (Abst(vbnd,M)) = (vbnd,ttg S M)
  | ttg_abst S M =
		 raise Illegal("Argument to quantifier is not an abstraction")

and ttr_abst S (Abst(vbnd,M)) = (vbnd,ttr S M)
  | ttr_abst S M = 
		 raise Illegal("Argument to quantifier is not an abstraction")

val term_to_gform = ttg
val term_to_dform = ttd
val term_to_rform = ttr

fun subst_evars nil nil g = g
  | subst_evars (evar::evars) (x::xs) g =
       subst_evars evars xs (gsubst evar x g)
  | subst_evars _ _ _ = 
	raise Internal(" in subst_evars: lists of unequal length.")

fun query_to_goal (varnames, A) =
  let val xs = map Terms.Varbind varnames
      val evars = map (fn vname => Terms.new_evar vname nil) xs
      val g = term_to_gform Terms.empty_substitution A
   in (evars,subst_evars evars xs g) end

fun abstract_over_rform r nil = r
  | abstract_over_rform r (vname::fvs) =
      abstract_over_rform (Rall((Terms.Varbind(vname),r))) fvs

and abstract_over_dform d nil = d
  | abstract_over_dform (Dresource(r)) fvs =
      Dresource(abstract_over_rform r fvs)
  | abstract_over_dform (Dbang(r)) fvs =
      Dbang(abstract_over_rform r fvs)
  | abstract_over_dform (d as Dtensor _) fvs = d
  | abstract_over_dform (d as Done) fvs = d
  | abstract_over_dform _ _ = raise Illegal "Match: abstract_over_dform"

fun clauses_to_dform nil = Done
  | clauses_to_dform ((fvars,A)::clauses) =
       Dtensor((abstract_over_dform (term_to_dform Terms.empty_substitution A)
				    fvars),
               clauses_to_dform clauses)

end  (* functor Terms_To_Props *)
