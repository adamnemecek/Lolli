(* Version of PROPOSITIONS for extended Horn clauses *)

signature PROPOSITIONS =
sig

structure Terms : TERMS

datatype gform  =                       (* Goal formula *)
     Gone				(* Empty Tensor *)	
  |  Gtrue                              (* Truth *)
  |  Gatom of Terms.term                (* Atomic G formula *)
  |  Gbang of gform			(* Banged Goal Formula *)
  |  Goplus of gform * gform		(* Multiplicative Disjunction *)
  |  Gwith of gform * gform             (* Additive Conjunction *)
  |  Gtensor of gform * gform           (* Multiplicative Conjunction *)
  |  Glinload of Terms.term * gform	(* Module Loading Linear Implication *)
  |  Glinimpl of dform * gform		(* Embedded Linear Implication *)
(*|  Gintimpl of dform * gform      	Embedded Intuistionistic Implication *)
  |  Gexists of Terms.varbind * gform   (* Existential *)
  |  Gall of Terms.varbind * gform	(* Embedded Universal *)
  |  Gguard of  gform * gform * gform	(* Guard Expression *)
  |  Gflex of Terms.term		(* Flexible Goal *)

and dform =                             (* Program formula *)
     Done				(* Empty Tensor *)
  |  Dresource of rform 		(* An R formula *)
  |  Dbang of rform			(* A Banged R formula *)
  |  Dtensor of dform * dform           (* Multiplicative Conjunction *)
  |  Dflex of Terms.term		(* Flexible D-Formula *)

and rform = 				(* Resource Formula *)
     Ratom of Terms.term		(* Atomic Resource formula *)
  |  Rwith of rform * rform             (* Additive Conjunction *)
  |  Rlinimpl of gform * rform          (* Implication *)
  |  Rall of Terms.varbind * rform      (* Universal *)
  |  Rflex of Terms.term		(* Flexible Resource *)
  
val gsubst : Terms.term -> Terms.varbind -> gform -> gform
val dsubst : Terms.term -> Terms.varbind -> dform -> dform
val rsubst : Terms.term -> Terms.varbind -> rform -> rform

end  (* signature PROPOSITIONS *)

functor Propositions (structure Terms : TERMS) : PROPOSITIONS =
struct

structure Terms = Terms

datatype gform  =                       (* Goal formula *)
     Gone				(* Empty Tensor *)	
  |  Gtrue                              (* Truth *)
  |  Gatom of Terms.term                (* Atomic G formula *)
  |  Gbang of gform			(* Banged Goal Formula *)
  |  Goplus of gform * gform		(* Multiplicative Disjunction *)
  |  Gwith of gform * gform             (* Additive Conjunction *)
  |  Gtensor of gform * gform           (* Multiplicative Conjunction *)
  |  Glinload of Terms.term * gform	(* Module Loading Linear Implication *)
  |  Glinimpl of dform * gform		(* Embedded Linear Implication *)
(*|  Gintimpl of dform * gform      	Embedded Intuistionistic Implication *)
  |  Gexists of Terms.varbind * gform   (* Existential *)
  |  Gall of Terms.varbind * gform	(* Embedded Universal *)
  |  Gguard of  gform * gform * gform	(* Guard Expression *)
  |  Gflex of Terms.term		(* Flexible Goal *)


and dform =                             (* Program formula *)
     Done				(* Empty Tensor *)
  |  Dresource of rform 		(* An R formula *)
  |  Dbang of rform			(* A Banged R formula *)
  |  Dtensor of dform * dform           (* Multiplicative Conjunction *)
  |  Dflex of Terms.term		(* Flexible D-Formula *)

and rform = 				(* Resource Formula *)
     Ratom of Terms.term		(* Atomic Resource formula *)
  |  Rwith of rform * rform             (* Additive Conjunction *)
  |  Rlinimpl of gform * rform          (* Implication *)
  |  Rall of Terms.varbind * rform      (* Universal *)
  |  Rflex of Terms.term		(* Flexible Resource *)

local fun formsubst t x = 
  let fun gsb (Gone) = Gone
	| gsb (Gtrue) = Gtrue
        | gsb (Gatom(s)) = Gatom(Terms.subst t x s)
	| gsb (Gbang(g)) = Gbang(gsb g)
        | gsb (Goplus(g1,g2)) = Goplus(gsb g1, gsb g2)
        | gsb (Gwith(g1,g2)) = Gwith(gsb g1, gsb g2)
        | gsb (Gtensor(g1,g2)) = Gtensor(gsb g1, gsb g2)
        | gsb (Glinload(s,g)) = Glinload(Terms.subst t x s, gsb g)
        | gsb (Glinimpl(d,g)) = Glinimpl(dsb d, gsb g)
        | gsb (Gexists(y,g)) =
	   Gexists(y, if Terms.shadow x y then g else gsb g)
	| gsb (Gall(y,g)) =
	   Gall(y, if Terms.shadow x y then g else gsb g)
        | gsb (Gguard(g1,g2,g3)) = Gguard(gsb g1, gsb g2, gsb g3)
        | gsb (Gflex(s)) = Gflex(Terms.subst t x s)
      and dsb (Done) = Done
	| dsb (Dresource(r)) = Dresource(rsb r)
	| dsb (Dbang(r)) = Dbang(rsb r)
	| dsb (Dtensor(d1,d2)) = Dtensor(dsb d1,dsb d2)
        | dsb (Dflex(s)) = Dflex(Terms.subst t x s)
      and rsb (Ratom(s)) = Ratom(Terms.subst t x s)
        | rsb (Rwith(r1,r2)) = Rwith(rsb r1, rsb r2)
        | rsb (Rlinimpl(g,r)) = Rlinimpl(gsb g, rsb r)
        | rsb (Rall(y,r)) =
           Rall(y, if Terms.shadow x y then r else rsb r)
        | rsb (Rflex(s)) = Rflex(Terms.subst t x s)
       in (gsb , dsb , rsb) end
in
  fun gsubst t x g =
         let val ( gsb , _ , _ ) = formsubst t x in gsb g end
  and dsubst t x d =
         let val ( _ , dsb , _ ) = formsubst t x in dsb d end
  and rsubst t x r =
         let val ( _ , _ , rsb ) = formsubst t x in rsb r end
end

end  (* functor Propositions *)


