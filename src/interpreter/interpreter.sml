    (******************************************************************)
    (*                                                                *)
    (*  FILE: interpreter.sml                                         *)
    (*        The core of the system, this covers the logic and the   *)
    (*        built-ins.                                              *)
    (*                                                                *)
    (*  AUTHOR: Joshua S. Hodas (hodas@saul.cis.upenn.edu)            *)
    (*  DATE: 10/19/92                                                *)
    (*                                                                *)
    (*  Portions of this and the other files in the system are based  *)
    (*  code originally developed by Frank Pfenning and Conal Elliott *)
    (*                                                                *)
    (******************************************************************)

(* Version of INTERPRETER for first-order linear logic fragment 
   with meta-variables*)

signature INTERPRETER =
  sig
    structure Terms_To_Props : TERMS_TO_PROPS
    val solve : Terms_To_Props.Props.gform 
		 -> Terms_To_Props.Props.dform 
		 -> Terms_To_Props.Props.Terms.term list
	         -> Terms_To_Props.Props.Terms.substitution 
		 -> (Terms_To_Props.Props.Terms.substitution 
		      -> Terms_To_Props.Props.dform -> bool -> unit)
		 -> unit
    val ll_file : string -> unit
    val ll : unit -> unit

    structure Parse : PARSE
end

functor Interpreter (structure Terms_To_Props : TERMS_TO_PROPS
		     structure Parse : PARSE
	               sharing Terms_To_Props.Props.Terms = 
                               Parse.Absyn.Terms) : INTERPRETER =
struct

structure Terms_To_Props = Terms_To_Props
structure Parse = Parse

structure Props = Terms_To_Props.Props
structure Terms = Terms_To_Props.Props.Terms


open Terms_To_Props
open Props
open Terms

exception Illegal of string
exception Internal of string
exception POP
exception POPALL
exception POPAUX
exception EXIT
exception ABORT
exception UnexpectedReturn;

val ll_version = "0.701, November 30, 1992";

val current_out_stream = ref std_out
val current_in_stream = ref std_in


fun built_in "write"  		= true
  | built_in "write_raw" 	= true
  | built_in "write_clause" 	= true
  | built_in "write_sans" 	= true
  | built_in "nl"     		= true
  | built_in "read"   		= true
  | built_in "telling" 		= true
  | built_in "seeing" 		= true
  | built_in "timing" 		= true
  | built_in "load"   		= true
  | built_in "cd"    		= true
  | built_in "system"  		= true
  | built_in "top"    		= true
  | built_in "fail"   		= true
  | built_in "pop"    		= true
  | built_in "popall" 		= true
  | built_in "abort"  		= true
  | built_in "exit"   		= true
  | built_in "bye"    		= true
  | built_in "is"     		= true
  | built_in "="      		= true
  | built_in "=:="    		= true
  | built_in "=\\="   		= true
  | built_in "=<"     		= true
  | built_in ">="     		= true
  | built_in ">"      		= true
  | built_in "<"      		= true
  | built_in "explode" 		= true
  | built_in "explode_words"	= true
  | built_in "var"    		= true
  | built_in "nonvar" 		= true
  | built_in "generalize"	= true
  | built_in   _      		= false

fun func_symbol_of (Appl (f,_)) = func_symbol_of f
  | func_symbol_of (Const (Name funct)) = funct
  | func_symbol_of (Const c) = 
	raise Illegal " in func_symbol_of: non-name in function position."
  | func_symbol_of (v as Uvar _) = makestring_term v 
  | func_symbol_of _ = raise Internal " Match: func_symbol_of"

fun d_scan (Done) subst = Done
  | d_scan (Dresource R) subst = Dresource (r_scan R subst)
  | d_scan (Dbang R) subst = Dbang (r_scan R subst)
  | d_scan (Dtensor (D1,D2)) subst = 
			Dtensor (d_scan D1 subst, d_scan D2 subst)
  | d_scan (Dflex M) subst =
	(case Terms_To_Props.term_to_dform subst M
             of Dflex(M1) => raise Illegal
		     (": Dformula with flexible head (" ^ 
			makestring_term M ^ ") cannot be assumed.")
	      | d => d_scan d subst)

and r_scan (Ratom M) subst = 
	if (built_in (func_symbol_of M))
	  then raise Illegal(": Cannot assume clause with special predicate ("^
				makestring_term M ^ ") as head.")
	  else (Ratom M)
  | r_scan (Rwith (R1,R2)) subst = 
			Rwith (r_scan R1 subst, r_scan R2 subst)
  | r_scan (Rlinimpl (G,R)) subst = Rlinimpl (G, r_scan R subst)
  | r_scan (Rall (V,R)) subst = Rall (V, r_scan R subst)
  | r_scan (Rflex M) subst =
	(case Terms_To_Props.term_to_rform subst M
             of Rflex(M1) => raise Illegal
		     (": Rformula with flexible head (" ^ 
			makestring_term M ^ ") cannot be assumed.")
	      | r => r_scan r subst);


fun solve (Gone) prog uvars subst sc = sc subst prog false
  | solve (Gtrue) prog uvars subst sc = sc subst prog true
  | solve (Gbang(g)) prog uvars subst sc =
      solve g prog uvars subst
	    (fn newsubst => (fn  newprog => (fn newflag =>
               if equalprog prog newprog 
		 then sc newsubst newprog false
		 else ())))
  | solve (Goplus(g1,g2)) prog uvars subst sc =
      ( solve g1 prog uvars subst sc ; solve g2 prog uvars subst sc )
  | solve (Gtensor(g1,g2)) prog uvars subst sc =
      solve g1 prog uvars subst
            (fn newsubst => (fn newprog => (fn newflag =>
               solve g2 newprog uvars newsubst 
		     (fn newsubst2 => (fn newprog2 => (fn newflag2 =>
			sc newsubst2 newprog2 (newflag orelse newflag2))))))) 
  | solve (Gwith(g1,g2)) prog uvars subst sc =
      solve g1 prog uvars subst
	    (fn newsubst => (fn newprog => (fn newflag =>
               solve g2 prog uvars newsubst 
		     (fn newsubst2 => (fn newprog2 => (fn newflag2 =>
		     check newflag newflag2 newprog newprog2 newsubst2 sc))))))
  | solve (Glinimpl(d,g)) prog uvars subst sc =
      let val newclauses = d_scan d subst
	in solve g (Dtensor(newclauses,prog)) uvars subst
	      (fn newsubst => (fn (Dtensor(b,newprog)) => (fn newflag =>
	         check2 newflag b newprog newsubst sc)))
	end
  | solve (Gatom(a)) prog uvars subst sc =
        if built_in (func_symbol_of a) 
	  then execute_built_in a prog uvars subst sc 
	  else pick_resource a prog uvars subst sc
  | solve (Gexists(x,g)) prog uvars subst sc =
      solve (gsubst (new_evar x uvars) x g) prog uvars subst  sc
  | solve (Gall(x,g)) prog uvars subst sc =
      let val uvar = new_uvar x
       in solve (gsubst uvar x g) prog (uvar::uvars) subst sc end
  | solve (Gguard(guard,g1,g2)) prog uvars subst sc =
   let exception guard_success of Props.Terms.substitution * Props.dform * bool
	in ( solve guard prog uvars subst
		  (fn newsubst => fn newprog => fn newflag =>
		     raise guard_success(newsubst,newprog,newflag)) ;
	     solve g2 prog uvars subst sc )
		handle guard_success(newsubst,newprog,newflag) => 
		 	solve g1 newprog uvars newsubst 
			     (fn newsubst2 => (fn newprog2 => (fn newflag2 =>
                             sc newsubst2 newprog2 (newflag orelse newflag2))))
	end
  | solve (Glinload(f,g)) prog uvars subst sc =
      let val f1 = dereference f subst
	  val modname = ((func_symbol_of f1) 
		handle Internal _  =>
		   raise Illegal (": Unbound variable as module name in --o ("
				  ^ makestring_term f1 ^ ").")
		     | Illegal _ =>
		   raise Illegal (": non-name as module name in --o ("
				  ^ makestring_term f1 ^ ")."))
	  val (modname2,params,locals,clauses) = 
					Parse.file_parse (modname ^ ".ll")
	  val rawclauses = clauses_to_dform clauses
	  val newlocals = map Terms.Varbind locals
	  val newuvars = map new_uvar newlocals
	  val newparams = map Terms.Varbind params
	  val newevars = map (fn p => new_evar p uvars) newparams
	  fun dsublist nil nil d = d
	    | dsublist (t::ts) (x::xs) d = dsubst t x (dsublist ts xs d)
	  val newclauses = dsublist newuvars newlocals 
				   (dsublist newevars newparams rawclauses)
	  fun make_term (modname::nil) = modname
	    | make_term (h::t) = Appl(make_term t,h)
	  val modhead = make_term (rev ((Const (Name modname2))::newevars))
      in
	unify modhead f1
	      (fn newsubst => 
        	 solve g (Dtensor(d_scan newclauses newsubst,prog)) 
		    (newuvars @ uvars) newsubst
		    (fn newsubst1 => (fn (Dtensor(b,newprog)) => (fn newflag =>
               		check2 newflag b newprog newsubst1 sc))))
	      subst
      end
  | solve (Gflex(M)) prog uvars subst sc =
	(case Terms_To_Props.term_to_gform subst M
         of Gflex(M1) => raise Illegal (": Unbound variable as goal (" ^
					makestring_term M ^ ").")
	  | g => solve g prog uvars subst sc)

and pick_resource a prog uvars subst sc =
      let fun rec_pick (Done) sc = ()
	    | rec_pick (Dresource(r)) sc = sc Done r
	    | rec_pick (r1 as Dbang(r)) sc  = sc r1 r
            | rec_pick (Dtensor(d1,d2)) sc =
	        (rec_pick d1 (fn newd1 => sc (Dtensor(newd1,d2))); 
		 rec_pick d2 (fn newd2 => sc (Dtensor(d1,newd2))))
	    | rec_pick _ _ = raise Internal " Match: rec_pick."
       in rec_pick prog (fn newprog =>
	 		   (fn r => backchain a r newprog uvars subst sc))
       end

and backchain a r prog uvars subst sc =
      let fun rec_bc (Ratom(a1)) sc =
                unify a1 a (fn newsubst => sc newsubst prog false) subst
            | rec_bc (Rwith(r1,r2)) sc =
	        (rec_bc r1 sc; rec_bc r2 sc)
	    | rec_bc (Rlinimpl(g,r)) sc =
		rec_bc r (fn newsubst => (fn newprog => (fn newflag =>
               		    solve g newprog uvars newsubst 
		     		  (fn newsubst2 => (fn newprog2 => 
				     (fn newflag2 =>
					sc newsubst2 newprog2 
					   (newflag orelse newflag2)))))))
	    | rec_bc (Rall(x,r)) sc =
		rec_bc (rsubst (new_evar x uvars) x r) sc
	    | rec_bc (Rflex M) sc = 
	(case Terms_To_Props.term_to_rform subst M
             of Rflex(M1) => raise Illegal
			(": Unbound variable as resource or clause head.(" ^
			 makestring_term M ^ ").")
	      | r => rec_bc r sc)
       in rec_bc r sc end

and check false false prog1 prog2 subst sc = 
	if equalprog prog1 prog2
	  then sc subst prog1 false
	  else ()
  | check false true prog1 prog2 subst sc =
	if subcontext prog1 prog2
	  then sc subst prog1 false
	  else ()
  | check true false prog1 prog2 subst sc =
	if subcontext prog2 prog1
	  then sc subst prog2 false
	  else ()
  | check true true prog1 prog2 subst sc = 
	sc subst (context_intersection prog1 prog2) true
  | check flag1 flag2 prog1 prog2 subst sc = ()

and check2 false new_clauses_out prog_out subst sc =
	if thinable new_clauses_out
	  then sc subst prog_out false
   	  else ()
  | check2 true  new_clauses_out prog_out subst sc =
	sc subst prog_out true

and equalprog (Done) (Done) = true
  | equalprog (Dresource(_)) (Dresource(_)) = true
  | equalprog (Dbang(_)) (Dbang(_)) = true
  | equalprog (Dtensor(d1l,d1r)) (Dtensor(d2l,d2r)) = 
      (equalprog d1l d2l) andalso (equalprog d1r d2r)
  | equalprog _ _ = false

and subcontext (Done) (Done) = true
  | subcontext (Done) (Dresource(_)) = true
  | subcontext (Dresource(r1)) (Dresource(r2)) = (r1 = r2)
  | subcontext (Dbang(_)) (Dbang(_)) = true
  | subcontext (Dtensor(d1l,d1r)) (Dtensor(d2l,d2r)) = 
      (subcontext d1l d2l) andalso (subcontext d1r d2r)
  | subcontext _ _ = false

and context_intersection (Done) (Done) = (Done)
  | context_intersection (Done) (Dresource(r)) = (Done)
  | context_intersection (Dresource(r)) (Done) = (Done)
  | context_intersection (Dresource(r1)) (Dresource(r2)) = 
	if (r1 = r2) 
	then (Dresource(r1))
	else raise Illegal ": Mismatched resources in context_intersection."
  | context_intersection (Dbang(r1)) (Dbang(r2)) = 
        if (r1 = r2)
        then (Dbang(r1))
        else raise 
		Illegal ": Mismatched banged resource in context_intersection."
  | context_intersection (Dtensor(d1l,d1r)) (Dtensor(d2l,d2r)) =	
	(Dtensor(context_intersection d1l d2l, context_intersection d1r d2r))
  | context_intersection _ _ =
	raise Illegal ": Mismatched structures in context_intersection."

and thinable (Done) = true
  | thinable (Dresource(r)) = false
  | thinable (Dbang(r)) = true
  | thinable (Dtensor(d1,d2)) = (thinable d1) andalso (thinable d2)
  | thinable (Dflex M) = 
	raise Illegal(": Unbound variable for clause in thinable (" ^
		      makestring_term M ^ ").")



and execute_built_in (Appl (Const (Name "write"),t)) prog uvars subst sc =
        (print_term (!current_out_stream) (dereference t subst) ; 
	 flush_out (!current_out_stream)  ; 
         sc subst prog false) 
  | execute_built_in (Appl (Const (Name "write_clause"),t)) 
		     prog uvars subst sc =
      	(print_clause (!current_out_stream) (dereference t subst) ; 
	 flush_out (!current_out_stream) ; 
         sc subst prog false) 
  | execute_built_in (Appl (Const (Name "write_sans"),t)) prog uvars subst sc =
	((case (dereference t subst)
	    of (Const (String s)) => output(!current_out_stream, s)
	     | (Const (Name n)) => output(!current_out_stream, n)
	     | s => print_term (!current_out_stream) (dereference t subst)) ;
	 flush_out (!current_out_stream)  ; 
         sc subst prog false)
  | execute_built_in (Appl (Const (Name "write_raw"),t)) prog uvars subst sc =
      	(print_raw (!current_out_stream) (dereference t subst) ; 
	 flush_out (!current_out_stream) ; 
         sc subst prog false) 
  | execute_built_in (Const (Name "nl")) prog uvars subst sc =
        (output((!current_out_stream),"\n") ; sc subst prog false)
  | execute_built_in (Appl (Const (Name "read"),t)) prog uvars subst sc =
      let fun subnew nil nil t = t
           | subnew (evar::evars) (x::xs) t = 
           	  subnew evars xs (Terms.subst evar x t)
	   | subnew _ _ _ =
   		  raise Internal (" in read/subnew: lists of unequal length.")
	  val (varnames,s) = (Parse.stream_term_parse (!current_in_stream))
				 handle Parse.Parse_EOF => 
					(nil, Const (Name "end_of_file"))
          val xs = map Terms.Varbind varnames
          val evars = map (fn vname => Terms.new_evar vname nil) xs
      in unify (subnew evars xs s) t 
	       (fn newsubst => sc newsubst prog false) subst
      end
  | execute_built_in (Appl (Appl (Const (Name "telling"), fname), Goal))
                     prog uvars subst sc =
      (case (dereference fname subst) 
	of (Const (String filename)) =>
		( current_out_stream := open_out filename ;
		  solve (Terms_To_Props.term_to_gform subst Goal) 
			prog uvars subst
			(fn newsubst => fn newprog => fn newflag =>
				( current_out_stream := std_out ;
				  sc newsubst newprog newflag )) ;
		  current_out_stream := std_out )
	 | s as (Evar _) => raise Illegal 
				(": Filename in telling unbound (" ^
			 	 makestring_term s ^ ").")
	 | s 		 => raise Illegal 
				(": Filename in telling is not a string (" ^
			 	 makestring_term s ^ ")."))
  | execute_built_in (Appl (Appl (Const (Name "seeing"), fname), Goal)) 
                     prog uvars subst sc =
      (case (dereference fname subst) 
	of (Const (String filename)) =>
		( current_in_stream := open_in filename ;
		  solve (Terms_To_Props.term_to_gform subst Goal) 
			prog uvars subst
			(fn newsubst => fn newprog => fn newflag =>
				( current_in_stream := std_in ;
				  sc newsubst newprog newflag )) ;
		  current_in_stream := std_in )
	 | s as (Evar _) => raise Illegal 
				(": Filename in seeing unbound (" ^
			 	 makestring_term s ^ ").")
	 | s 		 => raise Illegal 
				(": Filename in seeing is not a string (" ^
			 	 makestring_term s ^ ")."))
  | execute_built_in (Appl (Appl (Const (Name "timing"), Goal), time))
		     prog uvars subst sc = 
	    let
	      open System.Timer
	      val start = start_timer ()
	    in
	      solve (Terms_To_Props.term_to_gform subst Goal) 
		    prog uvars subst
		    (fn newsubst => fn newprog => fn newflag =>
			let 
			  val non_gc_time = check_timer start
			  val gc_time = check_timer_gc start
			  val TIME{sec=s,usec=u} =
				 add_time(non_gc_time,gc_time)
			in
			  unify time (Const(Int (s * 1000000 + u)))
				(fn newsubst2 => sc newsubst2 newprog newflag)
				newsubst
			end)
	    end
  | execute_built_in (Appl (Appl (Const (Name "system"), cmd), result))
		     prog uvars subst sc =
	(case (dereference cmd subst)
	  of (Const (String command)) => 
		unify (Const (Int (System.system command))) result
		      (fn newsubst => sc newsubst prog false) subst
	   | s as (Evar _) => raise Illegal 
				(": command in system unbound (" ^
			 	 makestring_term s ^ ").")
	   | s 		 => raise Illegal 
				(": command in system is not a string (" ^
			 	 makestring_term s ^ ")."))
   | execute_built_in (Appl (Const (Name "cd"), dname)) prog uvars subst sc =
	(case (dereference dname subst)
	  of (Const (String dirname)) => 
		if (System.Directory.isDir dirname)
		  then (System.Directory.cd dirname ; sc subst prog false)
		  else raise Illegal (": Directory name in cd is invalid (" ^
			 		dirname ^ ").")
	   | s as (Evar _) => raise Illegal 
				(": Directory name in cd unbound (" ^
			 	 makestring_term s ^ ").")
	   | s 		 => raise Illegal 
				(": Directory name in cd is not a string (" ^
			 	 makestring_term s ^ ")."))
  | execute_built_in (Appl (Const (Name "var"),t)) prog uvars subst sc =
      	(case (dereference t subst)
	   of s as (Evar _) => sc subst prog false
	    | _ => ())
  | execute_built_in (Appl (Const (Name "nonvar"),t)) prog uvars subst sc =
      	(case (dereference t subst)
	   of s as (Evar _) => ()
	    | _ => sc subst prog false)
  | execute_built_in (Appl (Appl (Const (Name "generalize"), t), s)) 
                     prog uvars subst sc =
	unify (generalize t subst) s 
	      (fn newsubst => sc newsubst prog false) subst 
  | execute_built_in (Appl (Appl (Const (Name "explode"), str), lst)) 
                     prog uvars subst sc =
	(case (dereference str subst) 
	   of (Const (String s)) =>
		let val l = explode s
                    fun cvt nil      = (Const (Name "nil"))
                      | cvt (c::cs)  = (Appl (Appl (Const (Name "::"),
						   (Const (Name c))),
					     cvt cs))
		in unify (cvt l) lst 
			 (fn newsubst => sc newsubst prog false) subst 
		end
	    | s as (Evar _) =>
		(case (dereference lst subst)
		   of (l as Evar _) => raise Illegal 
			(": Both arguments to explode unbound (" ^
			 makestring_term s ^ "," ^ makestring_term l ^ ").")
		    | l =>
			let fun cvt (Const (Name "nil")) = ""
                      	      | cvt (Appl (Appl (Const (Name "::"),
						(Const (Name c))),cs)) =
			  		c ^ (cvt cs) 
		              | cvt _ = raise Illegal 
					(": 2nd argument to explode contains" ^
					 " a non-atomic constant (" ^
					 makestring_term l ^ ").")
			in unify (Const (String (cvt l))) s
		         	 (fn newsubst => sc newsubst prog false) subst 
			end)
	    | s => raise Illegal (": 1st argument to explode is not a string ("
			 	  ^ makestring_term s ^ ")."))
  | execute_built_in (Appl (Appl (Const (Name "explode_words"), str), lst)) 
                     prog uvars subst sc =
	(case (dereference str subst) 
	   of (Const (String s)) =>
		let fun explode_words nil "" = nil
		      | explode_words nil word = word::nil
		      | explode_words (" "::cs) "" = explode_words cs "" 
		      | explode_words ("\t"::cs) "" = explode_words cs "" 
		      | explode_words (" "::cs) word = 
			  word::(explode_words cs "")
		      | explode_words ("\t"::cs) word = 
			  word::(explode_words cs "")
		      | explode_words (c::cs) word = explode_words cs (word^c) 
		    val l = (explode_words (explode s) "")
                    fun cvt nil      = (Const (Name "nil"))
                      | cvt (w::ws)  = (Appl (Appl (Const (Name "::"),
						   (Const (Name w))),
					     cvt ws))
		in unify (cvt l) lst 
			 (fn newsubst => sc newsubst prog false) subst 
		end
	    | s as (Evar _) =>
		(case (dereference lst subst)
		   of (l as Evar _) => raise Illegal
			(": Both arguments to explode_words unbound (" ^
			 makestring_term s ^ "," ^ makestring_term l ^ ").")
		    | l =>
		let fun cvt (Const (Name "nil")) = ""
                      | cvt (Appl (Appl (Const (Name "::"),Const (Name w)),
				   Const (Name "nil"))) = w
                      | cvt (Appl (Appl (Const (Name "::"),Const (Name w)),
				   ws)) = w ^ " " ^ (cvt ws)
		      | cvt _ = raise Illegal 
				(": 2nd argument to explode_words contains" ^
			 	 " a non-atomic constant (" ^
				 makestring_term l ^ ").")
		in unify (Const (String (cvt l))) s
		         (fn newsubst => sc newsubst prog false) subst 
		end)
	    | s => raise Illegal (": 1st argument to explode_words is not a" ^
				  " string (" ^ makestring_term s ^ ")."))
  | execute_built_in (Appl (Appl (Const (Name "="), t1), t2)) 
		     prog uvars subst sc= 
                	unify t1 t2 (fn newsubst => sc newsubst prog false) 
			      subst
  | execute_built_in (Appl (Appl (Const (Name "is"), t), exp))
		     prog uvars subst sc = 
	let val result = (eval_exp (dereference exp subst))
			  handle Terms.Illegal(msg) =>
			    raise Illegal (": 2nd argument of `is' contains "
					   ^ msg)
	in unify t result (fn newsubst => sc newsubst prog false) subst
	end
  | execute_built_in (Appl (Appl (Const (Name "=:="), t1), t2)) 
		     prog uvars subst sc= 
	let val i1 = term_to_int(
			(eval_exp (dereference t1 subst))
			  handle Terms.Illegal(msg) =>
			    raise Illegal (": 1st argument of `=:=' contains "
					   ^ msg))
            val i2 = term_to_int(
			(eval_exp (dereference t2 subst))
			  handle Terms.Illegal(msg) =>
			    raise Illegal (": 2nd argument of `=:=' contains "
					   ^ msg))
	in if i1 = i2 
	     then sc subst prog false
   	     else ()
	end
  | execute_built_in (Appl (Appl (Const (Name "=\\="), t1), t2)) 
		     prog uvars subst sc= 
	let val i1 = term_to_int(
			(eval_exp (dereference t1 subst))
			  handle Terms.Illegal(msg) =>
			    raise Illegal (": 1st argument of `=\\=' contains "
					   ^ msg))
            val i2 = term_to_int(
			(eval_exp (dereference t2 subst))
			  handle Terms.Illegal(msg) =>
			    raise Illegal (": 2nd argument of `=\\=' contains "
					   ^ msg))
	in if i1 <> i2 
	     then sc subst prog false
   	     else ()
	end
  | execute_built_in (Appl (Appl (Const (Name ">="), t1), t2)) 
		     prog uvars subst sc= 
	let val i1 = term_to_int(
			(eval_exp (dereference t1 subst))
			  handle Terms.Illegal(msg) =>
			    raise Illegal (": 1st argument of `>=' contains "
					   ^ msg))
            val i2 = term_to_int(
			(eval_exp (dereference t2 subst))
			  handle Terms.Illegal(msg) =>
			    raise Illegal (": 2nd argument of `>=' contains "
					   ^ msg))
	in if i1 >= i2 
	     then sc subst prog false
   	     else ()
	end
  | execute_built_in (Appl (Appl (Const (Name "=<"), t1), t2)) 
		     prog uvars subst sc= 
	let val i1 = term_to_int(
			(eval_exp (dereference t1 subst))
			  handle Terms.Illegal(msg) =>
			    raise Illegal (": 1st argument of `=<' contains "
					   ^ msg))
            val i2 = term_to_int(
			(eval_exp (dereference t2 subst))
			  handle Terms.Illegal(msg) =>
			    raise Illegal (": 2nd argument of `=<' contains "
					   ^ msg))
	in if i1 <= i2 
	     then sc subst prog false
   	     else ()
	end
  | execute_built_in (Appl (Appl (Const (Name ">"), t1), t2)) 
		     prog uvars subst sc= 
	let val i1 = term_to_int(
			(eval_exp (dereference t1 subst))
			  handle Terms.Illegal(msg) =>
			    raise Illegal (": 1st argument of `>' contains "
					   ^ msg))
            val i2 = term_to_int(
			(eval_exp (dereference t2 subst))
			  handle Terms.Illegal(msg) =>
			    raise Illegal (": 2nd argument of `>' contains "
					   ^ msg))
	in if i1 > i2 
	     then sc subst prog false
   	     else ()
	end
  | execute_built_in (Appl (Appl (Const (Name "<"), t1), t2)) 
		     prog uvars subst sc= 
	let val i1 = term_to_int(
			(eval_exp (dereference t1 subst))
			  handle Terms.Illegal(msg) =>
			    raise Illegal (": 1st argument of `<' contains "
					   ^ msg))
            val i2 = term_to_int(
			(eval_exp (dereference t2 subst))
			  handle Terms.Illegal(msg) =>
			    raise Illegal (": 2nd argument of `<' contains "
					   ^ msg))
	in if i1 < i2 
	     then sc subst prog false
   	     else ()
	end
  | execute_built_in (Appl (Const (Name "load"),t))
		     prog uvars subst sc =
		(print ("loading " ^ makestring_term t ^ "...\n") ;
		 solve (Glinload(t,Gatom(Const (Name "top"))))
     		       prog uvars subst sc )
  | execute_built_in (Const (Name "top")) prog uvars subst sc =
      (top_level "?- " prog uvars subst
       handle POP => (print "Returning to previous top level...\n" ;
		      raise POPAUX))
  | execute_built_in (Const (Name "fail")) prog uvars subst sc = ()
  | execute_built_in (Const (Name "pop")) prog uvars subst sc = raise POP
  | execute_built_in (Const (Name "popall")) prog uvars subst sc = raise POPALL
  | execute_built_in (Const (Name "abort")) prog uvars subst sc = raise ABORT
  | execute_built_in (Const (Name "exit")) prog uvars subst sc = raise EXIT
  | execute_built_in (Const (Name "bye")) prog uvars subst sc = raise EXIT
  | execute_built_in a prog uvars subst sc =
	 raise Illegal (": Built in predicate " ^ func_symbol_of a 
		  	^ " called with the wrong number of arguments ("
			^ makestring_term a ^ ").")


and catch_errors func =
    	func ()
	   handle ABORT  => raise ABORT
		| POP 	 => raise POP
		| POPAUX => raise POPAUX
		| POPALL => raise POPALL
		| EXIT   => raise EXIT
		| Parse.Parse_EOF => raise POP 
		| Parse.Parse_Error (msg) => print(msg ^ "\n")
		| Io (msg) => print("I/O Error: " ^ msg ^ "\n")
		| Illegal (msg) => 
			print("Lolli Error" ^ msg ^ "\n")
		| Internal (msg) => 
			print("Internal Error" ^ msg ^ "\n")
	        | Terms.Illegal(msg) => 
			print("Lolli Error" ^ msg ^ "\n")
	        | Terms.Internal(msg) => 
			print("Internal Error" ^ msg ^ "\n")
		| Terms_To_Props.Illegal (msg) => 
			print("Lolli Error" ^ msg ^ "\n")
		| Terms_To_Props.Internal (msg) => 
			print("Internal Error" ^ msg ^ "\n")
		| exn => print("Urecognized Exception Error: " 
			 ^ (System.exn_name exn) ^ "\n")

and handle_interrupt (infiniteLoop : unit -> unit) =
  let val oldHandler = System.Signals.inqHandler(System.Signals.SIGINT)
  in ( callcc (fn k =>
	 ( System.Signals.setHandler(System.Signals.SIGINT,SOME(fn _ => k)) ;
	   infiniteLoop () ;
	   raise UnexpectedReturn )) ;
       print ("\nInterrupted...\n") ;
       infiniteLoop () ;
       raise UnexpectedReturn )
     handle exn => (System.Signals.setHandler(System.Signals.SIGINT, 
					       oldHandler) ;
		     raise exn )
 end

and top_level (promptstr:string) prog uvars subst =
     let exception Query_Complete
	 fun read_eval () = 
	       let val (evars,g) = query_to_goal 
                                     (Parse.stream_query_parse std_in)
		   fun initial_sc newsubst = fn newprog => fn newflag =>
			let val ps = Terms.project_substitution evars newsubst
			in
		          ( if ((evars = nil) orelse 
				(is_empty_substitution ps))
			      then print "solved"
			      else Terms.print_substitution ps ;
			    if more_solutions ()
			      then ()  (* This backtracks *)
			      else raise Query_Complete )
			end
	        in ( solve (Glinimpl(prog,g)) Done uvars
		           subst initial_sc;
		     print "no\n" ) 
		   handle Query_Complete => print "yes\n"
                        | ABORT => print"\naborted...\n"
			| POPAUX => ()
  	        end
	 fun prompt () = ( print promptstr ; flush_out std_out )
	 fun loop () = ( prompt () ; catch_errors(read_eval) ; loop () )
      in handle_interrupt(loop) end

and more_solutions () =
       (ord (input_line std_in) = ord ";") handle Ord => false

and ll_outer_level prog uvars =
	 ((top_level "?- " prog uvars Terms.empty_substitution 
	     handle POP => (print ("You are now at the top level. " ^ 
				     "Use 'bye' to leave Lolli.\n") ;
			    ll_outer_level prog uvars))
	     handle POPALL => (print "Returning to topmost level.\n" ;
			       ll_outer_level prog uvars))
	     handle EXIT => (print "Closing Lolli. \n"; ())

and ll_file filename = print "Starting with a file loaded not currently supported.\n Use --o from within the system.\n"

and ll () = ( System.Control.Print.signatures := 0 ;
	      System.Control.Print.printDepth := 15 ;
	      System.Control.Runtime.gcmessages := 0 ;
	      print ("Starting Lolli version " ^ ll_version ^ 
		     "\n  (built with " ^ System.version ^ ")...\n") ;
	      ll_outer_level Done nil)


(* comment this out if not building c code *)

(*
val _ = ll();
*)

end  (* functor Interpreter *)




