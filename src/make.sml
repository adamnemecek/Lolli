use "./interpreter/terms.sml";
use "./interpreter/propositions.sml";
use "./interpreter/terms_to_props.sml";

use "./parser/base.sml";
use "./parser/absyn.sig";
use "./parser/absyn.sml";
use "./parser/fol.grm.sig";
use "./parser/fol.grm.sml";
use "./parser/interface.sml";
use "./parser/fol.lex.sml";
use "./parser/parse.sml";

use "./interpreter/interpreter.sml";
use "./link.sml";

fun export_ll () = 
  let fun aux (callname::filename::nil,environment) =
            Interpreter.ll_file filename
        | aux (callname::nil,environment) = Interpreter.ll ()
        | aux (callname::_,environment) = 
            print ("usage: " ^ callname ^ " [filename]\n")
  in exportFn("lolli",aux) end;
	    
export_ll();
