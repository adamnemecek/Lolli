
functor FolLrValsFun (structure Token : TOKEN
			       structure Absyn : ABSYN) : Fol_LRVALS = 
struct
structure ParserData=
struct
structure Header = 
struct
structure Absyn = Absyn
open Absyn

end
structure LrTable = Token.LrTable
structure Token = Token
local open LrTable in 
val table=let val actionRows =
"\
\\001\000\001\000\000\000\002\000\000\000\000\000\
\\001\000\002\000\077\000\000\000\
\\001\000\002\000\082\000\007\000\040\000\008\000\039\000\009\000\038\000\
\\016\000\037\000\017\000\036\000\018\000\035\000\019\000\034\000\
\\020\000\033\000\021\000\032\000\022\000\031\000\036\000\030\000\
\\037\000\029\000\038\000\028\000\000\000\
\\001\000\002\000\085\000\000\000\
\\001\000\002\000\087\000\007\000\040\000\008\000\039\000\009\000\038\000\
\\016\000\037\000\017\000\036\000\018\000\035\000\019\000\034\000\
\\020\000\033\000\021\000\032\000\022\000\031\000\036\000\030\000\
\\037\000\029\000\038\000\028\000\000\000\
\\001\000\003\000\075\000\010\000\022\000\012\000\021\000\014\000\020\000\
\\024\000\019\000\025\000\018\000\026\000\017\000\027\000\016\000\
\\028\000\015\000\032\000\014\000\033\000\013\000\034\000\012\000\
\\035\000\011\000\000\000\
\\001\000\005\000\027\000\000\000\
\\001\000\006\000\068\000\000\000\
\\001\000\007\000\040\000\008\000\039\000\009\000\038\000\011\000\071\000\
\\016\000\037\000\017\000\036\000\018\000\035\000\019\000\034\000\
\\020\000\033\000\021\000\032\000\022\000\031\000\036\000\030\000\
\\037\000\029\000\038\000\028\000\000\000\
\\001\000\007\000\040\000\008\000\039\000\009\000\038\000\013\000\070\000\
\\016\000\037\000\017\000\036\000\018\000\035\000\019\000\034\000\
\\020\000\033\000\021\000\032\000\022\000\031\000\036\000\030\000\
\\037\000\029\000\038\000\028\000\000\000\
\\001\000\007\000\040\000\008\000\039\000\009\000\038\000\015\000\069\000\
\\016\000\037\000\017\000\036\000\018\000\035\000\019\000\034\000\
\\020\000\033\000\021\000\032\000\022\000\031\000\036\000\030\000\
\\037\000\029\000\038\000\028\000\000\000\
\\001\000\007\000\040\000\008\000\039\000\009\000\038\000\016\000\037\000\
\\017\000\036\000\018\000\035\000\019\000\034\000\020\000\033\000\
\\021\000\032\000\022\000\031\000\023\000\080\000\036\000\030\000\
\\037\000\029\000\038\000\028\000\000\000\
\\001\000\010\000\022\000\012\000\021\000\014\000\020\000\024\000\019\000\
\\025\000\018\000\026\000\017\000\027\000\016\000\028\000\015\000\
\\032\000\014\000\033\000\013\000\034\000\012\000\035\000\011\000\000\000\
\\001\000\029\000\005\000\030\000\004\000\031\000\003\000\000\000\
\\001\000\032\000\045\000\033\000\044\000\000\000\
\\001\000\032\000\054\000\033\000\053\000\000\000\
\\090\000\000\000\
\\091\000\000\000\
\\092\000\000\000\
\\093\000\000\000\
\\094\000\000\000\
\\095\000\004\000\051\000\000\000\
\\096\000\000\000\
\\097\000\032\000\054\000\033\000\053\000\000\000\
\\098\000\032\000\054\000\033\000\053\000\000\000\
\\099\000\000\000\
\\100\000\000\000\
\\101\000\003\000\075\000\010\000\022\000\012\000\021\000\014\000\020\000\
\\024\000\019\000\025\000\018\000\026\000\017\000\027\000\016\000\
\\028\000\015\000\032\000\014\000\033\000\013\000\034\000\012\000\
\\035\000\011\000\000\000\
\\102\000\000\000\
\\103\000\000\000\
\\104\000\000\000\
\\105\000\007\000\040\000\008\000\039\000\009\000\038\000\016\000\037\000\
\\017\000\036\000\018\000\035\000\019\000\034\000\020\000\033\000\
\\021\000\032\000\022\000\031\000\036\000\030\000\037\000\029\000\
\\038\000\028\000\000\000\
\\106\000\007\000\040\000\008\000\039\000\009\000\038\000\016\000\037\000\
\\017\000\036\000\018\000\035\000\019\000\034\000\020\000\033\000\
\\021\000\032\000\022\000\031\000\036\000\030\000\037\000\029\000\
\\038\000\028\000\000\000\
\\107\000\007\000\040\000\018\000\035\000\020\000\033\000\021\000\032\000\
\\022\000\031\000\036\000\030\000\037\000\029\000\038\000\028\000\000\000\
\\108\000\007\000\040\000\009\000\038\000\018\000\035\000\020\000\033\000\
\\021\000\032\000\022\000\031\000\036\000\030\000\037\000\029\000\
\\038\000\028\000\000\000\
\\109\000\007\000\040\000\008\000\039\000\009\000\038\000\018\000\035\000\
\\020\000\033\000\021\000\032\000\022\000\031\000\036\000\030\000\
\\037\000\029\000\038\000\028\000\000\000\
\\110\000\018\000\035\000\020\000\033\000\021\000\032\000\022\000\031\000\
\\036\000\030\000\037\000\029\000\038\000\028\000\000\000\
\\111\000\007\000\040\000\008\000\039\000\009\000\038\000\018\000\035\000\
\\020\000\033\000\021\000\032\000\022\000\031\000\036\000\030\000\
\\037\000\029\000\038\000\028\000\000\000\
\\112\000\018\000\035\000\020\000\033\000\021\000\032\000\022\000\031\000\
\\036\000\030\000\037\000\029\000\038\000\028\000\000\000\
\\113\000\007\000\040\000\008\000\039\000\009\000\038\000\018\000\035\000\
\\020\000\033\000\021\000\032\000\022\000\031\000\036\000\030\000\
\\037\000\029\000\038\000\028\000\000\000\
\\114\000\020\000\033\000\022\000\031\000\036\000\030\000\037\000\029\000\
\\038\000\028\000\000\000\
\\115\000\007\000\040\000\008\000\039\000\009\000\038\000\018\000\035\000\
\\020\000\033\000\021\000\032\000\022\000\031\000\036\000\030\000\
\\037\000\029\000\038\000\028\000\000\000\
\\116\000\036\000\030\000\037\000\029\000\038\000\028\000\000\000\
\\117\000\000\000\
\\118\000\000\000\
\\119\000\000\000\
\\120\000\000\000\
\\121\000\037\000\029\000\038\000\028\000\000\000\
\\122\000\038\000\028\000\000\000\
\\123\000\038\000\028\000\000\000\
\\124\000\010\000\022\000\024\000\019\000\025\000\018\000\028\000\015\000\
\\032\000\014\000\033\000\013\000\034\000\012\000\035\000\011\000\000\000\
\\125\000\000\000\
\\126\000\000\000\
\\127\000\000\000\
\\128\000\000\000\
\\129\000\000\000\
\\130\000\000\000\
\\131\000\000\000\
\\132\000\000\000\
\\133\000\000\000\
\\134\000\000\000\
\\135\000\000\000\
\\136\000\007\000\040\000\008\000\039\000\009\000\038\000\016\000\037\000\
\\017\000\036\000\018\000\035\000\019\000\034\000\020\000\033\000\
\\021\000\032\000\022\000\031\000\036\000\030\000\037\000\029\000\
\\038\000\028\000\000\000\
\\137\000\000\000\
\\138\000\000\000\
\"
val actionRowNumbers =
"\013\000\012\000\012\000\006\000\
\\056\000\032\000\050\000\051\000\
\\018\000\058\000\057\000\061\000\
\\060\000\055\000\014\000\014\000\
\\054\000\053\000\012\000\012\000\
\\012\000\031\000\017\000\021\000\
\\016\000\015\000\012\000\012\000\
\\012\000\012\000\012\000\012\000\
\\012\000\012\000\012\000\012\000\
\\012\000\012\000\012\000\052\000\
\\007\000\046\000\064\000\063\000\
\\045\000\010\000\009\000\008\000\
\\005\000\015\000\001\000\024\000\
\\023\000\049\000\048\000\047\000\
\\040\000\038\000\011\000\041\000\
\\036\000\039\000\037\000\034\000\
\\035\000\033\000\012\000\044\000\
\\043\000\059\000\002\000\027\000\
\\019\000\012\000\003\000\020\000\
\\026\000\025\000\012\000\062\000\
\\029\000\028\000\004\000\021\000\
\\042\000\030\000\022\000\000\000"
val gotoT =
"\
\\001\000\087\000\000\000\
\\009\000\008\000\010\000\007\000\011\000\006\000\012\000\005\000\
\\015\000\004\000\000\000\
\\008\000\022\000\010\000\007\000\011\000\006\000\012\000\021\000\
\\015\000\004\000\000\000\
\\002\000\024\000\003\000\023\000\000\000\
\\000\000\
\\000\000\
\\010\000\039\000\015\000\004\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\013\000\041\000\014\000\040\000\000\000\
\\013\000\044\000\014\000\040\000\000\000\
\\000\000\
\\000\000\
\\010\000\007\000\011\000\006\000\012\000\045\000\015\000\004\000\000\000\
\\010\000\007\000\011\000\006\000\012\000\046\000\015\000\004\000\000\000\
\\010\000\007\000\011\000\006\000\012\000\047\000\015\000\004\000\000\000\
\\000\000\
\\000\000\
\\004\000\048\000\000\000\
\\000\000\
\\005\000\050\000\000\000\
\\010\000\007\000\011\000\006\000\012\000\053\000\015\000\004\000\000\000\
\\010\000\007\000\011\000\006\000\012\000\054\000\015\000\004\000\000\000\
\\010\000\007\000\011\000\006\000\012\000\055\000\015\000\004\000\000\000\
\\010\000\007\000\011\000\006\000\012\000\056\000\015\000\004\000\000\000\
\\010\000\007\000\011\000\006\000\012\000\057\000\015\000\004\000\000\000\
\\010\000\007\000\011\000\006\000\012\000\058\000\015\000\004\000\000\000\
\\010\000\007\000\011\000\006\000\012\000\059\000\015\000\004\000\000\000\
\\010\000\007\000\011\000\006\000\012\000\060\000\015\000\004\000\000\000\
\\010\000\007\000\011\000\006\000\012\000\061\000\015\000\004\000\000\000\
\\010\000\007\000\011\000\006\000\012\000\062\000\015\000\004\000\000\000\
\\010\000\007\000\011\000\006\000\012\000\063\000\015\000\004\000\000\000\
\\010\000\007\000\011\000\006\000\012\000\064\000\015\000\004\000\000\000\
\\010\000\007\000\011\000\006\000\012\000\065\000\015\000\004\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\006\000\072\000\007\000\071\000\010\000\007\000\011\000\006\000\
\\012\000\070\000\015\000\004\000\000\000\
\\005\000\074\000\000\000\
\\000\000\
\\005\000\076\000\000\000\
\\005\000\077\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\010\000\007\000\011\000\006\000\012\000\079\000\015\000\004\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\006\000\081\000\007\000\071\000\010\000\007\000\011\000\006\000\
\\012\000\070\000\015\000\004\000\000\000\
\\000\000\
\\010\000\007\000\011\000\006\000\012\000\082\000\015\000\004\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\010\000\007\000\011\000\006\000\012\000\084\000\015\000\004\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\004\000\086\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\"
val numstates = 88
val numrules = 49
val s = ref "" and index = ref 0
val string_to_int = fn () => 
let val i = !index
in index := i+2; ordof(!s,i) + ordof(!s,i+1) * 256
end
val string_to_list = fn s' =>
    let val len = String.length s'
        fun f () =
           if !index < len then string_to_int() :: f()
           else nil
   in index := 0; s := s'; f ()
   end
val string_to_pairlist = fn (conv_key,conv_entry) =>
     let fun f () =
         case string_to_int()
         of 0 => EMPTY
          | n => PAIR(conv_key (n-1),conv_entry (string_to_int()),f())
     in f
     end
val string_to_pairlist_default = fn (conv_key,conv_entry) =>
    let val conv_row = string_to_pairlist(conv_key,conv_entry)
    in fn () =>
       let val default = conv_entry(string_to_int())
           val row = conv_row()
       in (row,default)
       end
   end
val string_to_table = fn (convert_row,s') =>
    let val len = String.length s'
 	 fun f ()=
	    if !index < len then convert_row() :: f()
	    else nil
     in (s := s'; index := 0; f ())
     end
local
  val memo = Array.array(numstates+numrules,ERROR)
  val _ =let fun g i=(Array.update(memo,i,REDUCE(i-numstates)); g(i+1))
	fun f i =
	     if i=numstates then g i
	     else (Array.update(memo,i,SHIFT (STATE i)); f (i+1))
	   in f 0 handle Subscript => ()
	   end
in
val entry_to_action = fn 0 => ACCEPT | 1 => ERROR | j => Array.sub(memo,(j-2))
end
val gotoT=Array.arrayoflist(string_to_table(string_to_pairlist(NT,STATE),gotoT))
val actionRows=string_to_table(string_to_pairlist_default(T,entry_to_action),actionRows)
val actionRowNumbers = string_to_list actionRowNumbers
val actionT = let val actionRowLookUp=
let val a=Array.arrayoflist(actionRows) in fn i=>Array.sub(a,i) end
in Array.arrayoflist(map actionRowLookUp actionRowNumbers)
end
in LrTable.mkLrTable {actions=actionT,gotos=gotoT,numRules=numrules,
numStates=numstates,initialState=STATE 0}
end
end
local open Header in
type pos = int
type arg = unit
structure MlyValue = 
struct
datatype svalue = VOID | ntVOID of unit | RIGHTINFIXOP of  (string)
 | LEFTINFIXOP of  (string) | INFIXOP of  (string)
 | STRING of  (string) | INT of  (int) | UCID of  (string)
 | LCID of  (string) | id of  (Absyn.aterm)
 | bdvar of  (Absyn.avarbind) | lamterm of  (Absyn.aterm)
 | term of  (Absyn.aterm) | appl of  (Absyn.aterm)
 | atom of  (Absyn.aterm) | readterm of  (string list*Terms.term)
 | query of  (string list*Terms.term) | clause of  (Absyn.aterm)
 | clauselist of  (Absyn.aterm list) | idlist of  (string list)
 | locallist of  (string list) | moddecl of  (string list)
 | module of  (string*string list*string list* ( string list * Terms.term )  list)
 | start of  (Absyn.parse_result)
end
type svalue = MlyValue.svalue
type result = Absyn.parse_result
end
structure EC=
struct
open LrTable
val is_keyword =
fn _ => false
val preferred_insert =
fn (T 1) => true | _ => false
val preferred_subst =
fn  _ => nil
val noShift = 
fn (T 0) => true | _ => false
val showTerminal =
fn (T 0) => "EOF"
  | (T 1) => "DOT"
  | (T 2) => "LINEAR"
  | (T 3) => "LOCAL"
  | (T 4) => "MODULE"
  | (T 5) => "BACKSLASH"
  | (T 6) => "COMMA"
  | (T 7) => "SEMICOLON"
  | (T 8) => "AMPERSAND"
  | (T 9) => "LPAREN"
  | (T 10) => "RPAREN"
  | (T 11) => "LCURLY"
  | (T 12) => "RCURLY"
  | (T 13) => "LBRACKET"
  | (T 14) => "RBRACKET"
  | (T 15) => "BACKDOUBLE"
  | (T 16) => "BACKLOLLI"
  | (T 17) => "DOUBLEARROW"
  | (T 18) => "DCGARROW"
  | (T 19) => "ARROW"
  | (T 20) => "LOLLIPOP"
  | (T 21) => "LOADLOLLI"
  | (T 22) => "BAR"
  | (T 23) => "TRUE"
  | (T 24) => "ONE"
  | (T 25) => "FORALL"
  | (T 26) => "EXISTS"
  | (T 27) => "EXCL"
  | (T 28) => "PARSEMODULE"
  | (T 29) => "PARSEQUERY"
  | (T 30) => "PARSETERM"
  | (T 31) => "LCID"
  | (T 32) => "UCID"
  | (T 33) => "INT"
  | (T 34) => "STRING"
  | (T 35) => "INFIXOP"
  | (T 36) => "LEFTINFIXOP"
  | (T 37) => "RIGHTINFIXOP"
  | _ => "bogus-term"
val errtermvalue=
let open Header in
fn _ => MlyValue.VOID
end
val terms = (T 0) :: (T 1) :: (T 2) :: (T 3) :: (T 4) :: (T 5) :: (T 6
) :: (T 7) :: (T 8) :: (T 9) :: (T 10) :: (T 11) :: (T 12) :: (T 13)
 :: (T 14) :: (T 15) :: (T 16) :: (T 17) :: (T 18) :: (T 19) :: (T 20)
 :: (T 21) :: (T 22) :: (T 23) :: (T 24) :: (T 25) :: (T 26) :: (T 27)
 :: (T 28) :: (T 29) :: (T 30) :: nil
end
structure Actions =
struct 
exception mlyAction of int
val actions = 
let open Header
in
fn (i392,defaultPos,stack,
    (()):arg) =>
case (i392,stack)
of (0,(_,(MlyValue.module module,_,module1right))::(_,(_,
PARSEMODULE1left,_))::rest671) => let val result=MlyValue.start((
Parsed_Module(module)))
 in (LrTable.NT 0,(result,PARSEMODULE1left,module1right),rest671) end
| (1,(_,(MlyValue.query query,_,query1right))::(_,(_,PARSEQUERY1left,_
))::rest671) => let val result=MlyValue.start((Parsed_Query(query)))
 in (LrTable.NT 0,(result,PARSEQUERY1left,query1right),rest671) end
| (2,(_,(MlyValue.readterm readterm,_,readterm1right))::(_,(_,
PARSETERM1left,_))::rest671) => let val result=MlyValue.start((
Parsed_Term(readterm)))
 in (LrTable.NT 0,(result,PARSETERM1left,readterm1right),rest671) end
| (3,(_,(MlyValue.clauselist clauselist,_,clauselist1right))::(_,(
MlyValue.locallist locallist,_,_))::(_,(MlyValue.moddecl moddecl,
moddecl1left,_))::rest671) => let val result=MlyValue.module((
close_module(moddecl,locallist,clauselist)))
 in (LrTable.NT 1,(result,moddecl1left,clauselist1right),rest671) end
| (4,(_,(_,_,DOT1right))::(_,(MlyValue.idlist idlist,_,_))::(_,(_,
MODULE1left,_))::rest671) => let val result=MlyValue.moddecl((idlist))
 in (LrTable.NT 2,(result,MODULE1left,DOT1right),rest671) end
| (5,rest671) => let val result=MlyValue.locallist((nil))
 in (LrTable.NT 3,(result,defaultPos,defaultPos),rest671) end
| (6,(_,(MlyValue.locallist locallist,_,locallist1right))::_::(_,(
MlyValue.idlist idlist,_,_))::(_,(_,LOCAL1left,_))::rest671) => let 
val result=MlyValue.locallist((idlist @ locallist))
 in (LrTable.NT 3,(result,LOCAL1left,locallist1right),rest671) end
| (7,(_,(MlyValue.LCID LCID,LCID1left,LCID1right))::rest671) => let 
val result=MlyValue.idlist((LCID::nil))
 in (LrTable.NT 4,(result,LCID1left,LCID1right),rest671) end
| (8,(_,(MlyValue.UCID UCID,UCID1left,UCID1right))::rest671) => let 
val result=MlyValue.idlist((UCID::nil))
 in (LrTable.NT 4,(result,UCID1left,UCID1right),rest671) end
| (9,(_,(MlyValue.idlist idlist,_,idlist1right))::(_,(MlyValue.LCID 
LCID,LCID1left,_))::rest671) => let val result=MlyValue.idlist((
LCID::idlist))
 in (LrTable.NT 4,(result,LCID1left,idlist1right),rest671) end
| (10,(_,(MlyValue.idlist idlist,_,idlist1right))::(_,(MlyValue.UCID 
UCID,UCID1left,_))::rest671) => let val result=MlyValue.idlist((
UCID::idlist))
 in (LrTable.NT 4,(result,UCID1left,idlist1right),rest671) end
| (11,(_,(MlyValue.clause clause,clause1left,clause1right))::rest671)
 => let val result=MlyValue.clauselist((clause::nil))
 in (LrTable.NT 5,(result,clause1left,clause1right),rest671) end
| (12,(_,(MlyValue.clauselist clauselist,_,clauselist1right))::(_,(
MlyValue.clause clause,clause1left,_))::rest671) => let val result=
MlyValue.clauselist((clause::clauselist))
 in (LrTable.NT 5,(result,clause1left,clauselist1right),rest671) end
| (13,(_,(_,_,DOT1right))::(_,(MlyValue.term term,term1left,_))::
rest671) => let val result=MlyValue.clause((mk_unop ("bang",term)))
 in (LrTable.NT 6,(result,term1left,DOT1right),rest671) end
| (14,(_,(_,_,DOT1right))::(_,(MlyValue.term term,_,_))::(_,(_,
LINEAR1left,_))::rest671) => let val result=MlyValue.clause((term))
 in (LrTable.NT 6,(result,LINEAR1left,DOT1right),rest671) end
| (15,(_,(MlyValue.term term,term1left,term1right))::rest671) => let 
val result=MlyValue.query((close_term(term)))
 in (LrTable.NT 7,(result,term1left,term1right),rest671) end
| (16,(_,(MlyValue.term term,term1left,term1right))::rest671) => let 
val result=MlyValue.readterm((close_term(term)))
 in (LrTable.NT 8,(result,term1left,term1right),rest671) end
| (17,(_,(MlyValue.term term2,_,term2right))::_::(_,(MlyValue.term 
term1,term1left,_))::rest671) => let val result=MlyValue.term((
mk_binop (",",term1,term2)))
 in (LrTable.NT 11,(result,term1left,term2right),rest671) end
| (18,(_,(MlyValue.term term2,_,term2right))::_::(_,(MlyValue.term 
term1,term1left,_))::rest671) => let val result=MlyValue.term((
mk_binop ("&",term1,term2)))
 in (LrTable.NT 11,(result,term1left,term2right),rest671) end
| (19,(_,(MlyValue.term term2,_,term2right))::_::(_,(MlyValue.term 
term1,term1left,_))::rest671) => let val result=MlyValue.term((
mk_binop (";",term1,term2)))
 in (LrTable.NT 11,(result,term1left,term2right),rest671) end
| (20,(_,(MlyValue.term term2,_,term2right))::_::(_,(MlyValue.term 
term1,term1left,_))::rest671) => let val result=MlyValue.term((
mk_binop ("=>",term1,term2)))
 in (LrTable.NT 11,(result,term1left,term2right),rest671) end
| (21,(_,(MlyValue.term term2,_,term2right))::_::(_,(MlyValue.term 
term1,term1left,_))::rest671) => let val result=MlyValue.term((
mk_binop ("=>",term2,term1)))
 in (LrTable.NT 11,(result,term1left,term2right),rest671) end
| (22,(_,(MlyValue.term term2,_,term2right))::_::(_,(MlyValue.term 
term1,term1left,_))::rest671) => let val result=MlyValue.term((
mk_binop ("-o",term1,term2)))
 in (LrTable.NT 11,(result,term1left,term2right),rest671) end
| (23,(_,(MlyValue.term term2,_,term2right))::_::(_,(MlyValue.term 
term1,term1left,_))::rest671) => let val result=MlyValue.term((
mk_binop ("-o",term2,term1)))
 in (LrTable.NT 11,(result,term1left,term2right),rest671) end
| (24,(_,(MlyValue.term term2,_,term2right))::_::(_,(MlyValue.term 
term1,term1left,_))::rest671) => let val result=MlyValue.term((
mk_binop ("--o",term1,term2)))
 in (LrTable.NT 11,(result,term1left,term2right),rest671) end
| (25,(_,(MlyValue.term term2,_,term2right))::_::(_,(MlyValue.term 
term1,term1left,_))::rest671) => let val result=MlyValue.term((
mk_binop ("-->",term2,term1)))
 in (LrTable.NT 11,(result,term1left,term2right),rest671) end
| (26,(_,(MlyValue.term term3,_,term3right))::_::(_,(MlyValue.term 
term2,_,_))::_::(_,(MlyValue.term term1,term1left,_))::rest671) => 
let val result=MlyValue.term((mk_ternop("guard",term1,term2,term3)))
 in (LrTable.NT 11,(result,term1left,term3right),rest671) end
| (27,(_,(_,_,RCURLY1right))::(_,(MlyValue.term term,_,_))::(_,(_,
LCURLY1left,_))::rest671) => let val result=MlyValue.term((
mk_unop ("bang",term)))
 in (LrTable.NT 11,(result,LCURLY1left,RCURLY1right),rest671) end
| (28,(_,(_,_,RBRACKET1right))::(_,(MlyValue.term term,_,_))::(_,(_,
LBRACKET1left,_))::rest671) => let val result=MlyValue.term((
mk_unop ("dcgcodebracket",term)))
 in (LrTable.NT 11,(result,LBRACKET1left,RBRACKET1right),rest671) end
| (29,(_,(MlyValue.lamterm lamterm,_,lamterm1right))::(_,(_,
FORALL1left,_))::rest671) => let val result=MlyValue.term((
mk_quant ("forall",lamterm)))
 in (LrTable.NT 11,(result,FORALL1left,lamterm1right),rest671) end
| (30,(_,(MlyValue.lamterm lamterm,_,lamterm1right))::(_,(_,
EXISTS1left,_))::rest671) => let val result=MlyValue.term((
mk_quant ("exists",lamterm)))
 in (LrTable.NT 11,(result,EXISTS1left,lamterm1right),rest671) end
| (31,(_,(MlyValue.term term2,_,term2right))::(_,(MlyValue.INFIXOP 
INFIXOP,_,_))::(_,(MlyValue.term term1,term1left,_))::rest671) => let 
val result=MlyValue.term((mk_binop (INFIXOP,term1,term2)))
 in (LrTable.NT 11,(result,term1left,term2right),rest671) end
| (32,(_,(MlyValue.term term2,_,term2right))::(_,(MlyValue.LEFTINFIXOP
 LEFTINFIXOP,_,_))::(_,(MlyValue.term term1,term1left,_))::rest671)
 => let val result=MlyValue.term((mk_binop (LEFTINFIXOP,term1,term2)))
 in (LrTable.NT 11,(result,term1left,term2right),rest671) end
| (33,(_,(MlyValue.term term2,_,term2right))::(_,(
MlyValue.RIGHTINFIXOP RIGHTINFIXOP,_,_))::(_,(MlyValue.term term1,
term1left,_))::rest671) => let val result=MlyValue.term((
mk_binop (RIGHTINFIXOP,term1,term2)))
 in (LrTable.NT 11,(result,term1left,term2right),rest671) end
| (34,(_,(MlyValue.appl appl,appl1left,appl1right))::rest671) => let 
val result=MlyValue.term((appl))
 in (LrTable.NT 11,(result,appl1left,appl1right),rest671) end
| (35,(_,(MlyValue.atom atom,atom1left,atom1right))::rest671) => let 
val result=MlyValue.appl((atom))
 in (LrTable.NT 10,(result,atom1left,atom1right),rest671) end
| (36,(_,(MlyValue.atom atom,_,atom1right))::(_,(MlyValue.appl appl,
appl1left,_))::rest671) => let val result=MlyValue.appl((
mk_appl(appl,atom)))
 in (LrTable.NT 10,(result,appl1left,atom1right),rest671) end
| (37,(_,(_,TRUE1left,TRUE1right))::rest671) => let val result=
MlyValue.atom((mk_zerop "erase"))
 in (LrTable.NT 9,(result,TRUE1left,TRUE1right),rest671) end
| (38,(_,(_,ONE1left,ONE1right))::rest671) => let val result=
MlyValue.atom((mk_zerop "true"))
 in (LrTable.NT 9,(result,ONE1left,ONE1right),rest671) end
| (39,(_,(_,EXCL1left,EXCL1right))::rest671) => let val result=
MlyValue.atom((mk_zerop "cut"))
 in (LrTable.NT 9,(result,EXCL1left,EXCL1right),rest671) end
| (40,(_,(MlyValue.id id,id1left,id1right))::rest671) => let val 
result=MlyValue.atom((id))
 in (LrTable.NT 9,(result,id1left,id1right),rest671) end
| (41,(_,(MlyValue.INT INT,INT1left,INT1right))::rest671) => let val 
result=MlyValue.atom((mk_int INT))
 in (LrTable.NT 9,(result,INT1left,INT1right),rest671) end
| (42,(_,(MlyValue.STRING STRING,STRING1left,STRING1right))::rest671)
 => let val result=MlyValue.atom((mk_string STRING))
 in (LrTable.NT 9,(result,STRING1left,STRING1right),rest671) end
| (43,(_,(_,_,RPAREN1right))::(_,(MlyValue.term term,_,_))::(_,(_,
LPAREN1left,_))::rest671) => let val result=MlyValue.atom((term))
 in (LrTable.NT 9,(result,LPAREN1left,RPAREN1right),rest671) end
| (44,(_,(MlyValue.LCID LCID,LCID1left,LCID1right))::rest671) => let 
val result=MlyValue.id((mk_lcid LCID))
 in (LrTable.NT 14,(result,LCID1left,LCID1right),rest671) end
| (45,(_,(MlyValue.UCID UCID,UCID1left,UCID1right))::rest671) => let 
val result=MlyValue.id((mk_ucid UCID))
 in (LrTable.NT 14,(result,UCID1left,UCID1right),rest671) end
| (46,(_,(MlyValue.term term,_,term1right))::_::(_,(MlyValue.bdvar 
bdvar,bdvar1left,_))::rest671) => let val result=MlyValue.lamterm((
mk_abst (bdvar,term)))
 in (LrTable.NT 12,(result,bdvar1left,term1right),rest671) end
| (47,(_,(MlyValue.LCID LCID,LCID1left,LCID1right))::rest671) => let 
val result=MlyValue.bdvar((mk_varbind LCID))
 in (LrTable.NT 13,(result,LCID1left,LCID1right),rest671) end
| (48,(_,(MlyValue.UCID UCID,UCID1left,UCID1right))::rest671) => let 
val result=MlyValue.bdvar((mk_varbind UCID))
 in (LrTable.NT 13,(result,UCID1left,UCID1right),rest671) end
| _ => raise (mlyAction i392)
end
val void = MlyValue.VOID
val extract = fn a => (fn MlyValue.start x => x
| _ => let exception ParseInternal
	in raise ParseInternal end) a 
end
end
structure Tokens : Fol_TOKENS =
struct
type svalue = ParserData.svalue
type ('a,'b) token = ('a,'b) Token.token
fun EOF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 0,(
ParserData.MlyValue.VOID,p1,p2))
fun DOT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 1,(
ParserData.MlyValue.VOID,p1,p2))
fun LINEAR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 2,(
ParserData.MlyValue.VOID,p1,p2))
fun LOCAL (p1,p2) = Token.TOKEN (ParserData.LrTable.T 3,(
ParserData.MlyValue.VOID,p1,p2))
fun MODULE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 4,(
ParserData.MlyValue.VOID,p1,p2))
fun BACKSLASH (p1,p2) = Token.TOKEN (ParserData.LrTable.T 5,(
ParserData.MlyValue.VOID,p1,p2))
fun COMMA (p1,p2) = Token.TOKEN (ParserData.LrTable.T 6,(
ParserData.MlyValue.VOID,p1,p2))
fun SEMICOLON (p1,p2) = Token.TOKEN (ParserData.LrTable.T 7,(
ParserData.MlyValue.VOID,p1,p2))
fun AMPERSAND (p1,p2) = Token.TOKEN (ParserData.LrTable.T 8,(
ParserData.MlyValue.VOID,p1,p2))
fun LPAREN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 9,(
ParserData.MlyValue.VOID,p1,p2))
fun RPAREN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 10,(
ParserData.MlyValue.VOID,p1,p2))
fun LCURLY (p1,p2) = Token.TOKEN (ParserData.LrTable.T 11,(
ParserData.MlyValue.VOID,p1,p2))
fun RCURLY (p1,p2) = Token.TOKEN (ParserData.LrTable.T 12,(
ParserData.MlyValue.VOID,p1,p2))
fun LBRACKET (p1,p2) = Token.TOKEN (ParserData.LrTable.T 13,(
ParserData.MlyValue.VOID,p1,p2))
fun RBRACKET (p1,p2) = Token.TOKEN (ParserData.LrTable.T 14,(
ParserData.MlyValue.VOID,p1,p2))
fun BACKDOUBLE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 15,(
ParserData.MlyValue.VOID,p1,p2))
fun BACKLOLLI (p1,p2) = Token.TOKEN (ParserData.LrTable.T 16,(
ParserData.MlyValue.VOID,p1,p2))
fun DOUBLEARROW (p1,p2) = Token.TOKEN (ParserData.LrTable.T 17,(
ParserData.MlyValue.VOID,p1,p2))
fun DCGARROW (p1,p2) = Token.TOKEN (ParserData.LrTable.T 18,(
ParserData.MlyValue.VOID,p1,p2))
fun ARROW (p1,p2) = Token.TOKEN (ParserData.LrTable.T 19,(
ParserData.MlyValue.VOID,p1,p2))
fun LOLLIPOP (p1,p2) = Token.TOKEN (ParserData.LrTable.T 20,(
ParserData.MlyValue.VOID,p1,p2))
fun LOADLOLLI (p1,p2) = Token.TOKEN (ParserData.LrTable.T 21,(
ParserData.MlyValue.VOID,p1,p2))
fun BAR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 22,(
ParserData.MlyValue.VOID,p1,p2))
fun TRUE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 23,(
ParserData.MlyValue.VOID,p1,p2))
fun ONE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 24,(
ParserData.MlyValue.VOID,p1,p2))
fun FORALL (p1,p2) = Token.TOKEN (ParserData.LrTable.T 25,(
ParserData.MlyValue.VOID,p1,p2))
fun EXISTS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 26,(
ParserData.MlyValue.VOID,p1,p2))
fun EXCL (p1,p2) = Token.TOKEN (ParserData.LrTable.T 27,(
ParserData.MlyValue.VOID,p1,p2))
fun PARSEMODULE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 28,(
ParserData.MlyValue.VOID,p1,p2))
fun PARSEQUERY (p1,p2) = Token.TOKEN (ParserData.LrTable.T 29,(
ParserData.MlyValue.VOID,p1,p2))
fun PARSETERM (p1,p2) = Token.TOKEN (ParserData.LrTable.T 30,(
ParserData.MlyValue.VOID,p1,p2))
fun LCID (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 31,(
ParserData.MlyValue.LCID i,p1,p2))
fun UCID (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 32,(
ParserData.MlyValue.UCID i,p1,p2))
fun INT (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 33,(
ParserData.MlyValue.INT i,p1,p2))
fun STRING (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 34,(
ParserData.MlyValue.STRING i,p1,p2))
fun INFIXOP (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 35,(
ParserData.MlyValue.INFIXOP i,p1,p2))
fun LEFTINFIXOP (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 36,(
ParserData.MlyValue.LEFTINFIXOP i,p1,p2))
fun RIGHTINFIXOP (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 37,(
ParserData.MlyValue.RIGHTINFIXOP i,p1,p2))
end
end
