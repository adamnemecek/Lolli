
structure Tokens = Tokens
structure Interface = Interface
open Interface

type pos = Interface.pos
type svalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult= (svalue,pos) token

val eof = fn () => Tokens.EOF(!line,!line)

fun makeInt (s : string) = 
  let val ord0 = ord "0"
      fun rec_mi nil = 0
        | rec_mi (h::t) = ((ord h) - ord0) + (10 * (rec_mi t))
  in rec_mi (rev (explode s)) end

fun strip_quotes (s:string) =
      let val ( _ :: tail) = (explode s) 
        in let val ( _ :: middle) = (rev tail)
             in (implode (rev middle)) end end 

fun strip_carats (s:string) =
  let fun rec_sc nil = nil
	| rec_sc ("^"::quoted_char::tail) = (quoted_char::(rec_sc tail))
	| rec_sc (head::tail) = (head::(rec_sc tail))
  in (implode (rec_sc (explode s))) end

%%
%header (functor FolLexFun(structure Tokens: Fol_TOKENS
			   structure Interface: INTERFACE) : LEXER);
%s COMMENT;
lcstart=[a-z];
ucstart=[A-Z_];
idchars={lcstart}|{ucstart}|[0-9]|\^.|\^\n;
ucid={ucstart}{idchars}*;
lcid={idchars}*;
quote_ucid='{ucstart}[^\']*';
quote_lcid='[^\']*';
ws=[\t\ \012]*;
num=[0-9]+;
string=\"[^\"]*\";
infixop="="|"=:="|"=\\="|"=<"|">="|"<"|">"|"is";
leftinfixop="+"|"-"|"*"|"/";
rightinfixop="::";
%%
<INITIAL>{ws}		=> (lex());
<INITIAL>\n		=> (next_line(); lex());
<INITIAL>"%"		=> (YYBEGIN COMMENT; lex());
<INITIAL>"MODULE" 	=> (Tokens.MODULE(!line,!line));
<INITIAL>"LINEAR" 	=> (Tokens.LINEAR(!line,!line));
<INITIAL>"LOCAL"  	=> (Tokens.LOCAL(!line,!line));
<INITIAL>"<="		=> (Tokens.BACKDOUBLE(!line,!line));
<INITIAL>":-"		=> (Tokens.BACKLOLLI(!line,!line));
<INITIAL>"-->"		=> (Tokens.DCGARROW(!line,!line));
<INITIAL>","		=> (Tokens.COMMA(!line,!line));
<INITIAL>";"		=> (Tokens.SEMICOLON(!line,!line));
<INITIAL>"&"		=> (Tokens.AMPERSAND(!line,!line));
<INITIAL>"."    	=> (Tokens.DOT(!line,!line));
<INITIAL>"\\"   	=> (Tokens.BACKSLASH(!line,!line));
<INITIAL>"("		=> (Tokens.LPAREN(!line,!line));
<INITIAL>")"		=> (Tokens.RPAREN(!line,!line));
<INITIAL>"{"		=> (Tokens.LCURLY(!line,!line));
<INITIAL>"}"		=> (Tokens.RCURLY(!line,!line));
<INITIAL>"["		=> (Tokens.LBRACKET(!line,!line));
<INITIAL>"]"		=> (Tokens.RBRACKET(!line,!line));
<INITIAL>"->"		=> (Tokens.ARROW(!line,!line));
<INITIAL>"--o"		=> (Tokens.LOADLOLLI(!line,!line));
<INITIAL>"-o"		=> (Tokens.LOLLIPOP(!line,!line));
<INITIAL>"=>"		=> (Tokens.DOUBLEARROW(!line,!line));
<INITIAL>"|"		=> (Tokens.BAR(!line,!line));
<INITIAL>"!"		=> (Tokens.EXCL(!line,!line));
<INITIAL>"erase" 	=> (Tokens.TRUE(!line,!line));
<INITIAL>"true"  	=> (Tokens.ONE(!line,!line));
<INITIAL>"forall" 	=> (Tokens.FORALL(!line,!line));
<INITIAL>"exists" 	=> (Tokens.EXISTS(!line,!line));
<INITIAL>{infixop} 	=> (Tokens.INFIXOP (yytext,!line,!line));
<INITIAL>{leftinfixop} 	=> (Tokens.LEFTINFIXOP (yytext,!line,!line));
<INITIAL>{rightinfixop} => (Tokens.RIGHTINFIXOP (yytext,!line,!line));
<INITIAL>{num}		=> (Tokens.INT (makeInt yytext,!line,!line));
<INITIAL>{string} 	=> (Tokens.STRING (strip_quotes yytext,!line,!line));
<INITIAL>{ucid} 	=> (Tokens.UCID (strip_carats yytext,!line,!line));
<INITIAL>{lcid} 	=> (Tokens.LCID (strip_carats yytext,!line,!line));
<INITIAL>{quote_ucid} 	=> (Tokens.UCID (strip_quotes yytext,!line,!line));
<INITIAL>{quote_lcid} 	=> (Tokens.LCID (strip_quotes yytext,!line,!line));

<INITIAL>.		=> (error ("ignoring illegal character" ^ yytext,
			   !line,!line); lex());
<COMMENT>\n     	=> (next_line(); YYBEGIN INITIAL; lex());
<COMMENT>.		=> (lex());
