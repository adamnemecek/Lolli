signature Fol_TOKENS =
sig
type ('a,'b) token
type svalue
val RIGHTINFIXOP: (string) *  'a * 'a -> (svalue,'a) token
val LEFTINFIXOP: (string) *  'a * 'a -> (svalue,'a) token
val INFIXOP: (string) *  'a * 'a -> (svalue,'a) token
val STRING: (string) *  'a * 'a -> (svalue,'a) token
val INT: (int) *  'a * 'a -> (svalue,'a) token
val UCID: (string) *  'a * 'a -> (svalue,'a) token
val LCID: (string) *  'a * 'a -> (svalue,'a) token
val PARSETERM:  'a * 'a -> (svalue,'a) token
val PARSEQUERY:  'a * 'a -> (svalue,'a) token
val PARSEMODULE:  'a * 'a -> (svalue,'a) token
val EXCL:  'a * 'a -> (svalue,'a) token
val EXISTS:  'a * 'a -> (svalue,'a) token
val FORALL:  'a * 'a -> (svalue,'a) token
val ONE:  'a * 'a -> (svalue,'a) token
val TRUE:  'a * 'a -> (svalue,'a) token
val BAR:  'a * 'a -> (svalue,'a) token
val LOADLOLLI:  'a * 'a -> (svalue,'a) token
val LOLLIPOP:  'a * 'a -> (svalue,'a) token
val ARROW:  'a * 'a -> (svalue,'a) token
val DCGARROW:  'a * 'a -> (svalue,'a) token
val DOUBLEARROW:  'a * 'a -> (svalue,'a) token
val BACKLOLLI:  'a * 'a -> (svalue,'a) token
val BACKDOUBLE:  'a * 'a -> (svalue,'a) token
val RBRACKET:  'a * 'a -> (svalue,'a) token
val LBRACKET:  'a * 'a -> (svalue,'a) token
val RCURLY:  'a * 'a -> (svalue,'a) token
val LCURLY:  'a * 'a -> (svalue,'a) token
val RPAREN:  'a * 'a -> (svalue,'a) token
val LPAREN:  'a * 'a -> (svalue,'a) token
val AMPERSAND:  'a * 'a -> (svalue,'a) token
val SEMICOLON:  'a * 'a -> (svalue,'a) token
val COMMA:  'a * 'a -> (svalue,'a) token
val BACKSLASH:  'a * 'a -> (svalue,'a) token
val MODULE:  'a * 'a -> (svalue,'a) token
val LOCAL:  'a * 'a -> (svalue,'a) token
val LINEAR:  'a * 'a -> (svalue,'a) token
val DOT:  'a * 'a -> (svalue,'a) token
val EOF:  'a * 'a -> (svalue,'a) token
end
signature Fol_LRVALS=
sig
structure Tokens : Fol_TOKENS
structure ParserData:PARSER_DATA
sharing type ParserData.Token.token = Tokens.token
sharing type ParserData.svalue = Tokens.svalue
end
