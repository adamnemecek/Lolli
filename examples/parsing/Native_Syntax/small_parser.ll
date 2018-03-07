MODULE small_parser.

%Sample Natural Language Parser
%Based on the example in the  LICS/I&C paper, this one uses some
%built-ins to make it pretty, and also returns the parse tree.

%Sample Use:
%  ?- small_parser --o top.
%  ?- parse "bob loves mary" T.
%  
%  T5 <- sent (np (pn bob)) (vp (tv loves) (np (pn mary))).
%  yes
%
%  ?- parse "mary loves the man whom jill married" T.
%  
%  T441 <- sent (np (pn mary)) (vp (tv loves) (np (det the) (n man) 
%          (rel whom (sent (np (pn jill)) (vp (tv married) (np gap)))))).
%  yes

parse Str Tree     :- explode_words Str Lst, sent Lst nil Tree.



% grammar rules

sent P1 P2 (sent N V)  :- {np P1 P0 N}, vp P0 P2 V.

vp P1 P2 (vp T N)      :- tv P1 P0 T, np P0 P2 N.
vp P1 P2 (vp Stv Sbar) :- stv P1 P0 Stv, sbar P0 P2 Sbar.

sbar (that::P1) P2 (sbar that S) :- sent P1 P2 S.

np P1 P2 (np D N)   :- det P1 P0 D, n P0 P2 N.
np P1 P2 (np D N R) :- det P1 P0 D, n P0 P3 N, rel P3 P2 R.
np P1 P2 (np P)     :- pn P1 P2 P.

rel (whom::P1) P2 (rel whom S) :- (forall Z\ np Z Z (np gap)) -o sent P1 P2 S.



% lexical items

det (the::L) L (det the).

n (man::L) L (n man).
n (woman::L) L (n woman).
n (girl::L) L (n girl).
n (boy::L) L (n boy).

pn (mary::L) L (pn mary).
pn (bob::L) L (pn bob).
pn (jill::L) L (pn jill).

tv (loves::L) L (tv loves).
tv (married::L) L (tv married).

stv (believes::L) L (stv believes).
