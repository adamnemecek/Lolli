MODULE ldcg.

% This code comes in part from a DCG -> Prolog translator recently
% posted on comp.lang.prolog.

% Sample Usage:
%
%	?- ldcg --o ldcg.
%	Linear Definite Clause Grammar (LDCG) translator
%	LDCG file?  "small".
%	Lolli file? "small".
%	solved
%	yes
%	?- bye.
%	Closing Loli.

append nil    L L.
append (H::T) L (H::K) :- append T L K.

concat A B C :- explode A A1, explode B B1, append A1 B1 C1, explode C C1.


ldcg :- write_sans "Linear Definite Clause Grammar (LDCG) translator", nl,
     	write_sans "LDCG file?  ", read Read,
	write_sans "Lolli file? ", read Write,
	concat Read ".ldcg" Readfile, concat Write ".ll" Writefile,
	seeing Readfile (telling Writefile 
				(write_sans "MODULE ", write_sans Write,
				 write_sans ".", nl, do_gtrans)).

do_gtrans :- read LDCG, 
	LDCG = end_of_file  -> true
	     | (gtrans LDCG CLAUSE, write_clause CLAUSE, write_sans ".", nl, 
		do_gtrans).


gtrans LDCG Term :- 
	LDCG = (Head --> Body) -> trans_head Head S0 S Head1, 
				  trans_body Body S0 S Body1,
				  (Body1 = true -> Term = Head1
					 | Term = (Head1 :- Body1))
	     | Term = LDCG.

%trans_head((NonTerm,PushBack), S0, S, Head1) :- !,
%        nonvar(PushBack),
%        append(PushBack, S, S1),
%        trans_goal(NonTerm, S0, S1, Head1).

trans_head NonTerm S0 S Head :- trans_goal NonTerm S0 S Head.

trans_goal Goal Before After (Goal Before After).

trans_body fail      S  S fail.
trans_body true      S  S true.
trans_body erase     S  S erase.
trans_body ({Goal})  S0 S ({Goal1}) :- trans_body Goal S0 S Goal1.
trans_body ([Goal])  S  S Goal.
trans_body (P1,P2)   S0 S G :- trans_body P1 S0 S1 G1, trans_body P2 S1 S  G2,
			     trans_and G1 G2 G.
trans_body (P1;P2)   S0 S (G1;G2) :- trans_or P1 S0 S G1, trans_or P2 S0 S G2.
trans_body (D -o P)  S0 S (D2 -o P1) :- gtrans D D1, generalize D1 D2,
					trans_body P S0 S P1.
trans_body Terminals S0 S true :- append Terminals S S0.
trans_body NonTerm   S0 S Goal :- 
	var NonTerm -> Goal = (ldcg --o trans_body NonTerm S0 S Goal)
		     | trans_goal NonTerm S0 S Goal.

% These are not yet implemented
%trans_body (P1&P2)   S0 S G :- trans_body P1 S0 S1 G1, trans_body P2 S1 S  G2,
%			     trans_and G1 G2 G.
%trans_body((!), S, S, (!)) :- !.

%trans_or(P, S0, S, G) :-
%        trans_body(P, S1, S, G1), !,
%        trans_or(S1, S, S0, G1, G).

%trans_or(S0, S, S0, G, G) :-
%        var(S0), S0 \== S, !.
%trans_or(S1, _, S0, true, (S0=S1)) :- !.
%trans_or(S1, _, S0, G, (S0=S1,G)).


trans_and (A,B) C (A,D) :- trans_and B C D.
trans_and true A A.
trans_and A true A.
trans_and A B (A,B).
