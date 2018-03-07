MODULE sw Name initial.

LOCAL register.

% This module implements a mutable toggle switch, named 'Name' with
% initial state 'initial'. The state of the switch is stored in the
% local predicate 'register'. There is a different such register for
% each switch created. There is an appropriately instantiated copy
% of each of the clauses below for each switch.
%
% This is a re-implementation of the first basic example in the paper
% "Representing Object Objects in a Logic Programming Language with 
%  Scoping Constructs", Hodas & Miller, ICLP-90.
%
% Sample Usage:
%
% 	?- sw s1 on --o top.
%	?- sw s2 off --o top.
%	?- toggle s1 top.
%	?- setting s1 S.
%	S_39 <- off;
%	no
%	?- setting s2 S.
%	S_68 <- off;
%	no
%	?- toggle s2 top.
%	?- toggle S (setting S on). %What switch can be toggled to make it on?
%	S_118 <- s1;
%	no
%	?- toggle S (setting S off). 
%	S_245 <- s2;
%	no
%	?- set_on S (setting S on).
%	S_372 <- s2;
%	S_372 <- s1;
%	no
%	?- bye.
%	Closing Loli.


LINEAR register initial.

setting Name Setting :- register Setting, erase.

set_on Name Goal :- register Old, register on -o Goal.
set_off Name Goal :- register Old, register off -o Goal.

toggle Name Goal :- register on, register off -o Goal.
toggle Name Goal :- register off, register on -o Goal. 
