MODULE examples.

% This module tests the provability of some sample formulas of this fragment
% of Linear Logic.  Not all are theorems.

% proving examples will cause each of the example clauses to be
% proved as many times as possible. Formulas 20 through 24 are not provable, 
% 17 has eight proofs, 25 has two proofs, and 27 has three proofs. That
% formula 28 has only a single proof is a result of the lazy treatment of
% erasure, which is explained in the proof system shown in 
% ../../papers/newio.dvi

% Sample Usage:
%
% 	?- examples --o examples.
%	1 solved
%	2 solved
%	3 solved
%	4 solved
%	...
 
formula 1  (a -o a).
formula 2  (a -o b -o (a , b)).
formula 3  (a => {a}).
formula 4  ((a & b) -o (a & b)).
formula 5  (a => (a & a)).
formula 6  (a => (a , a)).
formula 7  ((a & b) -o a).
formula 8  (a -o (a & a)).
formula 9  (a => b => {a & b}).
formula 10 ((a & b) => ({a}, {b})).
formula 11 ((a -o b -o c) -o (a => b => c)).
formula 12 (((a , b) -o c) -o (a -o b -o c)).
formula 13 (a -o b -o (a , erase)).
formula 14 (a -o b -o (erase , a)).
formula 15 (a -o b -o (b , erase , a)).
formula 16 (a -o b => (b , erase , a)).
formula 17 ((a & b) -o (a & b) -o ((a , a) & (a , b) & (b , b))).
formula 18 (a => b -o (b , {a})).
formula 19 (a => b -o ({a} , b)).
formula 20 (a -o (a , a)).
formula 21 (a -o a -o a).
formula 22 (a -o b -o (a & b)).
formula 23 ((a & b) -o (a , b)).
formula 24 ((a -o b -o c) -o (a -o b) -o a -o c).
formula 25 ((a -o b -o c) -o (a -o b) -o (a -o a -o c)).
formula 26 (a -o b -o c -o erase).
formula 27 (a -o a -o a -o (a , erase)).
formula 28 (a -o b -o c -o (erase , erase)).

examples :- formula X F, F, write X, write_sans " solved", nl, fail.


