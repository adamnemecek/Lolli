% Here are some sample intuitionistic formulas to use to test the
% propositional theorem prover.  Not all are provable.
% Thanks to Bob Constable for some of the more interesting ones.


% Sample use:
%
% ?- propositional --o test --o test.
% 1
% 2
% 3
% 3 ...
%


MODULE test.


prop 1  (imp a a).
prop 2  (imp (or a b) (or b a)).
prop 3  (imp (and a b) (and b a)).
prop 4  (imp a (imp b a)).
prop 5  (imp (imp a (imp b c)) (imp (imp a b) (imp a c))).
prop 6  (imp (imp (imp a b) a) (imp (imp a b) b)).
prop 7  (imp (imp (imp a b) a) a).
prop 8  (imp (and (imp a b) (imp c a)) (imp c b)).
prop 9  (imp (or a b) (imp (imp a c) (imp (imp b c) c))).
prop 10 (imp (or a b) (imp (imp a c) (imp (imp (and b d) c) (imp d c)))).
prop 11 (imp (or (imp a b) (imp a c)) (imp a (or b c))).
prop 12 (imp (or a b) (imp (imp a c) (imp (imp b (imp d c)) (imp d c)))).
prop 13 (imp (and (and a a) (imp a b)) b).
prop 14 (imp a (imp a (imp (imp a b) b))).

prop 15 (imp (or c (imp c false)) (imp (and (imp a b) (imp (imp a c) b)) b)).
prop 16 (imp (or b (imp b false)) (imp (and (a imp b) (imp (imp a c) b)) b)).
prop 17 (imp (or a (imp a false)) (imp (and (a imp b) (imp (imp a c) b)) b)).
prop 18 (imp (imp b (imp b false)) (imp (imp (imp b false) false) b)).


test :- prop A B, pv B, write A, nl, fail.
