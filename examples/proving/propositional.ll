% This Module implements a complete (even in the depth-first setting)
% theorem prover for propositional intuitionistic logic. This example,
% was discussed in the LICS-91/IC-92 papers, and is based in part on the
% work of Roy Dyckoff.


MODULE propositional.

pv true :- true.

pv (and A B) :- pv A & pv B.
pv (imp A B) :- hyp A -o pv B.
pv (or A B)  :- pv A.
pv (or A B)  :- pv B.

pv C :- hyp (and A B), hyp A -o hyp B -o pv C.
pv C :- hyp (or A B), (hyp A -o pv C & hyp B -o pv C).
pv C :- hyp false, erase.
pv C :- hyp true, pv C.
pv C :- hyp C, erase.

pv C :- hyp (imp (imp A1 A2) B),
        (hyp (imp A2 B) -o pv (imp A1 A2) & hyp B -o pv C).
pv C :- hyp (imp (and A1 A2) B),
        hyp (imp A1 (imp A2 B)) -o pv C.
pv C :- hyp (imp (or A1 A2) B),
        hyp (imp A1 B) -o hyp (imp A2 B) -o pv C.
pv C :- hyp (imp false B), pv C.
pv C :- hyp (imp true B), hyp B -o pv C.
pv C :- hyp (imp A B), atom A, hyp A, hyp B -o hyp A -o pv C.


% Instead of explicitely axiomatizing the 'atom' predicate, as was done
% in the paper, we define it in terms of negation-as-failure.

atom A :- not (A = (and B C)), not (A = (or B C)), not (A = (imp B C)),
          not (A = false), not (A = true).

not G :- G -> fail | true.
