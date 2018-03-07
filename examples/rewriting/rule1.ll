MODULE rule1 store.

% A module of rewrite rules to be loaded from the module rewrite.ll
% This set of rules just rewrites a number to two values that add up to the
% original number.

% The module is parameterized by the predicate name used to store the
% elements being rewritten.


rewrite G :- G.

rewrite G :- store 6, ((store 3, store 3) -o rewrite G).
rewrite G :- store 6, ((store 4, store 2) -o rewrite G).
rewrite G :- store 6, ((store 5, store 1) -o rewrite G).

rewrite G :- store 5, ((store 3, store 2) -o rewrite G).
rewrite G :- store 5, ((store 4, store 1) -o rewrite G).

rewrite G :- store 5, ((store 3, store 2) -o rewrite G).
rewrite G :- store 5, ((store 4, store 1) -o rewrite G).

rewrite G :- store 4, ((store 2, store 2) -o rewrite G).
rewrite G :- store 4, ((store 3, store 1) -o rewrite G).

rewrite G :- store 3, ((store 2, store 1) -o rewrite G).

rewrite G :- store 2, ((store 1, store 1) -o rewrite G).
