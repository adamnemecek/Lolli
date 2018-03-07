MODULE sort ordering.

% By declaring these predicate names LOCAL, the implementation of the
% sort predicate is effectively hidden from the outside environment.

LOCAL collect unpack hyp.

% A list sorting package. This is yet another variation on the list rewriting
% theme. The only modification to the basic pattern is that collect can only
% collect things according to the ordering by which the module is 
% parameterized.
%
% Sample Usage:
%
%	?- sort '>=' --o sort (1::3::5::2::4::6::0::nil) A.
%	A_1 <- 6 :: 5 :: 4 :: 3 :: 2 :: 1 :: 0 :: nil
%	yes
%	?- sort '=<' --o sort (1::3::5::2::4::6::0::nil) A.
%	A_97424 <- 0 :: 1 :: 2 :: 3 :: 4 :: 5 :: 6 :: nil
%	yes
%	?- sort '=<' --o sort (1::2::3::nil) (2::3::1::nil).
%	no
%	?- sort '=<' --o sort A (1::2::nil).
%	A_181288 <- 2 :: 1 :: nil;
%	A_181288 <- 1 :: 2 :: nil


collect nil.
collect (X::nil) :- hyp X.
collect (X::Y::L) :- hyp X, collect (Y::L), ordering X Y.

unpack nil G :- G.
unpack (X::L) G :- hyp X -o unpack L G.

sort L K :- unpack L (collect K).




