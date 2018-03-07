MODULE rewrite rulemodule.

LOCAL store.

% This module defines the shell of the rewriting system.
%
% Sample Usage:
%
% 	?- rewrite rule1 --o rewrite (6::nil) L.
%	L_1 <- 6 :: nil;
%	L_1 <- 3 :: 3 :: nil;
%	L_1 <- 3 :: 3 :: nil;
%	L_1 <- 2 :: 1 :: 3 :: nil;
%	L_1 <- 2 :: 3 :: 1 :: nil;
%	L_1 <- 1 :: 2 :: 3 :: nil;
%	L_1 <- 1 :: 3 :: 2 :: nil;
%	L_1 <- 3 :: 2 :: 1 :: nil;
%	L_1 <- 3 :: 1 :: 2 :: nil;
%	L_1 <- 2 :: 1 :: 2 :: 1 :: nil


% collect gathers all the list elements, currently stored in the database
% using the `store' predicate, back into a list.

collect nil.
collect (X::L) :- store X, collect L.


% unpack takes the elements of the given list and loads them into the
% database individually, putting them in the `store' predicate. When done
% it calls the continuation goal `G'.

unpack nil G :- G.
unpack (X::L) G :- store X -o unpack L G.


% Given a list, L:
%
%    1) unpack the list into the database
%    2) load a module of rewriting rules. Pass the module the name
%	used locally for storage, so the rules in the module can
	access the terms for rewriting.
%    3) use those rules to perform some amount of rewriting
%    4) gather the rewritten elements back into the list K.

rewrite L K :- unpack L ((rulemodule store) --o (rewrite  (collect K))).



