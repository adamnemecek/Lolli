% This program is a simple, artificial, demonstration of the use of the
% with operator ('&') in the head of a clause.


MODULE with_clause.

LINEAR (a & b).

(c & d) :- a.
(e & f) :- b.


% The last two clauses demonstrate the use of with in the head of a clause.
% This creates a clause that will match multiple goals. That is, it says
% that either of the heads can be proved using the body.

% The first clause demonstrates the use of with to select between mutually
% exculsive clauses (since the clasue (a & b) is equivalent to 
% ((a :- true) & (b :- true))).

% Taken together, this program will prove any one of a, b, c, d, e, or f, 
% but no two of them. In contrast, if the LINEAR declaration is removed from
% the first clause, the program will prove any conjunction of those goals.
% Ie:
%
% 	?- with_clause --o top.
%	?- a.
%	solved
%	yes
%	?- c.
%	solved
%	yes
%	?- a,b.
%	no
%	?- c,d.
%	no
%	?- erase , ((a & b) => top).	% replace LINEAR with non-linear
%	?- a,b,c.
%	solved
%	yes
%	?- a,d,c,a,a,f.
%	solved
%	yes
%	?-
%
%
% This feature is most useful, I think, in providing multiple heads for a 
% single clause. For that purpose I would recommend formatting of the form:
%
% ( (head_1 ... ) &
%   (head_2 ... ) &
%   ...
%   (head_n ... ) ) :- body_of_clause.


