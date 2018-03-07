MODULE compile.

LOCAL reg.

% This file contains two versions of a simple expression compiler.
% The first is quite simple, and will use each register on the target machine
% only once. The second version is essentially the same code, but as registers 
% are no longer needed, they are returned to a pool of available registers.

% UTILITY PREDICATES
% ==================

% Define negation-as-failure in terms of guard expressions

  not G :- G -> false | true.

% release/2 loads the database with resources, one for each register included
% in the list in the first argument, then attempts to prove the second one.

  release nil G :- G.
  release (H::T) G :- reg H -o release T G.

% Pretty print a machine code tree.

  writec (A,B,C) :- writec A, nl, writec B, nl, writec C, nl.
  writec C :- not (C = (A,B,D)), write C.

% Given N, generate a list of registers, named '(r 1)' to '(r n)'.

  reglist N Rs :- (N = 0) -> (Rs = nil)
                           | (Rs = ((r N)::RL), N1 is (N - 1), reglist N1 RL).

% EXPRESSION COMPILER, NO REGISTER REUSE
% ======================================

% Can a given Expr be compiled to machine code using only Numregs registers
% each at most once. If so, print the compiled code.

  compile Expr Numregs:- reglist Numregs Regs, 
		         release Regs (comp Expr Code Reg erase), writec Code.

% The complex expression (X op Y)  is compiled to the code tree 
%     (C1 , C2 , (machine_op R3 R1 R2))
% putting its result in register R3, if X compiles to C1, with result in R1,
% and Y compiles to C2, with result in R2, and a register R3 is available,
% and G is provable.
% 
% Since registers are not reused, it is not necessary to use continuation
% passing style for this routine, i.e. the first case could just be:
%
% comp (X + Y) (C1,C2,(add R3 R1 R2)) R3 :- comp X C1 R1, comp Y C2 R2, reg R3.
%
% We use c.p. style in order to ease into the re-use version given next.

  comp (X + Y) (C1,C2,(add R3 R1 R2)) R3 G :-
	  comp X C1 R1 (comp Y C2 R2 (reg R3,G)).
  comp (X - Y) (C1,C2,(sub R3 R1 R2)) R3 G :-
	  comp X C1 R1 (comp Y C2 R2 (reg R3,G)).
  comp (X * Y) (C1,C2,(mul R3 R1 R2)) R3 G :-
	  comp X C1 R1 (comp Y C2 R2 (reg R3,G)).
  comp (X / Y) (C1,C2,(div R3 R1 R2)) R3 G :-
	  comp X C1 R1 (comp Y C2 R2 (reg R3,G)).

  comp X (load R X) R G :- not (X = A + B), not (X = A - B),
	 		   not (X = A * B), not (X = A / B), reg R, G.

%	?- compile ((1 + 2) * (3 + 4) * (5 * 6)) 14
%	load (r 1) 1
%	load (r 2) 2
%	add (r 3) (r 1) (r 2)
%
%	load (r 4) 3
%	load (r 5) 4
%	add (r 6) (r 4) (r 5)
%
%	mul (r 7) (r 3) (r 6)
%
%	load (r 8) 5
%	load (r 9) 6
%	mul (r 10) (r 8) (r 9)
%
%	mul (r 11) (r 7) (r 10)
%	solved
%	yes


% EXPRESSION COMPILER, WITH REGISTER REUSE
% ========================================

% Can a given Expr be compiled to machine code using only Numregs registers
% if the registers are reused greedily. If so, print the compiled code.

  compile2 Expr Numregs:- reglist Numregs Regs, 
		          release Regs (comp2 Expr Code Reg erase), writec Code.

% The complex expression (X op Y)  is compiled to the code tree 
%     (C1 , C2 , (machine_op R3 R1 R2))
% putting its result in register R3, if X compiles to C1, with result in R1,
% and Y compiles to C2, with result in R2, and if, after releasing R1 and R2,
% a register R3 is available, and G is provable.

  comp2 (X + Y) (C1,C2,(add R3 R1 R2)) R3 G :-
	  comp2 X C1 R1 (comp2 Y C2 R2 (release (R1::R2::nil) (reg R3,G))).
  comp2 (X - Y) (C1,C2,(sub R3 R1 R2)) R3 G :-
	  comp2 X C1 R1 (comp2 Y C2 R2 (release (R1::R2::nil) (reg R3,G))).
  comp2 (X * Y) (C1,C2,(mul R3 R1 R2)) R3 G :-
	  comp2 X C1 R1 (comp2 Y C2 R2 (release (R1::R2::nil) (reg R3,G))).
  comp2 (X / Y) (C1,C2,(div R3 R1 R2)) R3 G :-
	  comp2 X C1 R1 (comp2 Y C2 R2 (release (R1::R2::nil) (reg R3,G))).

  comp2 X (load R X) R G :- not (X = A + B), not (X = A - B),
			    not (X = A * B), not (X = A / B), reg R, G.


%	?-  compile2  ((1 + 2) * (3 + 4) * (5 * 6)) 14
%	load (r 1) 1
%	load (r 2) 2
%	add (r 2) (r 1) (r 2)
%
%	load (r 1) 3
%	load (r 3) 4
%	add (r 3) (r 1) (r 3)
%
%	mul (r 3) (r 2) (r 3)
%
%	load (r 2) 5
%	load (r 1) 6
%	mul (r 1) (r 2) (r 1)
%
%	mul (r 1) (r 3) (r 1)
%	solved
%	yes
