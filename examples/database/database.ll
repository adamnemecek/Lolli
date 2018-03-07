% This program is based on the database example from the LICS-91/IC-92 papers.
% It has been changed in several places (using the guard control structure)
% to respond correctly when attempts are made to update or retract a committed
% fact. Without extra-logical control, such changes would have to be allowed,
% though they would have had no effect.
% The 'abort' predicate is used to force the database program to halt when the
% user types 'quit'.  If erase is used, the user can fail back into the system.

% Sample usage:
%
% ?- database --o db.
%
% Command: enter (student josh).
% Command: enter (student ramesh).
% Command: commit (student josh).
% Command: enter (professor jean).
% Command: enter (professor dale).
% Command: check (professor jean).
% professor jean is an entry.
% Command: necessary (professor jean).
% Try again.
% Command: update (student ramesh) (professor ramesh).
% student ramesh was updated to professor ramesh.
% Command: update (student josh) (professor josh).
% student josh is a necessary fact, and cannot be updated.
% Command: quit.
%
% aborted...
% ?-


MODULE database.

db :- write_sans "Command: ", read Command, do Command.
db :- write_sans  "Try again.", nl, db.
       
do (enter E)     :- entry E -o db.
do (commit E)    :- entry E => db.
do (retract E)   :- entry E, ({entry E} -> 
			  (write E, write_sans  " is a necessary fact, and ",
 			   write_sans  "cannot be retracted.", nl,  db)
			| (write E, write_sans  " was retracted.", nl,  db)).

do (update E N)  :- entry E, ({entry E} -> 
			  (write E, write_sans  " is a necessary fact, and ",
 			   write_sans  "cannot be updated.", nl,        db)
			| (write E, write_sans  " was updated to ", 
			   write N, write_sans  ".", nl, entry N -o db)).
do (check Q)     :- entry Q, erase, write Q,
		    write_sans  " is an entry.", nl & db.
do (necessary Q) :- {entry Q}, erase, write Q, 
		    write_sans  " is a necessary entry", nl & db.
do quit          :- abort.


