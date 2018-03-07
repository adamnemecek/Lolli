MODULE big_once.


% This program is an unsuccessful attempt to fix the crossing dependency
% problem in big_parser.ll. See the README file for an explanation.



parse Str Tree     :- explode_words Str Lst, 
		      (sent Lst nil Tree ; quest Lst nil Tree).


% (once G) succeeds if and only if G does, but the overall goal can only
% succeed once.

once G :- G -> true | fail.

% grammar rules

sent P1 P2 (sent NP VP)  :- {np P1 PA NP}, vp PA P2 VP.

% For conjoined sentences, we unroll the following definition to avoid 
% left recursion.
%
% sent P1 P2 (and S1 S2)  :- sent P1 (and::P0) S1 & sent P0 P2 S2.

sent P1 P2 (and (sent NP1 VP1) (sent NP2 VP2)) :-
        ({np P1 PA1 NP1}, vp PA1 (and::P0) VP1) &
        ({np P0 PA2 NP2}, vp PA2 P2 VP2).


quest P1 P2 (quest VFA NP AP) :- vfa P1 PA VFA, np PA PB NP, ap PB P2 AP.
quest P1 P2 (quest VFA NP VP) :- vfa P1 PA VFA, np PA PB NP, vp PB P2 VP.
quest P1 P2 (quest (NPWH Gap) Q) :- npwh P1 PA NPWH, 
     	(forall P\ npgap P P (npgap Gap)) -o quest PA P2 Q.
quest P1 P2 (quest (APW Gap) Q) :- apwh P1 PA APW, 
     	(forall P\ apgap P P (apgap Gap)) -o quest PA P2 Q.
quest P1 P2 (quest (PPW Gap) Q) :- ppwh P1 PA PPW, 
     	(forall P\ ppgap P P (ppgap Gap)) -o quest PA P2 Q.
quest P1 P2 (quest (NPWH Gap) VP) :- npwh P1 PA NPWH, vp PA P2 VP.

npwh P1 P2 (npwh NWH) :- nwh P1 P2 NWH.
npwh (which::P1) P2 (npwh which OptAP N) :- optap P1 PA OptAP, n PA P2 N.

apwh P1 P2 (apwh AWH) :- awh P1 P2 AWH.

ppwh P1 P2 (ppwh PWH) :- pwh P1 P2 PWH.

sbar (that::P1) P2 (sbar that S) :- sent P1 P2 S.

qbar P1 P2 (qbar NPWH VP) :- npwh P1 PA NPWH, vp PA P2 VP.
qbar P1 P2 (qbar (NPWH Gap) S) :- npwh P1 PA NPWH, 
     	(forall P\ npgap P P (npgap Gap)) -o sent PA P2 S.

np P1 P2 (np NPGAP) :- once (npgap P1 P2 NPGAP).
np P1 P2 (np PNposs) :- pnposs P1 P2 PNposs.
np P1 P2 (np Det Nposs OptPP OptRel) :-
    det P1 PA Det, nposs PA PB Nposs, optpp PB PC OptPP,
    optrel PC P2 OptRel.

pnposs P1 P2 (pnposs PN) :- pn P1 P2 PN.
pnposs P1 P2 (pnposs PN s Nposs) :-
    pn P1 (s::PA) PN, nposs PA P2 Nposs.

nposs P1 P2 (nposs OptAP N) :- optap P1 PA OptAP, n PA P2 N.
nposs P1 P2 (nposs OptAP N s Nposs) :-
    optap P1 PA OptAP, n PA (s::PB) N, nposs PB P2 Nposs.

vp P1 P2 (vp DV NP PP) :- dv P1 PA DV, np PA PB NP, pp PB P2 PP.
vp P1 P2 (vp TV NP) :- tv P1 PA TV, np PA P2 NP.
vp P1 P2 (vp IV OptPP) :- iv P1 PA IV, optpp PA P2 OptPP.
vp P1 P2 (vp Stv Sbar) :- stv P1 PA Stv, sbar PA P2 Sbar.
vp P1 P2 (vp TV NP Sbar) :- tv P1 PA TV, np PA PB NP, sbar PB P2 Sbar.
vp P1 P2 (vp Qv Qbar) :- qv P1 PA Qv, qbar PA P2 Qbar.
vp P1 P2 (vp Vfa VP) :- vfa P1 PA Vfa, vp PA P2 VP.
vp P1 P2 (vp Vfa AP) :- vfa P1 PA Vfa, ap PA P2 AP.

optpp P1 P1 (optpp epsilon).
optpp P1 P2 (optpp PP) :- pp P1 P2 PP.

pp P1 P2 (pp PPGAP) :- once (ppgap P1 P2 PPGAP).
pp P1 P2 (pp P NP) :- p P1 PA P, np PA P2 NP.

optap P1 P1 (optap epsilon).
optap P1 P2 (optap AP) :- ap P1 P2 AP.

ap P1 P2 (ap APGAP) :- once (apgap P1 P2 APGAP).
ap P1 P2 (ap A) :- a P1 P2 A.

optrel P1 P1 (optrel epsilon).
optrel P1 P2 (optrel Rel) :- rel P1 P2 Rel.

rel (that::P1) P2 (rel that VP) :- {vp P1 P2 VP}. 
rel (who::P1)  P2 (rel who VP)  :- {vp P1 P2 VP}. 
rel (that::P1) P2 (rel (that Gap) S) :- 
     	(forall P\ npgap P P (npgap Gap)) -o sent P1 P2 S.
rel (whom::P1) P2 (rel (whom Gap) S) :- 
	(forall P\ npgap P P (npgap Gap)) -o sent P1 P2 S.
rel P1 P2 (rel P (whom Gap) S) :- 
	p P1 (whom::PA) P,
	(forall P\ ppgap P P (ppgap Gap)) -o sent PA P2 S.
rel P1 P2 (rel P (which Gap) S) :- 
	p P1 (which::PA) P,
	(forall P\ ppgap P P (ppgap Gap)) -o sent PA P2 S.


% pre-terminals and lexical items

det (Det::L) L (det Det) :- det Det Agree.
det the   (pair third Num).
det a     (pair third sing).
det some  (pair third plur).
det every (pair third sing).
det all   (pair third plur).

nwh (NWH::L) L (nwh NWH) :- nwh NWH.
nwh who.
nwh what.
nwh which.

awh (AWH::L) L (awh AWH) :- awh AWH.
awh how.

pwh (PWH::L) L (pwh PWH) :- pwh PWH.
pwh where.

n (N::L) L (n N) :- n N Agree.
n man		(pair third sing).
n woman 	(pair third sing).
n girl 		(pair third sing).
n boy  		(pair third sing).
n author 	(pair third sing).
n book		(pair third sing).
n professor	(pair third sing).
n program	(pair third sing).
n programmer	(pair third sing).
n student	(pair third sing).
n computer	(pair third sing).

n men		(pair third plur).
n women 	(pair third plur).
n girls		(pair third plur).
n boys		(pair third plur).
n authors	(pair third plur).
n books		(pair third plur).
n professors	(pair third plur).
n programs	(pair third plur).
n programmers	(pair third plur).
n students	(pair third plur).
n computers	(pair third plur).
n fish		(pair third Num).

pn (PN::L) L (pn PN) :- pn PN Agree.
pn rufus	(pair third sing).
pn dale		(pair third sing).
pn eva		(pair third sing).
pn josh		(pair third sing).
pn elizabeth	(pair third sing).
pn steven	(pair third sing).
pn catherine	(pair third sing).
pn mary		(pair third sing).
pn bob		(pair third sing).
pn jill		(pair third sing).
pn bill		(pair third sing).
pn jane		(pair third sing).
pn john		(pair third sing).
pn sally	(pair third sing).

pn i		(pair first sing).
pn you		(pair second Num).
pn he		(pair third sing).
pn she		(pair third sing).
pn it		(pair third sing).
pn we		(pair first plur).
pn they		(pair third plur).

tv (TV::L) L (tv TV) :- tv TV Agree.
tv love		(pair first  sing).
tv love		(pair second sing).
tv love		(pair Person plur).
tv loves	(pair third sing).
tv loved	(pair Person Num).
tv marry	(pair first  sing).
tv marry	(pair second sing).
tv marry	(pair Person plur).
tv marries	(pair third sing).
tv married	(pair Person Num).
tv concern	(pair first  sing).
tv concern	(pair second sing).
tv concern	(pair Person plur).
tv concerns	(pair third sing).
tv concerned	(pair Person Num).
tv meet		(pair first  sing).
tv meet		(pair second sing).
tv meet		(pair Person plur).
tv meets	(pair third sing).
tv met		(pair Person Num).
tv write	(pair first  sing).
tv write	(pair second sing).
tv write	(pair Person plur).
tv writes	(pair third sing).
tv wrote	(pair Person Num).
tv told		(pair P N).
tv saw		(pair P N).
tv sees		(pair P N).

iv (IV::L) L (iv IV) :- iv IV Agree.
iv run		(pair first  sing).
iv run		(pair second sing).
iv run		(pair Person plur).
iv runs		(pair third sing).
iv ran		(pair Person Num).
iv halt		(pair first  sing)
iv halt		(pair second sing).
iv halt		(pair Person plur).
iv halts	(pair third sing).
iv halted	(pair Person Num).

dv (DV::L) L (dv DV) :- dv DV Agree.
dv meet		(pair first  sing).
dv meet		(pair second sing).
dv meet		(pair Person plur).
dv meets	(pair third sing).
dv met		(pair Person Num).
dv write	(pair first  sing).
dv write	(pair second sing).
dv write	(pair Person plur).
dv writes	(pair third sing).
dv wrote	(pair Person Num).
dv written	(pair P N).
dv give		(pair first  sing).
dv give		(pair second sing).
dv give		(pair Person plur).
dv gives	(pair third sing).
dv gave		(pair Person Num).

stv (STV::L) L (stv STV) :- stv STV Agree.
stv believe	(pair first  sing).
stv believe	(pair second sing).
stv believe	(pair Person plur).
stv believes	(pair third sing).
stv believed	(pair Person Num).
stv think	(pair first  sing).
stv think	(pair second sing).
stv think	(pair Person plur).
stv thinks	(pair third sing).
stv thought	(pair Person Num).

qv (QV::L) L (qv QV) :- qv QV.
qv wondered.
qv wonders.
qv asks.
qv asked.


vfa (VFA::L) L (vfa VFA) :- vfa VFA.
vfa 'is'.
vfa did.
vfa was.
vfa would.

a (A::L) L (a A) :- a A.
a	tall.
a	stupid.
a	short.
a	smart.


p (P::L) L (p P) :- p P.
p with.
p about.
p to.
p under.
p above.
p on.