MODULE big2.
parse Str_798 Tree_796 :- (explode_words Str_798 Lst_797 , (sent Tree_796 Lst_797 nil; quest Tree_796 Lst_797 nil)).
sent (sent NP_820 VP_819) S0_830 S_831 :- ({np NP_820 S0_830 S1_906} , vp VP_819 S1_906 S_831).
quest (quest VFA_1326 NP_1325 AP_1324) S0_1336 S_1337 :- (vfa VFA_1326 S0_1336 S1_1412 , np NP_1325 S1_1412 S1_1606 , ap AP_1324 S1_1606 S_1337).
quest (quest VFA_2064 NP_2063 VP_2062) S0_2074 S_2075 :- (vfa VFA_2064 S0_2074 S1_2150 , np NP_2063 S1_2150 S1_2344 , vp VP_2062 S1_2344 S_2075).
quest (quest NPWH_2801 Q_2800) S0_2811 S_2812 :- (npwh NPWH_2801 S0_2811 S1_2887 , np (np gap) -o quest Q_2800 S1_2887 S_2812).
quest (quest APW_3343 Q_3342) S0_3353 S_3354 :- (apwh APW_3343 S0_3353 S1_3429 , ap (ap gap) -o quest Q_3342 S1_3429 S_3354).
quest (quest PPW_3885 Q_3884) S0_3895 S_3896 :- (ppwh PPW_3885 S0_3895 S1_3971 , pp (pp gap) -o quest Q_3884 S1_3971 S_3896).
quest (quest NPWH_4427 VP_4426) S0_4437 S_4438 :- (npwh NPWH_4427 S0_4437 S1_4513 , vp VP_4426 S1_4513 S_4438).
npwh (npwh NWH_4903) S0_4913 S_4914 :- nwh NWH_4903 S0_4913 S_4914.
npwh (npwh which OptAP_5120 N_5119) (which :: K_5335) S_5131 :- (optap OptAP_5120 K_5335 S1_5436 , n N_5119 S1_5436 S_5131).
apwh (apwh AWH_5889) S0_5899 S_5900 :- awh AWH_5889 S0_5899 S_5900.
ppwh (ppwh PWH_6105) S0_6115 S_6116 :- pwh PWH_6105 S0_6115 S_6116.
sbar (sbar that S_6321) (that :: K_6536) S_6332 :- sent S_6321 K_6536 S_6332.
qbar (qbar NPWH_6831 VP_6830) S0_6841 S_6842 :- (npwh NPWH_6831 S0_6841 S1_6917 , vp VP_6830 S1_6917 S_6842).
qbar (qbar NPWH_7308 S_7307) S0_7318 S_7319 :- (npwh NPWH_7308 S0_7318 S1_7394 , np (np gap) -o sent S_7307 S1_7394 S_7319).
np (np PNposs_7849) S0_7859 S_7860 :- pnposs PNposs_7849 S0_7859 S_7860.
np (np Det_8068 Nposs_8067 OptPP_8066 OptRel_8065) S0_8078 S_8079 :- (det Det_8068 S0_8078 S1_8154 , nposs Nposs_8067 S1_8154 S1_8348 , optpp OptPP_8066 S1_8348 S1_8542 , optrel OptRel_8065 S1_8542 S_8079).
pnposs (pnposs PN_9064) S0_9074 S_9075 :- pn PN_9064 S0_9074 S_9075.
pnposs (pnposs PN_9281 s Nposs_9280) S0_9291 S_9292 :- (pn PN_9281 S0_9291 (s :: K_9690) , nposs Nposs_9280 K_9690 S_9292).
nposs (nposs OptAP_10051 N_10050) S0_10061 S_10062 :- (optap OptAP_10051 S0_10061 S1_10137 , n N_10050 S1_10137 S_10062).
nposs (nposs OptAP_10529 N_10528 s Nposs_10527) S0_10539 S_10540 :- (optap OptAP_10529 S0_10539 S1_10615 , n N_10528 S1_10615 (s :: K_11132) , nposs Nposs_10527 K_11132 S_10540).
vp (vp DV_11560 NP_11559 PP_11558) S0_11570 S_11571 :- (dv DV_11560 S0_11570 S1_11646 , np NP_11559 S1_11646 S1_11840 , pp PP_11558 S1_11840 S_11571).
vp (vp TV_12297 NP_12296) S0_12307 S_12308 :- (tv TV_12297 S0_12307 S1_12383 , np NP_12296 S1_12383 S_12308).
vp (vp IV_12774 OptPP_12773) S0_12784 S_12785 :- (iv IV_12774 S0_12784 S1_12860 , optpp OptPP_12773 S1_12860 S_12785).
vp (vp Stv_13251 Sbar_13250) S0_13261 S_13262 :- (stv Stv_13251 S0_13261 S1_13337 , sbar Sbar_13250 S1_13337 S_13262).
vp (vp TV_13729 NP_13728 Sbar_13727) S0_13739 S_13740 :- (tv TV_13729 S0_13739 S1_13815 , np NP_13728 S1_13815 S1_14009 , sbar Sbar_13727 S1_14009 S_13740).
vp (vp Qv_14466 Qbar_14465) S0_14476 S_14477 :- (qv Qv_14466 S0_14476 S1_14552 , qbar Qbar_14465 S1_14552 S_14477).
vp (vp Vfa_14943 VP_14942) S0_14953 S_14954 :- (vfa Vfa_14943 S0_14953 S1_15029 , vp VP_14942 S1_15029 S_14954).
vp (vp Vfa_15420 AP_15419) S0_15430 S_15431 :- (vfa Vfa_15420 S0_15430 S1_15506 , ap AP_15419 S1_15506 S_15431).
optpp (optpp epsilon) S0_15905 S0_15905.
optpp (optpp PP_16076) S0_16086 S_16087 :- pp PP_16076 S0_16086 S_16087.
pp (pp P_16293 NP_16292) S0_16303 S_16304 :- (p P_16293 S0_16303 S1_16379 , np NP_16292 S1_16379 S_16304).
optap (optap epsilon) S0_16778 S0_16778.
optap (optap AP_16949) S0_16959 S_16960 :- ap AP_16949 S0_16959 S_16960.
ap (ap A_17165) S0_17175 S_17176 :- a A_17165 S0_17175 S_17176.
optrel (optrel epsilon) S0_17390 S0_17390.
optrel (optrel Rel_17561) S0_17571 S_17572 :- rel Rel_17561 S0_17571 S_17572.
rel (rel that VP_17777) (that :: K_17992) S_17788 :- {vp VP_17777 K_17992 S_17788}.
rel (rel who VP_18314) (who :: K_18529) S_18325 :- {vp VP_18314 K_18529 S_18325}.
rel (rel that S_18851) (that :: K_19066) S_18862 :- {np (np gap) -o sent S_18851 K_19066 S_18862}.
rel (rel whom S_19453) (whom :: K_19668) S_19464 :- {np (np gap) -o sent S_19453 K_19668 S_19464}.
rel (rel P_20056 whom S_20055) S0_20066 S_20067 :- (p P_20056 S0_20066 (whom :: K_20465) , {pp (pp gap) -o sent S_20055 K_20465 S_20067}).
rel (rel P_20919 which S_20918) S0_20929 S_20930 :- (p P_20919 S0_20929 (which :: K_21328) , {pp (pp gap) -o sent S_20918 K_21328 S_20930}).
det (det H_21998) (H_21998 :: S_21793) S_21793 :- det H_21998 Agree_21781.
det the (pair third Num_22165).
det a (pair third sing).
det some (pair third plur).
det every (pair third sing).
det all (pair third plur).
nwh (nwh H_22482) (H_22482 :: S_22277) S_22277 :- nwh H_22482.
nwh who.
nwh what.
nwh which.
awh (awh H_22925) (H_22925 :: S_22720) S_22720 :- awh H_22925.
awh how.
pwh (pwh H_23328) (H_23328 :: S_23123) S_23123 :- pwh H_23328.
pwh where.
n (n H_23732) (H_23732 :: S_23527) S_23527 :- n H_23732 Agree_23515.
n man (pair third sing).
n woman (pair third sing).
n girl (pair third sing).
n boy (pair third sing).
n author (pair third sing).
n book (pair third sing).
n professor (pair third sing).
n program (pair third sing).
n programmer (pair third sing).
n student (pair third sing).
n computer (pair third sing).
n men (pair third plur).
n women (pair third plur).
n girls (pair third plur).
n boys (pair third plur).
n authors (pair third plur).
n books (pair third plur).
n professors (pair third plur).
n programs (pair third plur).
n programmers (pair third plur).
n students (pair third plur).
n computers (pair third plur).
n fish (pair third Num_24339).
pn (pn H_24577) (H_24577 :: S_24372) S_24372 :- pn H_24577 Agree_24360.
pn rufus (pair third sing).
pn dale (pair third sing).
pn eva (pair third sing).
pn josh (pair third sing).
pn elizabeth (pair third sing).
pn steven (pair third sing).
pn catherine (pair third sing).
pn mary (pair third sing).
pn bob (pair third sing).
pn jill (pair third sing).
pn bill (pair third sing).
pn jane (pair third sing).
pn john (pair third sing).
pn sally (pair third sing).
pn i (pair first sing).
pn you (pair second Num_25044).
pn he (pair third sing).
pn she (pair third sing).
pn it (pair third sing).
pn we (pair first plur).
pn they (pair third plur).
tv (tv H_25382) (H_25382 :: S_25177) S_25177 :- tv H_25382 Agree_25165.
tv love (pair first sing).
tv love (pair second sing).
tv love (pair Person_25589 plur).
tv loves (pair third sing).
tv loved (pair Person_25631 Num_25630).
tv marry (pair first sing).
tv marry (pair second sing).
tv marry (pair Person_25692 plur).
tv marries (pair third sing).
tv married (pair Person_25734 Num_25733).
tv concern (pair first sing).
tv concern (pair second sing).
tv concern (pair Person_25795 plur).
tv concerns (pair third sing).
tv concerned (pair Person_25837 Num_25836).
tv meet (pair first sing).
tv meet (pair second sing).
tv meet (pair Person_25898 plur).
tv meets (pair third sing).
tv met (pair Person_25940 Num_25939).
tv write (pair first sing).
tv write (pair second sing).
tv write (pair Person_26001 plur).
tv writes (pair third sing).
tv wrote (pair Person_26043 Num_26042).
tv told (pair P_26065 N_26064).
tv saw (pair P_26087 N_26086).
tv sees (pair P_26109 N_26108).
iv (iv H_26347) (H_26347 :: S_26142) S_26142 :- iv H_26347 Agree_26130.
iv run (pair first sing).
iv run (pair second sing).
iv run (pair Person_26554 plur).
iv runs (pair third sing).
iv ran (pair Person_26596 Num_26595).
iv halt (pair first sing) iv halt (pair second sing).
iv halt (pair Person_26637 plur).
iv halts (pair third sing).
iv halted (pair Person_26679 Num_26678).
dv (dv H_26917) (H_26917 :: S_26712) S_26712 :- dv H_26917 Agree_26700.
dv meet (pair first sing).
dv meet (pair second sing).
dv meet (pair Person_27124 plur).
dv meets (pair third sing).
dv met (pair Person_27166 Num_27165).
dv write (pair first sing).
dv write (pair second sing).
dv write (pair Person_27227 plur).
dv writes (pair third sing).
dv wrote (pair Person_27269 Num_27268).
dv written (pair P_27291 N_27290).
dv give (pair first sing).
dv give (pair second sing).
dv give (pair Person_27352 plur).
dv gives (pair third sing).
dv gave (pair Person_27394 Num_27393).
stv (stv H_27632) (H_27632 :: S_27427) S_27427 :- stv H_27632 Agree_27415.
stv believe (pair first sing).
stv believe (pair second sing).
stv believe (pair Person_27839 plur).
stv believes (pair third sing).
stv believed (pair Person_27881 Num_27880).
stv think (pair first sing).
stv think (pair second sing).
stv think (pair Person_27942 plur).
stv thinks (pair third sing).
stv thought (pair Person_27984 Num_27983).
qv (qv H_28221) (H_28221 :: S_28016) S_28016 :- qv H_28221.
qv wondered.
qv wonders.
qv asks.
qv asked.
vfa (vfa H_28684) (H_28684 :: S_28479) S_28479 :- vfa H_28684.
vfa is.
vfa did.
vfa was.
vfa would.
a (a H_29147) (H_29147 :: S_28942) S_28942 :- a H_29147.
a tall.
a stupid.
a short.
a smart.
p (p H_29610) (H_29610 :: S_29405) S_29405 :- p H_29610.
p with.
p about.
p to.
p under.
p above.
p on.
