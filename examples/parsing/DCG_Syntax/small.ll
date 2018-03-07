MODULE small.
parse Str_135 Tree_133 :- (explode_words Str_135 Lst_134 , sent Tree_133 Lst_134 nil).
sent (sent N_179 V_178) S0_200 S_201 :- ({np N_179 S0_200 S1_309} , vp V_178 S1_309 S_201).
vp (vp T_805 N_804) S0_826 S_827 :- (tv T_805 S0_826 S1_935 , np N_804 S1_935 S_827).
vp (vp Stv_1392 Sbar_1391) S0_1413 S_1414 :- (stv Stv_1392 S0_1413 S1_1522 , sbar Sbar_1391 S1_1522 S_1414).
sbar (sbar that S_1978) (that :: K_2182) S_2000 :- sent S_1978 K_2182 S_2000.
np (np D_2455 N_2454) S0_2476 S_2477 :- (det D_2455 S0_2476 S1_2585 , n N_2454 S1_2585 S_2477).
np (np D_3043 N_3042 R_3041) S0_3064 S_3065 :- (det D_3043 S0_3064 S1_3173 , n N_3042 S1_3173 S1_3400 , rel R_3041 S1_3400 S_3065).
np (np P_3933) S0_3954 S_3955 :- pn P_3933 S0_3954 S_3955.
rel (rel whom S_4215) (whom :: K_4419) S_4237 :- ((forall S0_4504 \ np (np gap) S0_4504 S0_4504) -o sent S_4215 K_4419 S_4237).
det (det the) (the :: K_5059) K_5059.
n (n H_5284) (H_5284 :: S_5101) S_5101 :- n H_5284.
n man.
n woman.
n girl.
n boy.
pn (pn H_5791) (H_5791 :: S_5608) S_5608 :- pn H_5791.
pn mary.
pn bob.
pn jill.
tv (tv H_6256) (H_6256 :: S_6073) S_6073 :- tv H_6256.
tv loves.
tv married.
stv (stv believes) (believes :: K_6628) K_6628.
