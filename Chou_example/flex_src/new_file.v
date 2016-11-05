==29495== Memcheck, a memory error detector
==29495== Copyright (C) 2002-2015, and GNU GPL'd, by Julian Seward et al.
==29495== Using Valgrind-3.12.0.SVN and LibVEX; rerun with -h for copyright info
==29495== Command: ./trad ../Chou\ -\ full-angles\ 110\ examples.txt
==29495== 
Lemma fa_l0 : forall A B C D E F G: FA_Point,
FA_P_foot  D C A B ->FA_P_foot  E B A C ->FA_P_midp  F B C ->FA_P_midp  G D E ->
FA_P_perp  F G D E .
Lemma fa_l1 : forall A B C A1 B1 C1 O: FA_Point,
FA_P_midp  A1 B C ->FA_P_midp  B1 A C ->FA_P_midp  C1 A B ->FA_P_circum  O A B C ->
FA_P_perp  O A1 B1 C1 .
Lemma fa_l2 : forall A B C D E F H A1 P Q: FA_Point,
FA_P_foot  D A B C ->FA_P_foot  E B A C ->FA_P_foot  F C A B ->FA_P_col  H A D ->FA_P_col  H B E ->FA_P_col  H C F ->FA_P_midp  A1 B C ->FA_P_midp  P B E ->FA_P_midp  Q C F ->
FA_P_cycl  P Q H D .
Lemma fa_l3 : forall A B C D O Q S J M: FA_Point,
FA_P_circum  O A B C D ->FA_P_col  I A D ->FA_P_col  I B C ->FA_P_midp  Q B C ->FA_P_midp  S A D ->FA_P_midp  J S Q ->FA_P_midp  J O M ->
FA_P_perp  S M B C .
Lemma fa_l4 : forall A B C E F H: FA_Point,
FA_P_foot  E B A C ->FA_P_foot  F A B C ->FA_P_col  H A F ->FA_P_col  H B E ->
FA_P_perp  A B C H .
Lemma fa_l5 : forall O A B C D E F G: FA_Point,
FA_P_cong  O A O B ->FA_P_cong  O A O C ->FA_P_cong  O A O D ->FA_P_col  E B C ->FA_P_perp  E D B C ->FA_P_col  F A C ->FA_P_perp  F D A C ->FA_P_col  G A B ->FA_P_perp  G D A B ->
FA_P_col  G F E .
Lemma fa_l6 : forall A B C P P1 G G1 F F1 K: FA_Point,
FA_P_cycl  A B C P P1 ->FA_P_foot  G P A B ->FA_P_foot  F P A C ->FA_P_foot  G1 P1 A B ->FA_P_foot  F1 P1 A C ->FA_P_col  K F G ->FA_P_col  K F1 G1 ->
FA_P_eqangle  P A P1 F1 K F .
Lemma fa_l7 : forall A B C D E Q P: FA_Point,
FA_P_cycl  A B E Q ->FA_P_cycl  C D E Q ->FA_P_col  A B P ->FA_P_col  C D P ->FA_P_col  B C E ->FA_P_col  A D E ->
FA_P_cycl  D A P Q .
Lemma fa_l8 : forall A B C D L M N: FA_Point,
FA_P_midp  M B C ->FA_P_midp  N A C ->FA_P_midp  L A B ->FA_P_foot  D A B C ->
FA_P_cycl  L D M N .
Lemma fa_l9 : forall A B C D E F H G: FA_Point,
FA_P_para  D A B C ->FA_P_para  D C A B ->FA_P_foot  E B A C ->FA_P_foot  F A B D ->FA_P_foot  H C B D ->FA_P_foot  G D A C ->
FA_P_para  E F H G .
Lemma fa_l10 : forall C E F Q D I P A: FA_Point,
FA_P_circum  Q C E F D ->FA_P_midp  Q C D ->FA_P_midp  I E F ->FA_P_col  P I Q ->FA_P_perp  P E E Q ->FA_P_col  A C E ->FA_P_cong  A P P E ->
FA_P_col  A D F .
Lemma fa_l11 : forall A B C F D E G I H K: FA_Point,
FA_P_foot  F C A B ->FA_P_foot  D A B C ->FA_P_foot  E B A C ->FA_P_foot  G F B C ->FA_P_foot  I D A B ->FA_P_foot  H F A C ->FA_P_foot  K E A B ->
FA_P_cycl  H I G K .
Lemma fa_l12 : forall A C K N O B M: FA_Point,
FA_P_circum  O A C K N ->FA_P_col  B A K ->FA_P_col  B C N ->FA_P_cycl  M A B C ->FA_P_cycl  M B K N ->
FA_P_cycl  K O C M .
Lemma fa_l13 : forall A C K N O B M: FA_Point,
FA_P_circum  O A C K N ->FA_P_col  B A K ->FA_P_col  B C N ->FA_P_cycl  K O C M ->FA_P_cycl  M A B C ->FA_P_cycl  M B K N ->
FA_P_perp  B M M O .
Lemma fa_l14 : forall A B C D E F: FA_Point,
FA_P_cycl  A B C D ->FA_P_cycl  A B E F ->FA_P_col  A C E ->FA_P_col  B D F ->
FA_P_para  C D E F .
Lemma fa_l15 : forall A B C D E H G: FA_Point,
FA_P_foot  E B A C ->FA_P_foot  D A B C ->FA_P_col  H E B ->FA_P_col  H A D ->FA_P_foot  G H A B ->
FA_P_eqangle  D G H H G E .
Lemma fa_l16 : forall A B C H O P Q R: FA_Point,
FA_P_orthoc  H A B C ->FA_P_circum  O A B C ->FA_P_circum  R B C H ->FA_P_circum  P A C H ->FA_P_circum  Q A B H ->
FA_P_para  P C Q B .
Lemma fa_l17 : forall A B C H O P Q R: FA_Point,
FA_P_orthoc  H A B C ->FA_P_circum  O A B C ->FA_P_circum  R B C H ->FA_P_circum  P A C H ->FA_P_circum  Q A B H ->
FA_P_pbisector  H P Q .
Lemma fa_l18 : forall A B C F H P Q T: FA_Point,
FA_P_foot  F C A B ->FA_P_col  H C F ->FA_P_perp  H A B C ->FA_P_perp  H B A C ->FA_P_foot  P F A C ->FA_P_foot  Q F A H ->FA_P_foot  T F B C ->
FA_P_col  P Q T .
Lemma fa_l19 : forall A B C D P Q: FA_Point,
FA_P_foot  D A B C ->FA_P_foot  P D A C ->FA_P_foot  Q D A B ->
FA_P_cycl  P B Q C .
Lemma fa_l20 : forall A B C E F O: FA_Point,
FA_P_circum  O A B C ->FA_P_foot  E B A C ->FA_P_foot  F C A B ->
FA_P_perp  O A E F .
Lemma fa_l21 : forall A B C O B1 C1 P Q: FA_Point,
FA_P_circum  O A B C ->FA_P_midp  C1 A B ->FA_P_midp  B1 A C ->FA_P_col  P O C1 ->FA_P_col  Q O B1 ->FA_P_col  P A C ->FA_P_col  Q A B ->
FA_P_cycl  B C P Q .
Lemma fa_l22 : forall B C R S O A M N: FA_Point,
FA_P_circum  O B C R ->FA_P_cong  O B O S ->FA_P_col  A R B ->FA_P_col  A S C ->FA_P_foot  M A R S ->FA_P_foot  N A B C ->
FA_P_eqangle  B A M N A C .
Lemma fa_l23 : forall A B C D I E F: FA_Point,
FA_P_cycl  A B C D ->FA_P_col  I A B ->FA_P_col  I C D ->FA_P_perp  E D D C ->FA_P_perp  E A A B ->FA_P_perp  F B B A ->FA_P_perp  F C C D ->
FA_P_eqangle  A I E F I C .
Lemma fa_l24 : forall A B C H O P: FA_Point,
FA_P_orthoc  H A B C ->FA_P_circum  O B C H ->FA_P_perp  P H H C ->FA_P_cong  P O O B ->
FA_P_para  A H B P .
Lemma fa_l25 : forall A B C O D E H K: FA_Point,
FA_P_circum  O A B C ->FA_P_foot  D C A B ->FA_P_foot  E B A C ->FA_P_col  H B E ->FA_P_col  H C D ->FA_P_col  K C D ->FA_P_cong  K O A O ->
FA_P_pbisector  A H K .
Lemma fa_l26 : forall A B C O D E H O1: FA_Point,
FA_P_circum  O A B C ->FA_P_foot  D C A B ->FA_P_foot  E B A C ->FA_P_col  H B E ->FA_P_col  H C D ->FA_P_circum  O1 A B H ->
FA_P_pbisector  A O O1 .
Lemma fa_l27 : forall A B C O H A1 C1: FA_Point,
FA_P_circum  O A B C ->FA_P_orthoc  H A B C ->FA_P_col  A1 A H ->FA_P_cong  O A O A1 ->FA_P_col  C1 C H ->FA_P_cong  O A O C1 ->
FA_P_pbisector  B A1 C1 .
Lemma fa_l28 : forall A B C I M L1: FA_Point,
FA_P_incenter  I A B C ->FA_P_cycl  A B C M L1 ->FA_P_col  M I C ->FA_P_perp  B L1 B I ->
FA_P_para  M L1 A I .
Lemma fa_l29 : forall A B C I M: FA_Point,
FA_P_incenter  I A B C ->FA_P_col  M A C ->FA_P_para  I M A B ->
FA_P_pbisector  M A I .
Lemma fa_l30 : forall A B C I X Y L: FA_Point,
FA_P_incenter  I A B C ->FA_P_foot  X I B C ->FA_P_foot  Y I A C ->FA_P_foot  L B A I ->
FA_P_col  X Y L .
Lemma fa_l31 : forall A B C I A1 X X1 Y D: FA_Point,
FA_P_incenter  I A B C ->FA_P_midp  A1 B C ->FA_P_foot  X B A I ->FA_P_midp  X B X1 ->FA_P_col  X1 A C ->FA_P_foot  Y C A I ->FA_P_foot  D A B C ->
FA_P_cycl  X Y D A1 .
Lemma fa_l32 : forall A B C P: FA_Point,
FA_P_perp  C A C B ->FA_P_perp  P A P B ->FA_P_cong  P A P B ->
FA_P_eqangle  A C P P C B .
Lemma fa_l33 : forall A B C D A1 C1: FA_Point,
FA_P_cycl  A B C D ->FA_P_col  A1 C D ->FA_P_perp  A1 A A B ->FA_P_col  C1 A B ->FA_P_perp  C1 C C D ->
FA_P_para  A1 C1 B D .
Lemma fa_l34 : forall A B C D O I Q S J M: FA_Point,
FA_P_circum  O A B C D ->FA_P_col  I A D ->FA_P_col  I B C ->FA_P_midp  Q B C ->FA_P_midp  S A D ->FA_P_midp  J S Q ->FA_P_midp  J O M ->
FA_P_perp  I M Q S .
Lemma fa_l35 : forall A B C D E P Q S R: FA_Point,
FA_P_cycl  A B C D E ->FA_P_foot  P E A B ->FA_P_foot  Q E B C ->FA_P_foot  R E C D ->FA_P_foot  S E A D ->
FA_P_eqangle  E P S E Q R .
Lemma fa_l36 : forall A B C D U V: FA_Point,
FA_P_cycl  A B C D ->FA_P_orthoc  U A B D ->FA_P_orthoc  V A C D ->
FA_P_cycl  U V A D .
Lemma fa_l37 : forall A B C D E I: FA_Point,
FA_P_cycl  A B C D ->FA_P_col  E A C ->FA_P_col  E B D ->FA_P_circum  I A B E ->
FA_P_perp  I E C D .
Lemma fa_l38 : forall A B C D P Q S R O: FA_Point,
FA_P_perp  A C B D ->FA_P_midp  P A B ->FA_P_midp  Q B C ->FA_P_midp  S A D ->FA_P_midp  R C D ->FA_P_col  O P R ->FA_P_col  O Q S ->
FA_P_pbisector  O S R .
Lemma fa_l39 : forall A B C D O M P R: FA_Point,
FA_P_circum  O A B C D ->FA_P_perp  A C B D ->FA_P_col  M A C ->FA_P_col  M B D ->FA_P_midp  P A B ->FA_P_midp  R C D ->
FA_P_para  O P R M .
Lemma fa_l40 : forall A B C D O E: FA_Point,
FA_P_circum  O A B C D E ->FA_P_perp  A C B D ->FA_P_col  E D O ->
FA_P_para  B E A C .
Lemma fa_l41 : forall C D E O A F: FA_Point,
FA_P_perp  C E D E ->FA_P_midp  O C D ->FA_P_perp  A C C D ->FA_P_perp  A E E O ->FA_P_col  F A C ->FA_P_col  F D E ->
FA_P_pbisector  A E F .
Lemma fa_l42 : forall O A B C E D: FA_Point,
FA_P_cong  O A O B ->FA_P_col  C A B ->FA_P_perp  E B B O ->FA_P_perp  E C C O ->FA_P_perp  D A A O ->FA_P_col  E C D ->
FA_P_pbisector  O E D .
Lemma fa_l43 : forall A B C G O M D E F: FA_Point,
FA_P_perp  B A A C ->FA_P_midp  O B C ->FA_P_foot  D A B C ->FA_P_foot  M B A O ->FA_P_col  E B M ->FA_P_col  E A D ->FA_P_col  F A C ->FA_P_col  F B M ->
FA_P_pbisector  E A B .
Lemma fa_l44 : forall A B C G O M D E F: FA_Point,
FA_P_perp  B A A C ->FA_P_midp  O B C ->FA_P_foot  D A B C ->FA_P_foot  M B A O ->FA_P_col  E B M ->FA_P_col  E A D ->FA_P_col  F A C ->FA_P_col  F B M ->
FA_P_pbisector  E F A .
Lemma fa_l45 : forall A B M O D E: FA_Point,
FA_P_cong  M A M B ->FA_P_cong  O A O M ->FA_P_cong  O A O B ->FA_P_midp  D A B ->FA_P_col  M O D ->FA_P_perp  E A A O ->FA_P_para  M E A O ->
FA_P_pbisector  M E D .
Lemma fa_l46 : forall A B C D O E F: FA_Point,
FA_P_foot  D A B C ->FA_P_midp  O A D ->FA_P_col  E A B ->FA_P_cong  O A O E ->FA_P_col  F A C ->FA_P_cong  O A O F ->
FA_P_cycl  B C E F .
Lemma fa_l47 : forall A B C D E F: FA_Point,
FA_P_cycl  A B C D ->FA_P_col  E A B ->FA_P_col  E C D ->FA_P_col  F B C ->FA_P_para  F E A D ->
FA_P_eqangle  F E B E C B .
Lemma fa_l48 : forall A B C O M N: FA_Point,
FA_P_circum  O A B C ->FA_P_midp  M A B ->FA_P_col  N M O ->FA_P_cong  O A O N ->
FA_P_eqangle  A C N N C B .
Lemma fa_l49 : forall A B C O D E F N K: FA_Point,
FA_P_circum  O A B C ->FA_P_midp  D B C ->FA_P_midp  E A C ->FA_P_midp  F A B ->FA_P_col  N O F ->FA_P_cong  O A O N ->FA_P_foot  K N A C ->
FA_P_eqangle  E F K K F D .
Lemma fa_l50 : forall A B C O X D O1: FA_Point,
FA_P_circum  O A B C ->FA_P_midp  X A B ->FA_P_cong  O1 A O1 B ->FA_P_col  O1 X O ->FA_P_col  D B C ->FA_P_cong  D O1 O1 A ->
FA_P_eqangle  A O O1 A C D .
Lemma fa_l51 : forall D A B C E F G: FA_Point,
FA_P_cycl  A B C D ->FA_P_perp  E A E D ->FA_P_perp  E B E D ->FA_P_perp  F A F D ->FA_P_perp  F C F D ->FA_P_perp  G C G D ->FA_P_perp  G B G D ->
FA_P_col  E F G .
Lemma fa_l52 : forall P A1 B1 C1 A B C: FA_Point,
FA_P_circum  A P B1 C1 ->FA_P_circum  B P A1 C1 ->FA_P_circum  C P B1 A1 ->FA_P_col  A1 B1 C1 ->
FA_P_cycl  P A B C .
Lemma fa_l53 : forall E F M B D A E1 F1: FA_Point,
FA_P_circum  B E F M ->FA_P_midp  D E F ->FA_P_col  A D B ->FA_P_col  E1 M E ->FA_P_cong  E1 A E A ->FA_P_col  F1 M F ->FA_P_cong  F1 A E A ->
FA_P_perp  E1 F1 M B .
Lemma fa_l54 : forall A B C O D E N: FA_Point,
FA_P_circum  O A B C ->FA_P_col  D A B ->FA_P_col  E A C ->FA_P_para  D E B C ->FA_P_circum  N A D E ->
FA_P_col  A N O .
Lemma fa_l55 : forall A B C I H N M: FA_Point,
FA_P_foot  I C A B ->FA_P_col  H C I ->FA_P_perp  H A B C ->FA_P_midp  M C B ->FA_P_midp  N A H ->
FA_P_perp  M I N I .
Lemma fa_l56 : forall A B C I O B1 C1 M: FA_Point,
FA_P_incenter  I A B C ->FA_P_circum  O B C I ->FA_P_col  B1 B I ->FA_P_perp  B1 C C I ->FA_P_col  C1 C I ->FA_P_perp  C1 B B I ->FA_P_midp  M B1 C1 ->
FA_P_perp  M B O B .
Lemma fa_l57 : forall P D I A E X B G F: FA_Point,
FA_P_circum  A P D I E ->FA_P_midp  A D E ->FA_P_midp  X P I ->FA_P_col  B A X ->FA_P_perp  B P A P ->FA_P_col  E I G ->FA_P_cong  G B P B ->FA_P_midp  B G F ->
FA_P_perp  F G D E .
Lemma fa_l58 : forall A B M O I J: FA_Point,
FA_P_perp  A M B M ->FA_P_midp  O A B ->FA_P_circum  I O A M ->FA_P_circum  J O B M ->
FA_P_perp  I M M J .
Lemma fa_l59 : forall A B A1 O B1 P O1: FA_Point,
FA_P_circum  O A B A1 B1 ->FA_P_midp  O A B ->FA_P_col  P A A1 ->FA_P_col  P B B1 ->FA_P_circum  O1 P A1 B1 ->
FA_P_perp  O1 A1 O A1 .
Lemma fa_l60 : forall A B C D O F G: FA_Point,
FA_P_circum  O A B C D ->FA_P_para  D A B C ->FA_P_foot  G D A B ->FA_P_foot  F D A C ->
FA_P_para  G F O A .
Lemma fa_l61 : forall A B C D O F G: FA_Point,
FA_P_circum  O A B C D ->FA_P_foot  G D A B ->FA_P_foot  F D A C ->
FA_P_sim  D F G D C B .
Lemma fa_l62 : forall A B C D O F G L: FA_Point,
FA_P_circum  O A B C D ->FA_P_foot  G D A B ->FA_P_foot  F D A C ->FA_P_col  L D G ->FA_P_cong  L O O A ->
FA_P_para  C L F G .
Lemma fa_l63 : forall A B C O G D E F: FA_Point,
FA_P_circum  O A B C ->FA_P_foot  G C A B ->FA_P_col  D C G ->FA_P_cong  D O O A ->FA_P_foot  E D A C ->FA_P_foot  F D B C ->
FA_P_cycl  A B E F .
Lemma fa_l64 : forall A B C O1 O O2 D I: FA_Point,
FA_P_circum  O1 A B C ->FA_P_midp  O A B ->FA_P_col  O1 O2 O ->FA_P_col  D A C ->FA_P_cong  O2 A O2 D ->FA_P_col  O1 C I ->FA_P_col  O2 D I ->
FA_P_eqangle  C B D O1 I O2 .
Lemma fa_l65 : forall B C A O E D: FA_Point,
FA_P_cong  A B A C ->FA_P_cong  B C B A ->FA_P_pbisector  O A B ->FA_P_pbisector  O C B ->FA_P_pbisector  O E B ->FA_P_col  A E D ->FA_P_col  B C D ->
FA_P_sim  E D C E B A .
Lemma fa_l66 : forall B A C I O H K: FA_Point,
FA_P_incenter  I A B C ->FA_P_perp  B O A B ->FA_P_pbisector  O B I ->FA_P_pbisector  O B H ->FA_P_col  A C H ->FA_P_col  A C K ->FA_P_pbisector  O B K ->
FA_P_eqangle  H I C C I K .
Lemma fa_l67 : forall A B C O G E K H N: FA_Point,
FA_P_circum  O B A C ->FA_P_midp  G B C ->FA_P_col  G O E ->FA_P_pbisector  O B E ->FA_P_perp  K E A B ->FA_P_col  K A B ->FA_P_perp  A H O G ->FA_P_col  H O G ->FA_P_circum  N G H K ->
FA_P_perp  E K K N .
Lemma fa_l68 : forall A B C O D F: FA_Point,
FA_P_pbisector  O A B ->FA_P_pbisector  O A C ->FA_P_col  A B D ->FA_P_perp  A B C D ->FA_P_col  F A B ->FA_P_eqangle  A C F F C B ->
FA_P_eqangle  D C F F C O .
Lemma fa_l69 : forall A B C O U T: FA_Point,
FA_P_pbisector  O B C ->FA_P_pbisector  O B A ->FA_P_eqangle  B A U U A C ->FA_P_col  B U C ->FA_P_perp  O A A T ->FA_P_col  B C T ->
FA_P_pbisector  T A U .
Lemma fa_l70 : forall U V A B C O P Q: FA_Point,
FA_P_perp  A U A V ->FA_P_cong  A U A V ->FA_P_col  U V B ->FA_P_eqangle  C A U U A B ->FA_P_col  U V C ->FA_P_midp  O B C ->FA_P_col  A B P ->FA_P_col  A C Q ->FA_P_pbisector  O B Q ->FA_P_pbisector  O B P ->
FA_P_pbisector  C P Q .
Lemma fa_l71 : forall A B C O I E J L: FA_Point,
FA_P_incenter  O A B C ->FA_P_foot  I C A O ->FA_P_perp  E A O A ->FA_P_foot  J C A E ->FA_P_foot  L C B O ->
FA_P_col  I J L .
Lemma fa_l72 : forall B C A A1 B1 C1 N K J: FA_Point,
FA_P_midp  A1 B C ->FA_P_midp  C1 B A ->FA_P_midp  B1 A C ->FA_P_pbisector  N A1 B1 ->FA_P_pbisector  N A1 C1 ->FA_P_perp  A1 K A1 N ->FA_P_col  A C K ->FA_P_col  K A1 J ->FA_P_col  A B J ->
FA_P_cycl  K J B C .
Lemma fa_l73 : forall A B C O U I: FA_Point,
FA_P_pbisector  O A B ->FA_P_pbisector  O B C ->FA_P_eqangle  B A U U A C ->FA_P_col  B C U ->FA_P_pbisector  I A U ->FA_P_col  I O A ->
FA_P_perp  I U B C .
Lemma fa_l74 : forall A B C A1 B1 C1 A2 C2: FA_Point,
FA_P_midp  A B1 C ->FA_P_midp  A C1 B ->FA_P_midp  B A1 C ->FA_P_eqangle  A B A2 A2 B C ->FA_P_col  B1 C1 A2 ->FA_P_col  B A2 C2 ->FA_P_col  A1 B1 C2 ->
FA_P_pbisector  B1 A2 C2 .
Lemma fa_l75 : forall O X Y L A B P Q P1 Q1 I: FA_Point,
FA_P_perp  L A O X ->FA_P_col  A O X ->FA_P_perp  L B O Y ->FA_P_col  O B Y ->FA_P_midp  A L P ->FA_P_midp  B L Q ->FA_P_col  P1 L Q ->FA_P_col  O X P1 ->FA_P_col  Q1 L P ->FA_P_col  Q1 O Y ->
FA_P_cycl  O P Q P1 .
Lemma fa_l76 : forall B C A I A1 B1 C1 P Q N: FA_Point,
FA_P_incenter  I A B C ->FA_P_midp  P B I ->FA_P_midp  Q C I ->FA_P_pbisector  N A1 P ->FA_P_pbisector  N A1 Q ->FA_P_midp  A1 C B ->FA_P_midp  B1 C A ->FA_P_midp  C1 A B ->
FA_P_eqangle  B1 A1 N N A1 C1 .
Lemma fa_l77 : forall A B C D O F G C1 B1: FA_Point,
FA_P_pbisector  O A B ->FA_P_pbisector  O A C ->FA_P_pbisector  O A D ->FA_P_col  A B G ->FA_P_col  A C F ->FA_P_perp  A B D G ->FA_P_perp  A C D F ->FA_P_col  D G C1 ->FA_P_pbisector  O A C1 ->FA_P_col  D F B1 ->FA_P_pbisector  O A B1 ->
FA_P_para  C1 C B1 B .
Lemma fa_l78 : forall A B C O P P1 G G1 F F1 K: FA_Point,
FA_P_pbisector  O A B ->FA_P_pbisector  O A C ->FA_P_pbisector  O A P ->FA_P_pbisector  O A P1 ->FA_P_perp  P G A B ->FA_P_col  G A B ->FA_P_perp  P F A C ->FA_P_col  A C F ->FA_P_perp  P1 G1 A B ->FA_P_col  G1 A B ->FA_P_perp  P1 F1 A C ->FA_P_col  A C F1 ->FA_P_perp  K P F1 G1 ->FA_P_perp  K P1 F G ->
FA_P_cycl  P P1 A K .
Lemma fa_l79 : forall A B C O P P1 G G1 F F1 K: FA_Point,
FA_P_pbisector  O A B ->FA_P_pbisector  O A C ->FA_P_pbisector  O A P ->FA_P_pbisector  O A P1 ->FA_P_perp  P G A B ->FA_P_col  G A B ->FA_P_perp  P F A C ->FA_P_col  A C F ->FA_P_perp  P1 G1 A B ->FA_P_col  G1 A B ->FA_P_perp  P1 F1 A C ->FA_P_col  A C F1 ->FA_P_para  K P F1 G1 ->FA_P_para  K P1 F G ->
FA_P_cycl  P P1 A K .
Lemma fa_l80 : forall A B C D O D1 F G F1 G1 K A1 B1 C1 N: FA_Point,
FA_P_circum  O A B C D D1 ->FA_P_col  A B G ->FA_P_col  A C F ->FA_P_perp  A B D G ->FA_P_perp  A C D F ->FA_P_midp  O D D1 ->FA_P_col  A B G1 ->FA_P_col  A C F1 ->FA_P_perp  A B D1 G1 ->FA_P_perp  A C D1 F1 ->FA_P_col  G F K ->FA_P_col  G1 F1 K ->FA_P_midp  A1 C B ->FA_P_midp  B1 A C ->FA_P_midp  C1 A B ->FA_P_pbisector  N C1 A1 ->FA_P_pbisector  N C1 B1 ->FA_P_pbisector  N C1 K ->
FA_P_perp  F G F1 G1 .
Lemma fa_l81 : forall A B C D P O E F G H I: FA_Point,
FA_P_cycl  A B C D P ->FA_P_perp  P G A B ->FA_P_perp  P H B C ->FA_P_perp  P E C D ->FA_P_perp  P F D A ->FA_P_col  G A B ->FA_P_col  H B C ->FA_P_col  E C D ->FA_P_col  F D A ->FA_P_col  I G F ->FA_P_col  I E H ->
FA_P_cycl  G H P I .
Lemma fa_l82 : forall A B C O A1 S Q P: FA_Point,
FA_P_circum  O A B C P Q ->FA_P_midp  A1 B C ->FA_P_col  A A1 P ->FA_P_eqangle  B A S A1 A C ->FA_P_col  B S C ->FA_P_col  A S Q ->
FA_P_para  P Q B C .
Lemma fa_l83 : forall B C A A1 S N G H: FA_Point,
FA_P_midp  B A1 C ->FA_P_eqangle  B A S A1 A C ->FA_P_col  B S C ->FA_P_col  N A A1 ->FA_P_perp  N G A B ->FA_P_col  A G B ->FA_P_perp  N H A C ->FA_P_col  H A C ->
FA_P_perp  G H A S .
Lemma fa_l84 : forall A B C O A1 S Q P D G: FA_Point,
FA_P_circum  O A B C P Q ->FA_P_midp  A1 B C ->FA_P_col  A A1 P ->FA_P_eqangle  B A S A1 A C ->FA_P_col  B S C ->FA_P_col  A S Q ->FA_P_col  D B C ->FA_P_perp  Q D B C ->FA_P_col  A B G ->FA_P_perp  Q G A B ->
FA_P_perp  D G A P .
Lemma fa_l85 : forall A B C M N Q P: FA_Point,
FA_P_eqangle  B A M N A C ->FA_P_perp  M Q A B ->FA_P_col  Q A B ->FA_P_perp  M P A C ->FA_P_col  P A C ->
FA_P_perp  N A P Q .
Lemma fa_l86 : forall A B C M D F: FA_Point,
FA_P_cong  A C C B ->FA_P_cong  C B B A ->FA_P_midp  B A M ->FA_P_midp  M B D ->FA_P_foot  F D B C ->
FA_P_perp  C A A F .
Lemma fa_l87 : forall A B C O H D E: FA_Point,
FA_P_circum  O A B C ->FA_P_midp  H C B ->FA_P_col  D A B ->FA_P_col  D O H ->FA_P_perp  E A A O ->FA_P_perp  E C C O ->
FA_P_cycl  A O E D .
Lemma fa_l88 : forall A B C A1 B1 C1: FA_Point,
FA_P_cycl  A B C A1 B1 C1 ->FA_P_cong  A1 B A1 C ->FA_P_cong  B1 A B1 C ->FA_P_cong  C1 A C1 B ->
FA_P_perp  A A1 B1 C1 .
Lemma fa_l89 : forall A B C A1 B1 C1 A2 B2 C2: FA_Point,
FA_P_cycl  A B C A1 B1 C1 ->FA_P_cong  A1 B A1 C ->FA_P_cong  B1 A B1 C ->FA_P_cong  C1 A C1 B ->FA_P_foot  A2 A1 B1 C1 ->FA_P_foot  B2 B1 A1 C1 ->FA_P_foot  C2 C1 A1 B1 ->
FA_P_para  A B A2 B2 .
Lemma fa_l90 : forall A B C D E G F H: FA_Point,
FA_P_para  A D B C ->FA_P_midp  E A B ->FA_P_foot  G E C D ->FA_P_perp  A G B G ->FA_P_midp  F C D ->FA_P_foot  H F A B ->
FA_P_perp  C H H D .
Lemma fa_l91 : forall P Q A N D B C E: FA_Point,
FA_P_cycl  A B C D ->FA_P_cong  A P A Q ->FA_P_cong  A B A C ->FA_P_cong  D B D C ->FA_P_col  N A D ->FA_P_foot  P N A B ->FA_P_foot  Q N A C ->FA_P_circum  N D P Q ->FA_P_col  E P Q ->FA_P_col  E A D ->
FA_P_eqangle  A B E E B C .
Lemma fa_l92 : forall P0 P1 P2 P3 P4 Q0 Q1 Q2 Q3 Q4 M0 M1 M2 M3 M4: FA_Point,
FA_P_col  Q0 P1 P2 Q2 ->FA_P_col  Q1 P2 P3 Q3 ->FA_P_col  Q2 P3 P4 Q4 ->FA_P_col  Q3 P4 P0 Q0 ->FA_P_col  Q4 P0 P1 Q1 ->FA_P_cycl  M0 M1 Q0 P0 P1 ->FA_P_cycl  M0 M4 Q4 P0 P4 ->FA_P_cycl  M3 M4 Q3 P3 P4 ->FA_P_cycl  M3 M2 Q2 P2 P3 ->FA_P_cycl  M1 M2 Q1 P1 P2 ->
FA_P_cycl  M0 M1 M2 M4 .
Lemma fa_l93 : forall A B C D U V: FA_Point,
FA_P_cycl  A B C D ->FA_P_orthoc  U A B D ->FA_P_orthoc  V A C D ->
FA_P_para  U V B C .
Lemma fa_l94 : forall A B C P O D E F: FA_Point,
FA_P_midp  O A B ->FA_P_perp  A C C B ->FA_P_perp  A P P B ->FA_P_cong  O A O D ->FA_P_cong  C D C B ->FA_P_col  E A C ->FA_P_col  E P B ->FA_P_col  F A D ->FA_P_col  F P C ->
FA_P_perp  E F A D .
Lemma fa_l95 : forall A B D C E F M O1 O2 O3 O4: FA_Point,
FA_P_col  A B C ->FA_P_col  C D E ->FA_P_col  E F B ->FA_P_col  D F A ->FA_P_cycl  M A B F ->FA_P_cycl  M A C D ->FA_P_pbisector  O1 A B ->FA_P_pbisector  O1 A F ->FA_P_pbisector  O2 B C ->FA_P_pbisector  O2 B E ->FA_P_pbisector  O3 D F ->FA_P_pbisector  O3 D E ->FA_P_pbisector  O4 A C ->FA_P_pbisector  O4 A D ->
FA_P_cycl  O1 O2 O3 O4 .
Lemma fa_l96 : forall A B D C E F M O1 O2 O3 O4: FA_Point,
FA_P_col  A B C ->FA_P_col  C D E ->FA_P_col  E F B ->FA_P_col  D F A ->FA_P_cycl  M A B F ->FA_P_cycl  M A C D ->FA_P_pbisector  O1 A B ->FA_P_pbisector  O1 A F ->FA_P_pbisector  O2 B C ->FA_P_pbisector  O2 B E ->FA_P_pbisector  O3 D F ->FA_P_pbisector  O3 D E ->FA_P_pbisector  O4 A C ->FA_P_pbisector  O4 A D ->
FA_P_cycl  O1 O2 O3 M .
==29495== 
==29495== HEAP SUMMARY:
==29495==     in use at exit: 17,186 bytes in 15 blocks
==29495==   total heap usage: 866 allocs, 851 frees, 35,890 bytes allocated
==29495== 
==29495== LEAK SUMMARY:
==29495==    definitely lost: 0 bytes in 0 blocks
==29495==    indirectly lost: 0 bytes in 0 blocks
==29495==      possibly lost: 0 bytes in 0 blocks
==29495==    still reachable: 17,186 bytes in 15 blocks
==29495==         suppressed: 0 bytes in 0 blocks
==29495== Rerun with --leak-check=full to see details of leaked memory
==29495== 
==29495== For counts of detected and suppressed errors, rerun with: -v
==29495== ERROR SUMMARY: 0 errors from 0 contexts (suppressed: 0 from 0)
