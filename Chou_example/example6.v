Require Import full_angle.
(*Require Import forward_rules.*)

Section ex6.
  Generalizable Variables FA_Point Full_Angle FA_P_para FA_P_perp FA_P_col FA_P_med FA_P_cycl
                FA_P_circ FA_P_midp FA_P_to_FA FA_Zero FA_One FA_add
                FAMinus FAEq.
  Context `{FA_c:FA_Full_angle_ax FA_Point Full_Angle FA_P_para FA_P_perp FA_P_col
                               FA_P_med FA_P_cycl FA_P_circ FA_P_midp FA_P_to_FA
                               FA_Zero FA_One FA_add FAMinus FAEq }.

  (* currently need this *)
  Definition fp_Foot (O C A B : FA_Point) : Prop :=
    (FA_P_col O A B) /\ (FA_P_perp O C A B).

  Print FA_Full_angle_ax.

  Check FA_c.
  
  Lemma ex6 `{ FA_i : FA_Full_angle_ax FA_Point Full_Angle} : forall A B C E F H : FA_Point , A<>B -> C<>H ->
                fp_Foot E B A C -> fp_Foot F A B C ->
                FA_P_col H A F -> FA_P_col H B E ->
                FA_P_perp A B C H.
  Proof.
    intros A B C E F H.
    intros HAB HCH.
    intros H1 H2 H3 H4.
Check fa_rule_2.
    apply (fa_rule_2 FA_Point Full_Angle FA_P_para FA_P_perp FA_P_col FA_P_med FA_P_cycl
          FA_P_circ FA_P_midp FA_P_to_FA FA_Zero FA_One FA_add
          FAMinus FAEq  A B C H).
    assumption.
    assumption.    






(*
Conclusion: perp (a, b, c, h) .
  Lemma fa_l6 : forall A B C P P1 G G1 F F1 K: FA_Point,
                  FA_P_cycl  A B C P P1 ->FA_P_foot  G P A B ->FA_P_foot  F P A C
                  ->FA_P_foot  G1 P1 A B ->FA_P_foot  F1 P1 A C ->FA_P_col  K F G
                  ->FA_P_col  K F1 G1 ->
                  FA_P_eqangle  P A P1 F1 K F .*)