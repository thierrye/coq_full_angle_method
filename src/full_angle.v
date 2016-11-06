(*Require Import GeoCoq.Axioms.*)

(*Require Import Reals.*)
Require Export Setoid.

Section FA_FULLANGLES_defs.
  Variables FA_Point : Set.
  Variables Full_Angle : Set.
  
  (* Points predicate *)
  Variables FA_P_para : FA_Point -> FA_Point -> FA_Point -> FA_Point -> Prop.
  Variables FA_P_perp : FA_Point -> FA_Point -> FA_Point -> FA_Point -> Prop.
  Variables FA_P_col : FA_Point -> FA_Point -> FA_Point -> Prop.
  Variables FA_P_med : FA_Point -> FA_Point -> FA_Point -> Prop.
  Variables FA_P_cycl : FA_Point -> FA_Point -> FA_Point -> FA_Point -> Prop.
  Variables FA_P_circ : FA_Point -> FA_Point -> FA_Point -> FA_Point -> Prop.
  Variables FA_P_midp : FA_Point -> FA_Point -> FA_Point -> Prop.
  
  (* Full angle from points construction first and second points *)
  (* like third and fourth don't have to be different *)
  (* TODO maybe add more constraints later *)
  Variables FA_P_to_FA : FA_Point -> FA_Point -> FA_Point -> FA_Point -> Full_Angle.
  (* Full angle constants *)
  Variables FA_Zero : Full_Angle.
  Variables FA_One : Full_Angle.
  (* Full angles operations *)
  Variables FA_add : Full_Angle -> Full_Angle -> Full_Angle.
  Variables FAMinus : Full_Angle -> Full_Angle.
  (* Full angle predicates *)
  Variables FAEq : Full_Angle -> Full_Angle -> Prop.

  Notation "A + B" := (FA_add A B).
  
  Class FA_Full_angle_ax
  : Prop := build_FA_prop {
                (* Axioms *)
                (* case parallel lines *)
                fa_rule_1 : forall (A B C D : FA_Point),
                              FA_P_para A B C D ->
                              FAEq FA_Zero
                                   (FA_P_to_FA A B C D);
                (* case perpendicular lines *)
                fa_rule_2 : forall (A B C D : FA_Point),
                              FA_P_perp A B C D ->
                              FAEq FA_One
                                   (FA_P_to_FA A B C D);
                (* commutative and associative addition of full angles *)
                fa_rule_3a : forall (FA1 FA2 :  Full_Angle),
                               FAEq (FA1 + FA2) (FA2 + FA1);
                fa_rule_3b : forall (FA1 FA2 FA3 :  Full_Angle),
                               FAEq (FA1 + (FA2 + FA3)) ((FA1 + FA2) + FA3);
                (* property of FA_One *)
                fa_rule_4 : FAEq FA_Zero (FA_One + FA_One);
                (* property of FA_Zero *)
                fa_rule_5 : forall FA :  Full_Angle,
                              FAEq FA (FA + FA_Zero);
                (* case of 3 colinear points *)
                fa_rule_6 : forall (A B Q P X : FA_Point),
                              FA_P_col Q P X ->
                              FAEq (FA_P_to_FA A B P X)
                                      (FA_P_to_FA A B P Q);
                (* case parallel lines *)
                fa_rule_7 : forall (A B P X U V : FA_Point),
                              FA_P_para P X U V ->
                              FAEq (FA_P_to_FA A B P X)
                                      (FA_P_to_FA A B U V);
                (* case perpendicular lines *)
                fa_rule_8 : forall (A B P X U V : FA_Point),
                              FA_P_perp P X U V ->
                              FAEq (FA_P_to_FA A B P X)
                                      ((FA_P_to_FA A B U V) + FA_One);
                (* case of two distance equality XA = XB *)
                fa_rule_9 : forall (A B X : FA_Point),
                              FA_P_med X A B ->
                              FAEq (FA_P_to_FA A X A B)
                                      (FA_P_to_FA A B X B);
                (* inscribed angle theorem *)
                fa_rule_10 : forall (A B C D : FA_Point),
                               FA_P_cycl A B C D ->
                               FAEq (FA_P_to_FA A D C D)
                                    (FA_P_to_FA A B C B);
                (* circumcenter and midpoint *)
                fa_rule_11 : forall (A B C O M : FA_Point),
                               FA_P_circ O A B C ->
                               FA_P_midp M A B ->
                               FAEq (FA_P_to_FA A O O M)
                                    (FA_P_to_FA A C B C);
                (* equal distance and cyclic points *)
                fa_rule_12 : forall (A B P M : FA_Point),
                               FA_P_med M A B ->
                               FA_P_cycl A B P M ->
                               FAEq (FA_P_to_FA P A P M)
                                    (FA_P_to_FA P M P B);
                (* opposite full angle *)
                fa_rule_13 : forall (A B C D : FA_Point),
                               FAEq (FA_P_to_FA A B C D)
                                    (FAMinus (FA_P_to_FA C D A B));
                (* full angle splitting *)
                fa_rule_14 : forall (A B C D U V : FA_Point),
                               FAEq (FA_P_to_FA A B C D)
                                    ((FA_P_to_FA A B U V) +
                                     (FA_P_to_FA U V C D))
              }.

End FA_FULLANGLES_defs.


Print FA_Full_angle_ax.

(********************** END **********************************)


Section FA_build_from_p.

  Generalizable Variables CFA_Point CFull_Angle CP_para CP_perp CP_col CP_med CP_cycl
                CP_circ CP_midp CP_to_CFA CFA_Zero CFA_One CFA_add CFAMinus CFAEq.
  Variables C_para : forall (A B C : CFA_Point) (HAB : A <> B) (HCD : C <> D)
  Class CFA_from_P (FA : FA_Full_angle_ax CFA_Point CFull_Angle CP_para CP_perp CP_col CP_med CP_cycl
                                          CP_circ CP_midp CP_to_CFA CFA_Zero CFA_One CFA_add
                                          CFAMinus CFAEq)
  : Prop := {
             (* Constraints over equality of points to build full angles *)
             
  Class CFA_from_P (A B C D : CFA_Point)
        (FA : FA_Full_angle_ax CFA_Point CFull_Angle CP_para CP_perp CP_col CP_med CP_cycl CP_circ
                               CP_midp CP_to_CFA CFA_Zero CFA_One CFA_add CFAMinus CFAEq)
        (HAB : A <> B) (HCD : C <> D)
        : Set :=
  Global Instance FA_from_p  : FA_Full_angle_ax CFA_Point CFull_Angle CP_para CP_perp CP_cycl CP_circ
                                                CP_col CP_med CP_midp CP_to_CFA CFA_Zero CFA_One CFA_add CFAMinus CFAEq.

  
         
  Class C_FA_buid_P_constraint '{F : FA_Full_angle_ax CFA_Point CFull_Angle}
  : Prop := {
                                                                                 
        (CFA_Point CFull_Angle : Set)
        (*(CP_para CP_perp CP_cycl FA_P_circ : CFA_Point ->CFA_Point ->CFA_Point ->CFA_Point -> Prop)
        (CP_col CP_med FA_P_midp : FA_Point -> FA_Point -> FA_Point -> Prop)
        (CP_to_CFA : CFA_Point ->CFA_Point ->CFA_Point ->CFA_Point -> CFull_Angle)
        (FA_Zero  FA_One : CFull_Angle)
        (CFA_add : Full_Angle -> Full_Angle -> Full_Angle)
        (CFAMinus : Full_Angle -> Full_Angle)
        (CFAEq : Full_Angle -> Full_Angle -> Prop)*)
        '{F : FA_Full_angle_ax CFA_Point CFull_Angle
         CP_para CP_perp  : Prop
