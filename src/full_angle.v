(*Require Import GeoCoq.Axioms.metric_axioms.*)

Require Import Reals.
Require Export Setoid.

Open Scope R_scope.



Section full_angle_class.

  Record FA_cpl_to_ln {Point : Type} : Type := build_fa_line {A : Point ; B : Point ; Cond: A <> B}.

  (* Basic types in 2D space : points, lines and full angles *)
  Variables FA_Point : Type.
  Definition FA_Line := @FA_cpl_to_ln FA_Point.
  Variables FA_FullAngle : Type.
  
  (* Constant full angles *)
  Variables FA_Zero FA_One : FA_FullAngle.
  (* Equalities *)
  Variables FA_PEq : FA_Point -> FA_Point -> Prop.
  Variables FA_LEq : FA_Line -> FA_Line -> Prop.
  Variables FA_FAEq : FA_FullAngle -> FA_FullAngle -> Prop.
  (* Properties *)
  Variables FA_P_col : FA_Point -> FA_Point -> FA_Point -> Prop.
  Variables FA_P_cycl : FA_Point -> FA_Point -> FA_Point -> FA_Point -> Prop.
  Variables FA_P_midp : FA_Point -> FA_Point -> FA_Point -> Prop.
  Variables FA_P_circum : FA_Point -> FA_Point -> FA_Point -> FA_Point -> Prop.
  Variables FA_L_para : FA_Line -> FA_Line -> Prop.
  Variables FA_L_perp : FA_Line -> FA_Line -> Prop.

  (* Points to line,points to full angle, and lines to full angle
functions *)
  Definition FA_P_to_L := build_fa_line FA_Point.
  Variables FA_FullAngle_L : FA_Line -> FA_Line -> FA_FullAngle.
  Definition FA_FullAngle_P
             (A B C D : FA_Point)
             (HAB : A <> B)
             (HCD : C <> D)
  : FA_FullAngle :=
    FA_FullAngle_L (FA_P_to_L A B HAB) (FA_P_to_L C D HCD).
  (* Distance function *)
  Variables FA_P_dist : FA_Point -> FA_Point -> R.
  Class fa_dist_pr : Prop
    := build_fa_dist {
           (* basic properties *)
           fa_dist_positive : forall P1 P2 : FA_Point,
                                0 <= (FA_P_dist P1 P2);
           fa_dist_equal : forall P1 P2 : FA_Point,
                             (FA_P_dist P1 P2) = 0 <-> (FA_PEq P1 P2);
           fa_dist_sym : forall P1 P2 : FA_Point,
                           (FA_P_dist P1 P2) = (FA_P_dist P2 P1);
           (* midpoint related *)
           fa_dist_midp : forall P1 P2 P3 : FA_Point,
                            FA_P_midp P2 P1 P3 ->
                            FA_P_dist P1 P2 = FA_P_dist P2 P3;
           (* circumcenter related *)
           fa_dist_circum : forall O A B C : FA_Point,
                              FA_P_circum O A B C ->
                              FA_P_dist O A = FA_P_dist O B /\
                              FA_P_dist O A = FA_P_dist O C
         }.
  Definition FA_DIST_PR_Type := @fa_dist_pr.
  (* To lines related properties maybe others like perp predicates can be
concluced with full angles *)
  Class fa_line_pr : Prop
    := {
        (* A B C should be distinguished *)
        colinear_to_parallel : forall (A B C : FA_Point) (HAB : A <> B) (HAC : A <> C),
                                 FA_P_col A B C ->
                                 FA_L_para (FA_P_to_L A B HAB) (FA_P_to_L A C HAC);
        colinear_prop1 : forall (A B C : FA_Point),
                           FA_P_col A B C ->
                           (FA_P_col A C B) /\
                           (FA_P_col B A C) /\
                           (FA_P_col B C A) /\
                           (FA_P_col C A B) /\
                           (FA_P_col C B A)
      }.
  Definition FA_LINE_PR_Type := @fa_line_pr.
  (* Full Angles Axioms *)
  Class fa_full_angle {FA_add : FA_FullAngle ->  FA_FullAngle ->  FA_FullAngle}
  : Prop := {
             (* Full Angle building properties *)
             
             (* case parallel lines *)
             fa_rule_1 : forall (L1 L2 : FA_Line),
                           FA_L_para L1 L2 ->
                           FA_FAEq FA_Zero (FA_FullAngle_L L1 L2);
             (* case perpendicular lines *)
             fa_rule_2 : forall (L1 L2 : FA_Line),
                            FA_L_perp L1 L2 ->
                            FA_FAEq FA_One (FA_FullAngle_L L1 L2);
             (* commutative and associative addition of full angles *)
             fa_rule_3a : forall (FA1 FA2 :  FA_FullAngle),
                            FA_FAEq (FA_add FA1 FA2) (FA_add FA2 FA1);
             fa_rule_3b : forall (FA1 FA2 FA3 :  FA_FullAngle),
                            FA_FAEq (FA_add FA1 (FA_add FA2 FA3)) (FA_add (FA_add FA1 FA2) FA3);
             (* property of FA_One *)
             fa_rule_4 : FA_FAEq FA_Zero (FA_add FA_One FA_One);
             (* property of FA_Zero *)
             fa_rule_5 : forall FA :  FA_FullAngle,
                           FA_FAEq FA (FA_add FA FA_Zero);
             (* case of 3 colinear points *)
             fa_rule_6 : forall (A B Q P X : FA_Point)
                                (HAB : A <> B)
                                (HPX : P <> X)
                                (HPQ : P <> Q),
                           FA_P_col Q P X ->
                           FA_FAEq (FA_FullAngle_P A B P X HAB HPX)
                                   (FA_FullAngle_P A B P Q HAB HPQ);
             (* case parallel lines *)
             fa_rule_7 : forall (L1 L2 L3 : FA_Line),
                           FA_L_para L2 L3 ->
                           FA_FAEq (FA_FullAngle_L L1 L2)
                                 (FA_FullAngle_L L1 L3);
             (* case perpendicular lines *)
             fa_rule_8 : forall (L1 L2 L3 : FA_Line),
                           FA_L_perp L2 L3 ->
                           FA_FAEq (FA_FullAngle_L L1 L2)
                                   (FA_add (FA_FullAngle_L L1 L3)
                                           FA_One);
             (* case of two distance equality *)
             fa_rule_9 : forall (A B X : FA_Point)
                                (HAX : A <> X)
                                (HAB : A <> B)
                                (HXB : X <> B),
                           FA_FAEq (FA_FullAngle_P A X A B HAX HAB)
                                   (FA_FullAngle_P A B X B HAB HXB);
             (* inscribed angle theorem *)
             fa_rule_10 : forall (A B C D : FA_Point)
                                 (HAD : A <> D)
                                 (HCD : C <> D)
                                 (HAB : A <> B)
                                 (HCB : C <> B),
                            FA_P_cycl A B C D ->
                            FA_FAEq (FA_FullAngle_P A D C D HAD HCD)
                                    (FA_FullAngle_P A B C B HAB HCB);
             (* circumcenter and midpoint *)
             fa_rule_11 : forall (A B C O M : FA_Point)
                                 (HAO : A <> O)
                                 (HOM : O <> M)
                                 (HAC : A <> C)
                                 (HBC : B <> C),
                            FA_P_circum O A B C ->
                            FA_P_midp M A B ->
                            FA_FAEq (FA_FullAngle_P A O O M HAO HOM)
                                    (FA_FullAngle_P A C B C HAC HBC);
             (* equal distance and cyclic points *)
             fa_rule_12 : forall (A B P M : FA_Point)
                                 (HPA : P <> A)
                                 (HPM : P <> M)
                                 (HPB : P <> B),
                            FA_P_dist M A = FA_P_dist M B ->
                            FA_P_cycl A B P M ->
                            FA_FAEq (FA_FullAngle_P P A P M HPA HPM)
                                    (FA_FullAngle_P P M P B HPM HPB);
             
           }.
  
  (* equal distance *)
             
             
             