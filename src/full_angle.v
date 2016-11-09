(*Require Import GeoCoq.Axioms.*)

(*Require Import Reals.*)
Require Export Setoid.

Section FA_FULLANGLES_defs.
  Variables FA_Point : Type.
  Variables Full_Angle : Type.
  
  (* Points predicate *)
  (*Variables FA_P_para : forall (A B C D : FA_Point) (HAB : A<>B) (HCD : C<>D), Prop.*)
  (*Variables FA_P_perp : forall (A B C D : FA_Point) (HAB : A<>B) (HCD : C<>D), Prop.*)
  Variables FA_P_para : FA_Point -> FA_Point -> FA_Point -> FA_Point -> Prop.
  Variables FA_P_perp : FA_Point -> FA_Point -> FA_Point -> FA_Point -> Prop.
  (* use of bet *)
  Variables FA_P_col : FA_Point -> FA_Point -> FA_Point -> Prop.
  (* tarski : cong *)
  Variables FA_P_med : FA_Point -> FA_Point -> FA_Point -> Prop.
  Variables FA_P_cycl : FA_Point -> FA_Point -> FA_Point -> FA_Point -> Prop.
  Variables FA_P_circ : FA_Point -> FA_Point -> FA_Point -> FA_Point -> Prop.
  Variables FA_P_midp : FA_Point -> FA_Point -> FA_Point -> Prop.
  
  (* Full angle from points construction *)
  (*Variables FA_P_to_FA : forall (A B C D : FA_Point) (HAB : A<>B) (HCD : C<>D), Full_Angle.*)
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
                fa_rule_1 : forall (A B C D : FA_Point)
                                   (HAB : A<>B)
                                   (HCD : C<>D),
                              FA_P_para A B C D <->
                              FAEq FA_Zero
                                   (FA_P_to_FA A B C D);
                (* case perpendicular lines *)
                fa_rule_2 : forall (A B C D : FA_Point)
                                   (HAB : A<>B)
                                   (HCD : C<>D),
                              FA_P_perp A B C D <->
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
                fa_rule_6 : forall (A B Q P X : FA_Point)
                                   (HAB : A<>B)
                                   (HPX : P<>X)
                                   (HPQ : P<>Q),
                              FA_P_col Q P X ->
                              FAEq (FA_P_to_FA A B P X)
                                   (FA_P_to_FA A B P Q);
                (* case parallel lines *)
                fa_rule_7 : forall (A B P X U V : FA_Point)
                                   (HAB : A<>B)
                                   (HPX : P<>X)
                                   (HUV : U<>V),
                              FA_P_para P X U V ->
                              FAEq (FA_P_to_FA A B P X)
                                   (FA_P_to_FA A B U V);
                (* case perpendicular lines *)
                fa_rule_8 : forall (A B P X U V : FA_Point)
                                   (HAB : A<>B)
                                   (HPX : P<>X)
                                   (HUV : U<>V),
                              FA_P_perp P X U V ->
                              FAEq (FA_P_to_FA A B P X)
                                   ((FA_P_to_FA A B U V) + FA_One);
                (* case of two distance equality XA = XB *)
                fa_rule_9 : forall (A B X : FA_Point)
                                   (HAB : A<>B)
                                   (HAX : A<>X)
                                   (HXB : X<>B),
                              FA_P_med X A B ->
                              FAEq (FA_P_to_FA A X A B)
                                   (FA_P_to_FA A B X B);
                (* inscribed angle theorem *)
                fa_rule_10 : forall (A B C D : FA_Point)
                                    (HAB : A<>B)
                                    (HAD : A<>D)
                                    (HCD : C<>D)
                                    (HCB : C<>B),
                               FA_P_cycl A B C D ->
                               FAEq (FA_P_to_FA A D C D)
                                    (FA_P_to_FA A B C B);
                (* circumcenter and midpoint *)
                fa_rule_11 : forall (A B C O M : FA_Point)
                                    (HAO : A<>O)
                                    (HOM : O<>M)
                                    (HAC : A<>C)
                                    (HBC : B<>C),
                               FA_P_circ O A B C ->
                               FA_P_midp M A B ->
                               FAEq (FA_P_to_FA A O O M)
                                    (FA_P_to_FA A C B C);
                (* equal distance and cyclic points *)
                fa_rule_12 : forall (A B P M : FA_Point)
                                    (HPA : P<>A)
                                    (HPM : P<>M)
                                    (HPB : P<>B),
                               FA_P_med M A B ->
                               FA_P_cycl A B P M ->
                               FAEq (FA_P_to_FA P A P M)
                                    (FA_P_to_FA P M P B);
                (* opposite full angle *)
                fa_rule_13 : forall (A B C D : FA_Point)
                                    (HAB : A<>B)
                                    (HCD : C<>D),
                               FAEq (FA_P_to_FA A B C D)
                                    (FAMinus (FA_P_to_FA C D A B));
                (* full angle splitting *)
                fa_rule_14 : forall (A B C D U V : FA_Point)
                                    (HAB : A<>B)
                                    (HCD : C<>D)
                                    (HUV : U<>V),
                               FAEq (FA_P_to_FA A B C D)
                                    ((FA_P_to_FA A B U V) +
                                     (FA_P_to_FA U V C D))
              }.

End FA_FULLANGLES_defs.


(*Require Import GeoCoq.Axioms.independent_tarski_axioms.*)
Require Import GeoCoq.Axioms.tarski_axioms.
Section FA_instance.
  Context `{TE:Tarski_2D_euclidean}.
  Record basic_couble (A : Type) := mk_bcouple {first_p : A; second_p : A}.
  Record Quad_tpoint := {
                         p_1 : Tpoint;
                         p_2 : Tpoint;
                         p_3 : Tpoint;
                         p_4 : Tpoint;
                         H1 : p_1<>p_2;
                         H2 : p_3<>p_4
                       }.
  (*Class Point_fa_rep : Prop
    := {
        p_1 : Tpoint;
        p_2 : Tpoint;
        p_3 : Tpoint;
        p_4 : Tpoint;
        H1 : p_1<>p_2;
        H2 : p_3<>p_4
      }.*)
  (*Definition Full_Angle := @basic_couble Line.
  Definition build_FA  := mk_bcouple Line.*)

  Variables FEq : relation Quad_tpoint.
  Variables FEq_is_eqv : equiv Quad_tpoint FEq.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.
Print Par.
  (*Definition p_para (A B C D : Tpoint) (HAB : A<>B) (HCD : C<>D) : Prop :=
    Par A B C D.
  Definition p_perp (A B C D : Tpoint) (HAB : A<>B) (HCD : C<>D) : Prop :=
    Perp A B C D.*)
Require Import GeoCoq.Highschool.circumcenter.
Definition p_med (O A B : Tpoint) := Cong O A O B.
(*  Definition p_med (O A B : Tpoint) := is_circumcenter O A B A.*)
  Definition p_midp (M A B : Tpoint) : Prop :=
    (p_med M A B)/\(Col A B M).
  (*Variables a_line : Line.*)
  Variable FZero : Quad_tpoint.
  Variable FOne : Quad_tpoint.
  Variables Fadd : Quad_tpoint -> Quad_tpoint -> Quad_tpoint.
  Variables FMinus : Quad_tpoint -> Quad_tpoint.
(*  Definition Fadd (F1 F2 : Full_Angle) : F2 :=
    build_FA (first_p F1) (second_p F2).(* FFFFFAAAAUUUUUUUXXXXXXXX *)*)
  Require Import GeoCoq.Highschool.concyclic.
  Variables build_FA : forall (A B C D : Tpoint),Quad_tpoint.
  Instance FA_t : FA_Full_angle_ax Tpoint Quad_tpoint Par Perp Col p_med Concyclic
                                   is_circumcenter p_midp build_FA FZero FOne Fadd
                                   FMinus FEq.
  Proof.
    Admitted.
End FA_instance.
 
 Print FA_Full_angle_ax.

(********************** END **********************************)

