Require Import full_angle.

Section hypothesis_t_rules.

  (*Generalizable Variables Tpoint Quad_tpoint p_para p_perp Col p_med Concyclic
                is_circumcenter p_midp build_FA FZero FOne Fadd
                FMinus FEq.*)
  Context `{F:FA_Full_angle_ax}.

  Definition fp_Foot (O C A B : FA_Point) : Prop :=
    (FA_P_col O A B) /\ (FA_P_perp O C A B).

  (*Definition fp_Cong (A B C D : FA_Point) *)
  
End hypothesis_t_rules.

Print fp_Foot.