
Require Import GeoCoq.Highschool.Orthocenter.

Section Orthocenter.

Context `{TE:Tarski_2D_euclidean}.

Definition Foot d c a b := Col  /\ Perp  .

Lemma ex1 : forall a b c d e f g: TPoint,
Foot  d  c  a  b  -> Foot e  b  a  c  -> Midpoint  f  b  c  -> Midpoint  g  d  e  -> Perp  f  g  d  e .
Proof.
Admitted.

End Section.

forall a b c a1 b1 c1 o: FA_Point,
FA_P_midp  a1  b  c  ->FA_P_midp  b1  a  c  ->FA_P_midp  c1  a  b  ->FA_P_circum  o  a  b  c  ->
FA_P_perp  o  a1  b1  c1  .
forall a b c d e f h a1 p q: FA_Point,
FA_P_foot  d  a  b  c  ->FA_P_foot  e  b  a  c  ->FA_P_foot  f  c  a  b  ->FA_P_col  h  a  d  ->FA_P_col  h  b  e  ->FA_P_col  h  c  f  ->FA_P_midp  a1  b  c  ->FA_P_midp  p  b  e  ->FA_P_midp  q  c  f  ->
FA_P_cycl  p  q  h  d  .
forall a b c d o q s j m: FA_Point,
FA_P_circum  o  a  b  c  d  ->FA_P_col  i  a  d  ->FA_P_col  i  b  c  ->FA_P_midp  q  b  c  ->FA_P_midp  s  a  d  ->FA_P_midp  j  s  q  ->FA_P_midp  j  o  m  ->
FA_P_perp  s  m  b  c  .
forall a b c h o p q r: FA_Point,
FA_P_orthoc  h  a  b  c  ->FA_P_circum  o  a  b  c  ->FA_P_circum  p  a  c  h  ->FA_P_circum  q  a  b  h  ->
forall a b c e f h: FA_Point,
FA_P_foot  e  b  a  c  ->FA_P_foot  f  a  b  c  ->FA_P_col  h  a  f  ->FA_P_col  h  b  e  ->
FA_P_perp  a  b  c  h  .
forall o a b c d e f g: FA_Point,
FA_P_cong  o  a  o  b  ->FA_P_cong  o  a  o  c  ->FA_P_cong  o  a  o  d  ->FA_P_col  e  b  c  ->FA_P_perp  e  d  b  c  ->FA_P_col  f  a  c  ->FA_P_perp  f  d  a  c  ->FA_P_col  g  a  b  ->FA_P_perp  g  d  a  b  ->
FA_P_col  g  f  e  .
forall a b c p p1 g g1 f f1 k: FA_Point,
FA_P_cycl  a  b  c  p  p1  ->FA_P_foot  g  p  a  b  ->FA_P_foot  f  p  a  c  ->FA_P_foot  g1  p1  a  b  ->FA_P_foot  f1  p1  a  c  ->FA_P_col  k  f  g  ->FA_P_col  k  f1  g1  ->
FA_P_eqangle  p  a  p1  f1  k  f  .
forall a b c d p p1 g f f1 g1 f2 f3: FA_Point,
forall a b c d e q p: FA_Point,
FA_P_cycl  a  b  e  q  ->FA_P_cycl  c  d  e  q  ->FA_P_col  a  b  p  ->FA_P_col  c  d  p  ->FA_P_col  b  c  e  ->FA_P_col  a  d  e  ->
FA_P_cycl  d  a  p  q  .
forall a b c d l m n: FA_Point,
FA_P_midp  m  b  c  ->FA_P_midp  n  a  c  ->FA_P_midp  l  a  b  ->FA_P_foot  d  a  b  c  ->
FA_P_cycl  l  d  m  n  .
forall a b c d e f: FA_Point,
FA_P_cycl  a  b  c  d  ->FA_P_perp  a  c  b  d  ->FA_P_col  e  a  c  ->FA_P_col  e  b  d  ->FA_P_midp  f  a  b  ->
forall a b c d e f h g: FA_Point,
FA_P_para  d  a  b  c  ->FA_P_para  d  c  a  b  ->FA_P_foot  e  b  a  c  ->FA_P_foot  f  a  b  d  ->FA_P_foot  h  c  b  d  ->FA_P_foot  g  d  a  c  ->
FA_P_para  e  f  h  g  .
forall c e f q d i p a: FA_Point,
FA_P_circum  q  c  e  f  d  ->FA_P_midp  q  c  d  ->FA_P_midp  i  e  f  ->FA_P_col  p  i  q  ->FA_P_perp  p  e  e  q  ->FA_P_col  a  c  e  ->FA_P_cong  a  p  p  e  ->
FA_P_col  a  d  f  .
forall a b c f d e g i h k: FA_Point,
FA_P_foot  f  c  a  b  ->FA_P_foot  d  a  b  c  ->FA_P_foot  e  b  a  c  ->FA_P_foot  g  f  b  c  ->FA_P_foot  i  d  a  b  ->FA_P_foot  h  f  a  c  ->FA_P_foot  k  e  a  b  ->
FA_P_cycl  h  i  g  k  .
forall o a b c d m p q k t s: FA_Point,
forall a c k n o b m: FA_Point,
FA_P_circum  o  a  c  k  n  ->FA_P_col  b  a  k  ->FA_P_col  b  c  n  ->FA_P_cycl  m  a  b  c  ->FA_P_cycl  m  b  k  n  ->
FA_P_cycl  k  o  c  m  .
forall a c k n o b m: FA_Point,
FA_P_circum  o  a  c  k  n  ->FA_P_col  b  a  k  ->FA_P_col  b  c  n  ->FA_P_cycl  k  o  c  m  ->FA_P_cycl  m  a  b  c  ->FA_P_cycl  m  b  k  n  ->
FA_P_perp  b  m  m  o  .
forall a b c d e f: FA_Point,
FA_P_cycl  a  b  c  d  ->FA_P_cycl  a  b  e  f  ->FA_P_col  a  c  e  ->FA_P_col  b  d  f  ->
FA_P_para  c  d  e  f  .
forall a b c d e h g: FA_Point,
FA_P_foot  e  b  a  c  ->FA_P_foot  d  a  b  c  ->FA_P_col  h  e  b  ->FA_P_col  h  a  d  ->FA_P_foot  g  h  a  b  ->
FA_P_eqangle  d  g  h  h  g  e  .
forall a b c o d: FA_Point,
FA_P_cong  o  a  o  b  ->FA_P_cong  o  a  o  c  ->FA_P_col  d  b  c  ->FA_P_perp  a  d  b  c  ->
forall a m n o p q d e: FA_Point,
FA_P_cong  o  a  o  n  ->FA_P_cong  o  a  o  m  ->FA_P_col  p  o  n  ->FA_P_perp  p  a  o  n  ->FA_P_col  q  o  m  ->FA_P_perp  q  a  o  m  ->FA_P_col  e  a  p  ->FA_P_col  e  n  m  ->FA_P_col  d  a  q  ->FA_P_col  d  n  m  ->
forall a c d e o m f g: FA_Point,
FA_P_cong  o  a  o  c  ->FA_P_cong  o  a  o  d  ->FA_P_cong  o  a  o  e  ->FA_P_col  m  c  o  ->FA_P_perp  m  a  c  o  ->FA_P_col  f  a  m  ->FA_P_col  f  c  d  ->FA_P_col  g  a  m  ->FA_P_col  g  c  e  ->
forall x r p q s y i: FA_Point,
FA_P_cycl  r  p  q  s  ->FA_P_col  y  q  s  ->FA_P_cycl  y  p  q  x  ->FA_P_col  i  x  y  ->FA_P_col  i  r  s  ->
forall a b c f m q p l s n: FA_Point,
FA_P_foot  f  c  a  b  ->FA_P_midp  m  b  c  ->FA_P_midp  q  a  c  ->FA_P_midp  p  a  b  ->FA_P_midp  l  f  p  ->FA_P_midp  s  p  q  ->FA_P_perp  n  l  a  b  ->FA_P_perp  n  s  p  q  ->
forall a b c h o p q r: FA_Point,
FA_P_orthoc  h  a  b  c  ->FA_P_circum  o  a  b  c  ->FA_P_circum  r  b  c  h  ->FA_P_circum  p  a  c  h  ->FA_P_circum  q  a  b  h  ->
FA_P_para  p  c  q  b  .
forall a b c h o p q r: FA_Point,
FA_P_orthoc  h  a  b  c  ->FA_P_circum  o  a  b  c  ->FA_P_circum  r  b  c  h  ->FA_P_circum  p  a  c  h  ->FA_P_circum  q  a  b  h  ->
FA_P_pbisector  h  p  q  .
forall a b c f h p q t: FA_Point,
FA_P_foot  f  c  a  b  ->FA_P_col  h  c  f  ->FA_P_perp  h  a  b  c  ->FA_P_perp  h  b  a  c  ->FA_P_foot  p  f  a  c  ->FA_P_foot  q  f  a  h  ->FA_P_foot  t  f  b  c  ->
FA_P_col  p  q  t  .
forall a b c d p q: FA_Point,
FA_P_foot  d  a  b  c  ->FA_P_foot  p  d  a  c  ->FA_P_foot  q  d  a  b  ->
FA_P_cycl  p  b  q  c  .
forall a b c e f o: FA_Point,
FA_P_circum  o  a  b  c  ->FA_P_foot  e  b  a  c  ->FA_P_foot  f  c  a  b  ->
FA_P_perp  o  a  e  f  .
forall a b c o b1 c1 p q: FA_Point,
FA_P_circum  o  a  b  c  ->FA_P_midp  c1  a  b  ->FA_P_midp  b1  a  c  ->FA_P_col  p  o  c1  ->FA_P_col  q  o  b1  ->FA_P_col  p  a  c  ->FA_P_col  q  a  b  ->
FA_P_cycl  b  c  p  q  .
forall b c r s o a m n: FA_Point,
FA_P_circum  o  b  c  r  ->FA_P_cong  o  b  o  s  ->FA_P_col  a  r  b  ->FA_P_col  a  s  c  ->FA_P_foot  m  a  r  s  ->FA_P_foot  n  a  b  c  ->
FA_P_eqangle  b  a  m  n  a  c  .
forall a b c d i e f: FA_Point,
FA_P_cycl  a  b  c  d  ->FA_P_col  i  a  b  ->FA_P_col  i  c  d  ->FA_P_perp  e  d  d  c  ->FA_P_perp  e  a  a  b  ->FA_P_perp  f  b  b  a  ->FA_P_perp  f  c  c  d  ->
FA_P_eqangle  a  i  e  f  i  c  .
forall a b c h o p: FA_Point,
FA_P_orthoc  h  a  b  c  ->FA_P_circum  o  b  c  h  ->FA_P_perp  p  h  h  c  ->FA_P_cong  p  o  o  b  ->
FA_P_para  a  h  b  p  .
forall a b c o d e h k: FA_Point,
FA_P_circum  o  a  b  c  ->FA_P_foot  d  c  a  b  ->FA_P_foot  e  b  a  c  ->FA_P_col  h  b  e  ->FA_P_col  h  c  d  ->FA_P_col  k  c  d  ->FA_P_cong  k  o  a  o  ->
FA_P_pbisector  a  h  k  .
forall a b c o d e h o1: FA_Point,
FA_P_circum  o  a  b  c  ->FA_P_foot  d  c  a  b  ->FA_P_foot  e  b  a  c  ->FA_P_col  h  b  e  ->FA_P_col  h  c  d  ->FA_P_circum  o1  a  b  h  ->
FA_P_pbisector  a  o  o1  .
forall a b c o h a1 c1: FA_Point,
FA_P_circum  o  a  b  c  ->FA_P_orthoc  h  a  b  c  ->FA_P_col  a1  a  h  ->FA_P_cong  o  a  o  a1  ->FA_P_col  c1  c  h  ->FA_P_cong  o  a  o  c1  ->
FA_P_pbisector  b  a1  c1  .

forall a b c o d d1 p: FA_Point,
forall a b c i m l1: FA_Point,
FA_P_incenter  i  a  b  c  ->FA_P_cycl  a  b  c  m  l1  ->FA_P_col  m  i  c  ->FA_P_perp  b  l1  b  i  ->
FA_P_para  m  l1  a  i  .
forall a b c i m: FA_Point,
FA_P_incenter  i  a  b  c  ->FA_P_col  m  a  c  ->FA_P_para  i  m  a  b  ->
FA_P_pbisector  m  a  i  .
forall a b c i x y l: FA_Point,
FA_P_incenter  i  a  b  c  ->FA_P_foot  x  i  b  c  ->FA_P_foot  y  i  a  c  ->FA_P_foot  l  b  a  i  ->
FA_P_col  x  y  l  .
forall a b c i a1 x x1 y d: FA_Point,
FA_P_incenter  i  a  b  c  ->FA_P_midp  a1  b  c  ->FA_P_foot  x  b  a  i  ->FA_P_midp  x  b  x1  ->FA_P_col  x1  a  c  ->FA_P_foot  y  c  a  i  ->FA_P_foot  d  a  b  c  ->
FA_P_cycl  x  y  d  a1  .
forall a b c p: FA_Point,
FA_P_perp  c  a  c  b  ->FA_P_perp  p  a  p  b  ->FA_P_cong  p  a  p  b  ->
FA_P_eqangle  a  c  p  p  c  b  .
forall a b c d a1 c1: FA_Point,
FA_P_cycl  a  b  c  d  ->FA_P_col  a1  c  d  ->FA_P_perp  a1  a  a  b  ->FA_P_col  c1  a  b  ->FA_P_perp  c1  c  c  d  ->
FA_P_para  a1  c1  b  d  .
forall a b c d o i q s j m: FA_Point,
FA_P_circum  o  a  b  c  d  ->FA_P_col  i  a  d  ->FA_P_col  i  b  c  ->FA_P_midp  q  b  c  ->FA_P_midp  s  a  d  ->FA_P_midp  j  s  q  ->FA_P_midp  j  o  m  ->
FA_P_perp  i  m  q  s  .
forall a b c d e p q s r: FA_Point,
FA_P_cycl  a  b  c  d  e  ->FA_P_foot  p  e  a  b  ->FA_P_foot  q  e  b  c  ->FA_P_foot  r  e  c  d  ->FA_P_foot  s  e  a  d  ->
FA_P_eqangle  e  p  s  e  q  r  .
forall a b c d u v: FA_Point,
FA_P_cycl  a  b  c  d  ->FA_P_orthoc  u  a  b  d  ->FA_P_orthoc  v  a  c  d  ->
FA_P_cycl  u  v  a  d  .
forall a b c d e i: FA_Point,
FA_P_cycl  a  b  c  d  ->FA_P_col  e  a  c  ->FA_P_col  e  b  d  ->FA_P_circum  i  a  b  e  ->
FA_P_perp  i  e  c  d  .
forall a b c d p q s r o: FA_Point,
FA_P_perp  a  c  b  d  ->FA_P_midp  p  a  b  ->FA_P_midp  q  b  c  ->FA_P_midp  s  a  d  ->FA_P_midp  r  c  d  ->FA_P_col  o  p  r  ->FA_P_col  o  q  s  ->
FA_P_pbisector  o  s  r  .
forall a b c d o m p r: FA_Point,
FA_P_circum  o  a  b  c  d  ->FA_P_perp  a  c  b  d  ->FA_P_col  m  a  c  ->FA_P_col  m  b  d  ->FA_P_midp  p  a  b  ->FA_P_midp  r  c  d  ->
FA_P_para  o  p  r  m  .
forall a b c d o e: FA_Point,
FA_P_circum  o  a  b  c  d  e  ->FA_P_perp  a  c  b  d  ->FA_P_col  e  d  o  ->
FA_P_para  b  e  a  c  .
forall c d e o a f: FA_Point,
FA_P_perp  c  e  d  e  ->FA_P_midp  o  c  d  ->FA_P_perp  a  c  c  d  ->FA_P_perp  a  e  e  o  ->FA_P_col  f  a  c  ->FA_P_col  f  d  e  ->
FA_P_pbisector  a  e  f  .
forall o a b c e d: FA_Point,
FA_P_cong  o  a  o  b  ->FA_P_col  c  a  b  ->FA_P_perp  e  b  b  o  ->FA_P_perp  e  c  c  o  ->FA_P_perp  d  a  a  o  ->FA_P_col  e  c  d  ->
FA_P_pbisector  o  e  d  .
forall a b c g o m d e f: FA_Point,
FA_P_perp  b  a  a  c  ->FA_P_midp  o  b  c  ->FA_P_foot  d  a  b  c  ->FA_P_foot  m  b  a  o  ->FA_P_col  e  b  m  ->FA_P_col  e  a  d  ->FA_P_col  f  a  c  ->FA_P_col  f  b  m  ->
FA_P_pbisector  e  a  b  .
forall a b c g o m d e f: FA_Point,
FA_P_perp  b  a  a  c  ->FA_P_midp  o  b  c  ->FA_P_foot  d  a  b  c  ->FA_P_foot  m  b  a  o  ->FA_P_col  e  b  m  ->FA_P_col  e  a  d  ->FA_P_col  f  a  c  ->FA_P_col  f  b  m  ->
FA_P_pbisector  e  f  a  .
forall a b m o d e: FA_Point,
FA_P_cong  m  a  m  b  ->FA_P_cong  o  a  o  m  ->FA_P_cong  o  a  o  b  ->FA_P_midp  d  a  b  ->FA_P_col  m  o  d  ->FA_P_perp  e  a  a  o  ->FA_P_para  m  e  a  o  ->
FA_P_pbisector  m  e  d  .
forall a b c d o e f: FA_Point,
FA_P_foot  d  a  b  c  ->FA_P_midp  o  a  d  ->FA_P_col  e  a  b  ->FA_P_cong  o  a  o  e  ->FA_P_col  f  a  c  ->FA_P_cong  o  a  o  f  ->
FA_P_cycl  b  c  e  f  .
forall a b c d e f: FA_Point,
FA_P_cycl  a  b  c  d  ->FA_P_col  e  a  b  ->FA_P_col  e  c  d  ->FA_P_col  f  b  c  ->FA_P_para  f  e  a  d  ->
FA_P_eqangle  f  e  b  e  c  b  .
forall a b c o m n: FA_Point,
FA_P_circum  o  a  b  c  ->FA_P_midp  m  a  b  ->FA_P_col  n  m  o  ->FA_P_cong  o  a  o  n  ->
FA_P_eqangle  a  c  n  n  c  b  .
forall a b c o d e f n k: FA_Point,
FA_P_circum  o  a  b  c  ->FA_P_midp  d  b  c  ->FA_P_midp  e  a  c  ->FA_P_midp  f  a  b  ->FA_P_col  n  o  f  ->FA_P_cong  o  a  o  n  ->FA_P_foot  k  n  a  c  ->
FA_P_eqangle  e  f  k  k  f  d  .
forall a b c o x d o1: FA_Point,
FA_P_circum  o  a  b  c  ->FA_P_midp  x  a  b  ->FA_P_cong  o1  a  o1  b  ->FA_P_col  o1  x  o  ->FA_P_col  d  b  c  ->FA_P_cong  d  o1  o1  a  ->
FA_P_eqangle  a  o  o1  a  c  d  .
forall d a b c e f g: FA_Point,
FA_P_cycl  a  b  c  d  ->FA_P_perp  e  a  e  d  ->FA_P_perp  e  b  e  d  ->FA_P_perp  f  a  f  d  ->FA_P_perp  f  c  f  d  ->FA_P_perp  g  c  g  d  ->FA_P_perp  g  b  g  d  ->
FA_P_col  e  f  g  .
forall p a1 b1 c1 a b c: FA_Point,
FA_P_circum  a  p  b1  c1  ->FA_P_circum  b  p  a1  c1  ->FA_P_circum  c  p  b1  a1  ->FA_P_col  a1  b1  c1  ->
FA_P_cycl  p  a  b  c  .
forall e f m b d a e1 f1: FA_Point,
FA_P_circum  b  e  f  m  ->FA_P_midp  d  e  f  ->FA_P_col  a  d  b  ->FA_P_col  e1  m  e  ->FA_P_cong  e1  a  e  a  ->FA_P_col  f1  m  f  ->FA_P_cong  f1  a  e  a  ->
FA_P_perp  e1  f1  m  b  .
forall a b c o d e n: FA_Point,
FA_P_circum  o  a  b  c  ->FA_P_col  d  a  b  ->FA_P_col  e  a  c  ->FA_P_para  d  e  b  c  ->FA_P_circum  n  a  d  e  ->
FA_P_col  a  n  o  .
forall a b c i h n m: FA_Point,
FA_P_foot  i  c  a  b  ->FA_P_col  h  c  i  ->FA_P_perp  h  a  b  c  ->FA_P_midp  m  c  b  ->FA_P_midp  n  a  h  ->
FA_P_perp  m  i  n  i  .
forall a b c i o b1 c1 m: FA_Point,
FA_P_incenter  i  a  b  c  ->FA_P_circum  o  b  c  i  ->FA_P_col  b1  b  i  ->FA_P_perp  b1  c  c  i  ->FA_P_col  c1  c  i  ->FA_P_perp  c1  b  b  i  ->FA_P_midp  m  b1  c1  ->
FA_P_perp  m  b  o  b  .
forall p d i a e x b g f: FA_Point,
FA_P_circum  a  p  d  i  e  ->FA_P_midp  a  d  e  ->FA_P_midp  x  p  i  ->FA_P_col  b  a  x  ->FA_P_perp  b  p  a  p  ->FA_P_col  e  i  g  ->FA_P_cong  g  b  p  b  ->FA_P_midp  b  g  f  ->
FA_P_perp  f  g  d  e  .
forall a b m o i j: FA_Point,
FA_P_perp  a  m  b  m  ->FA_P_midp  o  a  b  ->FA_P_circum  i  o  a  m  ->FA_P_circum  j  o  b  m  ->
FA_P_perp  i  m  m  j  .
forall a b a1 o b1 p o1: FA_Point,
FA_P_circum  o  a  b  a1  b1  ->FA_P_midp  o  a  b  ->FA_P_col  p  a  a1  ->FA_P_col  p  b  b1  ->FA_P_circum  o1  p  a1  b1  ->
FA_P_perp  o1  a1  o  a1  .
forall a b c d o f g: FA_Point,
FA_P_circum  o  a  b  c  d  ->FA_P_para  d  a  b  c  ->FA_P_foot  g  d  a  b  ->FA_P_foot  f  d  a  c  ->
FA_P_para  g  f  o  a  .
forall a b c d o f g: FA_Point,
FA_P_circum  o  a  b  c  d  ->FA_P_foot  g  d  a  b  ->FA_P_foot  f  d  a  c  ->
FA_P_sim  d  f  g  d  c  b  .
forall a b c d o f g l: FA_Point,
FA_P_circum  o  a  b  c  d  ->FA_P_foot  g  d  a  b  ->FA_P_foot  f  d  a  c  ->FA_P_col  l  d  g  ->FA_P_cong  l  o  o  a  ->
FA_P_para  c  l  f  g  .
forall a b c o g d e f: FA_Point,
FA_P_circum  o  a  b  c  ->FA_P_foot  g  c  a  b  ->FA_P_col  d  c  g  ->FA_P_cong  d  o  o  a  ->FA_P_foot  e  d  a  c  ->FA_P_foot  f  d  b  c  ->
FA_P_cycl  a  b  e  f  .
forall a b c o1 o o2 d i: FA_Point,
FA_P_circum  o1  a  b  c  ->FA_P_midp  o  a  b  ->FA_P_col  o1  o2  o  ->FA_P_col  d  a  c  ->FA_P_cong  o2  a  o2  d  ->FA_P_col  o1  c  i  ->FA_P_col  o2  d  i  ->
FA_P_eqangle  c  b  d  o1  i  o2  .
forall b c a o e d: FA_Point,
FA_P_cong  a  b  a  c  ->FA_P_cong  b  c  b  a  ->FA_P_pbisector  o  a  b  ->FA_P_pbisector  o  c  b  ->FA_P_pbisector  o  e  b  ->FA_P_col  a  e  d  ->FA_P_col  b  c  d  ->
FA_P_sim  e  d  c  e  b  a  .
forall b a c i o h k: FA_Point,
FA_P_incenter  i  a  b  c  ->FA_P_perp  b  o  a  b  ->FA_P_pbisector  o  b  i  ->FA_P_pbisector  o  b  h  ->FA_P_col  a  c  h  ->FA_P_col  a  c  k  ->FA_P_pbisector  o  b  k  ->
FA_P_eqangle  h  i  c  c  i  k  .
forall a b c o g e k h n: FA_Point,
FA_P_circum  o  b  a  c  ->FA_P_midp  g  b  c  ->FA_P_col  g  o  e  ->FA_P_pbisector  o  b  e  ->FA_P_perp  k  e  a  b  ->FA_P_col  k  a  b  ->FA_P_perp  a  h  o  g  ->FA_P_col  h  o  g  ->FA_P_circum  n  g  h  k  ->
FA_P_perp  e  k  k  n  .
forall a b c o d f: FA_Point,
FA_P_pbisector  o  a  b  ->FA_P_pbisector  o  a  c  ->FA_P_col  a  b  d  ->FA_P_perp  a  b  c  d  ->FA_P_col  f  a  b  ->FA_P_eqangle  a  c  f  f  c  b  ->
FA_P_eqangle  d  c  f  f  c  o  .
forall a b c o u t: FA_Point,
FA_P_pbisector  o  b  c  ->FA_P_pbisector  o  b  a  ->FA_P_eqangle  b  a  u  u  a  c  ->FA_P_col  b  u  c  ->FA_P_perp  o  a  a  t  ->FA_P_col  b  c  t  ->
FA_P_pbisector  t  a  u  .
forall u v a b c o p q: FA_Point,
FA_P_perp  a  u  a  v  ->FA_P_cong  a  u  a  v  ->FA_P_col  u  v  b  ->FA_P_eqangle  c  a  u  u  a  b  ->FA_P_col  u  v  c  ->FA_P_midp  o  b  c  ->FA_P_col  a  b  p  ->FA_P_col  a  c  q  ->FA_P_pbisector  o  b  q  ->FA_P_pbisector  o  b  p  ->
FA_P_pbisector  c  p  q  .
forall a b c o i e j l: FA_Point,
FA_P_incenter  o  a  b  c  ->FA_P_foot  i  c  a  o  ->FA_P_perp  e  a  o  a  ->FA_P_foot  j  c  a  e  ->FA_P_foot  l  c  b  o  ->
FA_P_col  i  j  l  .
forall a b c d e x: FA_Point,
FA_P_col  b  c  d  ->FA_P_perp  b  c  a  d  ->FA_P_col  a  c  e  ->FA_P_perp  a  c  b  e  ->FA_P_col  a  b  x  ->FA_P_col  d  e  x  ->
forall b c a a1 b1 c1 n k j: FA_Point,
FA_P_midp  a1  b  c  ->FA_P_midp  c1  b  a  ->FA_P_midp  b1  a  c  ->FA_P_pbisector  n  a1  b1  ->FA_P_pbisector  n  a1  c1  ->FA_P_perp  a1  k  a1  n  ->FA_P_col  a  c  k  ->FA_P_col  k  a1  j  ->FA_P_col  a  b  j  ->
FA_P_cycl  k  j  b  c  .
forall a b c o u i: FA_Point,
FA_P_pbisector  o  a  b  ->FA_P_pbisector  o  b  c  ->FA_P_eqangle  b  a  u  u  a  c  ->FA_P_col  b  c  u  ->FA_P_pbisector  i  a  u  ->FA_P_col  i  o  a  ->
FA_P_perp  i  u  b  c  .
forall a b c a1 b1 c1 a2 c2: FA_Point,
FA_P_midp  a  b1  c  ->FA_P_midp  a  c1  b  ->FA_P_midp  b  a1  c  ->FA_P_eqangle  a  b  a2  a2  b  c  ->FA_P_col  b1  c1  a2  ->FA_P_col  b  a2  c2  ->FA_P_col  a1  b1  c2  ->
FA_P_pbisector  b1  a2  c2  .
forall a b c e f c1 b1 x: FA_Point,
FA_P_col  a  b  f  ->FA_P_col  a  c  e  ->FA_P_perp  a  b  c  f  ->FA_P_perp  a  c  b  e  ->FA_P_midp  c1  a  b  ->FA_P_midp  b1  a  c  ->FA_P_col  x  c1  e  ->FA_P_col  x  b1  f  ->
forall o x y l a b p q p1 q1 i: FA_Point,
FA_P_perp  l  a  o  x  ->FA_P_col  a  o  x  ->FA_P_perp  l  b  o  y  ->FA_P_col  o  b  y  ->FA_P_midp  a  l  p  ->FA_P_midp  b  l  q  ->FA_P_col  p1  l  q  ->FA_P_col  o  x  p1  ->FA_P_col  q1  l  p  ->FA_P_col  q1  o  y  ->
FA_P_cycl  o  p  q  p1  .
forall b c a i a1 b1 c1 p q n: FA_Point,
FA_P_incenter  i  a  b  c  ->FA_P_midp  p  b  i  ->FA_P_midp  q  c  i  ->FA_P_pbisector  n  a1  p  ->FA_P_pbisector  n  a1  q  ->FA_P_midp  a1  c  b  ->FA_P_midp  b1  c  a  ->FA_P_midp  c1  a  b  ->
FA_P_eqangle  b1  a1  n  n  a1  c1  .
forall a b c d o f g c1 b1: FA_Point,
FA_P_pbisector  o  a  b  ->FA_P_pbisector  o  a  c  ->FA_P_pbisector  o  a  d  ->FA_P_col  a  b  g  ->FA_P_col  a  c  f  ->FA_P_perp  a  b  d  g  ->FA_P_perp  a  c  d  f  ->FA_P_col  d  g  c1  ->FA_P_pbisector  o  a  c1  ->FA_P_col  d  f  b1  ->FA_P_pbisector  o  a  b1  ->
FA_P_para  c1  c  b1  b  .
forall a b c o p p1 g g1 f f1 k: FA_Point,
FA_P_pbisector  o  a  b  ->FA_P_pbisector  o  a  c  ->FA_P_pbisector  o  a  p  ->FA_P_pbisector  o  a  p1  ->FA_P_perp  p  g  a  b  ->FA_P_col  g  a  b  ->FA_P_perp  p  f  a  c  ->FA_P_col  a  c  f  ->FA_P_perp  p1  g1  a  b  ->FA_P_col  g1  a  b  ->FA_P_perp  p1  f1  a  c  ->FA_P_col  a  c  f1  ->FA_P_perp  k  p  f1  g1  ->FA_P_perp  k  p1  f  g  ->
FA_P_cycl  p  p1  a  k  .
forall a b c o p p1 g g1 f f1 k: FA_Point,
FA_P_pbisector  o  a  b  ->FA_P_pbisector  o  a  c  ->FA_P_pbisector  o  a  p  ->FA_P_pbisector  o  a  p1  ->FA_P_perp  p  g  a  b  ->FA_P_col  g  a  b  ->FA_P_perp  p  f  a  c  ->FA_P_col  a  c  f  ->FA_P_perp  p1  g1  a  b  ->FA_P_col  g1  a  b  ->FA_P_perp  p1  f1  a  c  ->FA_P_col  a  c  f1  ->FA_P_para  k  p  f1  g1  ->FA_P_para  k  p1  f  g  ->
FA_P_cycl  p  p1  a  k  .
forall a b c d o d1 f g f1 g1 k a1 b1 c1 n: FA_Point,
FA_P_circum  o  a  b  c  d  d1  ->FA_P_col  a  b  g  ->FA_P_col  a  c  f  ->FA_P_perp  a  b  d  g  ->FA_P_perp  a  c  d  f  ->FA_P_midp  o  d  d1  ->FA_P_col  a  b  g1  ->FA_P_col  a  c  f1  ->FA_P_perp  a  b  d1  g1  ->FA_P_perp  a  c  d1  f1  ->FA_P_col  g  f  k  ->FA_P_col  g1  f1  k  ->FA_P_midp  a1  c  b  ->FA_P_midp  b1  a  c  ->FA_P_midp  c1  a  b  ->FA_P_pbisector  n  c1  a1  ->FA_P_pbisector  n  c1  b1  ->FA_P_pbisector  n  c1  k  ->
FA_P_perp  f  g  f1  g1  .
forall a b c d p o e f g h i: FA_Point,
FA_P_cycl  a  b  c  d  p  ->FA_P_perp  p  g  a  b  ->FA_P_perp  p  h  b  c  ->FA_P_perp  p  e  c  d  ->FA_P_perp  p  f  d  a  ->FA_P_col  g  a  b  ->FA_P_col  h  b  c  ->FA_P_col  e  c  d  ->FA_P_col  f  d  a  ->FA_P_col  i  g  f  ->FA_P_col  i  e  h  ->
FA_P_cycl  g  h  p  i  .
forall a b c o a1 s q p: FA_Point,
FA_P_circum  o  a  b  c  p  q  ->FA_P_midp  a1  b  c  ->FA_P_col  a  a1  p  ->FA_P_eqangle  b  a  s  a1  a  c  ->FA_P_col  b  s  c  ->FA_P_col  a  s  q  ->
FA_P_para  p  q  b  c  .
forall b c a a1 s n g h: FA_Point,
FA_P_midp  b  a1  c  ->FA_P_eqangle  b  a  s  a1  a  c  ->FA_P_col  b  s  c  ->FA_P_col  n  a  a1  ->FA_P_perp  n  g  a  b  ->FA_P_col  a  g  b  ->FA_P_perp  n  h  a  c  ->FA_P_col  h  a  c  ->
FA_P_perp  g  h  a  s  .
forall a b c o a1 s q p d g: FA_Point,
FA_P_circum  o  a  b  c  p  q  ->FA_P_midp  a1  b  c  ->FA_P_col  a  a1  p  ->FA_P_eqangle  b  a  s  a1  a  c  ->FA_P_col  b  s  c  ->FA_P_col  a  s  q  ->FA_P_col  d  b  c  ->FA_P_perp  q  d  b  c  ->FA_P_col  a  b  g  ->FA_P_perp  q  g  a  b  ->
FA_P_perp  d  g  a  p  .
forall a b c o p s q: FA_Point,
forall a b c m n q p: FA_Point,
FA_P_eqangle  b  a  m  n  a  c  ->FA_P_perp  m  q  a  b  ->FA_P_col  q  a  b  ->FA_P_perp  m  p  a  c  ->FA_P_col  p  a  c  ->
FA_P_perp  n  a  p  q  .
forall a b c m d f: FA_Point,
FA_P_cong  a  c  c  b  ->FA_P_cong  c  b  b  a  ->FA_P_midp  b  a  m  ->FA_P_midp  m  b  d  ->FA_P_foot  f  d  b  c  ->
FA_P_perp  c  a  a  f  .
forall a b c o h d e: FA_Point,
FA_P_circum  o  a  b  c  ->FA_P_midp  h  c  b  ->FA_P_col  d  a  b  ->FA_P_col  d  o  h  ->FA_P_perp  e  a  a  o  ->FA_P_perp  e  c  c  o  ->
FA_P_cycl  a  o  e  d  .
forall a b c a1 b1 c1: FA_Point,
FA_P_cycl  a  b  c  a1  b1  c1  ->FA_P_cong  a1  b  a1  c  ->FA_P_cong  b1  a  b1  c  ->FA_P_cong  c1  a  c1  b  ->
FA_P_perp  a  a1  b1  c1  .
forall a b c a1 b1 c1 a2 b2 c2: FA_Point,
FA_P_cycl  a  b  c  a1  b1  c1  ->FA_P_cong  a1  b  a1  c  ->FA_P_cong  b1  a  b1  c  ->FA_P_cong  c1  a  c1  b  ->FA_P_foot  a2  a1  b1  c1  ->FA_P_foot  b2  b1  a1  c1  ->FA_P_foot  c2  c1  a1  b1  ->
FA_P_para  a  b  a2  b2  .
forall a b c d e g f h: FA_Point,
FA_P_para  a  d  b  c  ->FA_P_midp  e  a  b  ->FA_P_foot  g  e  c  d  ->FA_P_perp  a  g  b  g  ->FA_P_midp  f  c  d  ->FA_P_foot  h  f  a  b  ->
FA_P_perp  c  h  h  d  .
forall p q a n d b c e: FA_Point,
FA_P_cycl  a  b  c  d  ->FA_P_cong  a  p  a  q  ->FA_P_cong  a  b  a  c  ->FA_P_cong  d  b  d  c  ->FA_P_col  n  a  d  ->FA_P_foot  p  n  a  b  ->FA_P_foot  q  n  a  c  ->FA_P_circum  n  d  p  q  ->FA_P_col  e  p  q  ->FA_P_col  e  a  d  ->
FA_P_eqangle  a  b  e  e  b  c  .
forall p0 p1 p2 p3 p4 q0 q1 q2 q3 q4 m0 m1 m2 m3 m4: FA_Point,
FA_P_col  q0  p1  p2  q2  ->FA_P_col  q1  p2  p3  q3  ->FA_P_col  q2  p3  p4  q4  ->FA_P_col  q3  p4  p0  q0  ->FA_P_col  q4  p0  p1  q1  ->FA_P_cycl  m0  m1  q0  p0  p1  ->FA_P_cycl  m0  m4  q4  p0  p4  ->FA_P_cycl  m3  m4  q3  p3  p4  ->FA_P_cycl  m3  m2  q2  p2  p3  ->FA_P_cycl  m1  m2  q1  p1  p2  ->
FA_P_cycl  m0  m1  m2  m4  .
forall a b c d u v: FA_Point,
FA_P_cycl  a  b  c  d  ->FA_P_orthoc  u  a  b  d  ->FA_P_orthoc  v  a  c  d  ->
FA_P_para  u  v  b  c  .
forall a b c p o d e f: FA_Point,
FA_P_midp  o  a  b  ->FA_P_perp  a  c  c  b  ->FA_P_perp  a  p  p  b  ->FA_P_cong  o  a  o  d  ->FA_P_cong  c  d  c  b  ->FA_P_col  e  a  c  ->FA_P_col  e  p  b  ->FA_P_col  f  a  d  ->FA_P_col  f  p  c  ->
FA_P_perp  e  f  a  d  .
forall a b d c e f m o1 o2 o3 o4: FA_Point,
FA_P_col  a  b  c  ->FA_P_col  c  d  e  ->FA_P_col  e  f  b  ->FA_P_col  d  f  a  ->FA_P_cycl  m  a  b  f  ->FA_P_cycl  m  a  c  d  ->FA_P_pbisector  o1  a  b  ->FA_P_pbisector  o1  a  f  ->FA_P_pbisector  o2  b  c  ->FA_P_pbisector  o2  b  e  ->FA_P_pbisector  o3  d  f  ->FA_P_pbisector  o3  d  e  ->FA_P_pbisector  o4  a  c  ->FA_P_pbisector  o4  a  d  ->
FA_P_cycl  o1  o2  o3  o4  .
forall a b d c e f m o1 o2 o3 o4: FA_Point,
FA_P_col  a  b  c  ->FA_P_col  c  d  e  ->FA_P_col  e  f  b  ->FA_P_col  d  f  a  ->FA_P_cycl  m  a  b  f  ->FA_P_cycl  m  a  c  d  ->FA_P_pbisector  o1  a  b  ->FA_P_pbisector  o1  a  f  ->FA_P_pbisector  o2  b  c  ->FA_P_pbisector  o2  b  e  ->FA_P_pbisector  o3  d  f  ->FA_P_pbisector  o3  d  e  ->FA_P_pbisector  o4  a  c  ->FA_P_pbisector  o4  a  d  ->
FA_P_cycl  o1  o2  o3  m  .
