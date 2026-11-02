(* Candidate C5 ("abort-corrected Laur-Nyberg") in the ideal-commitment model.

   The man-in-the-middle talks to an ideal commitment functionality: after the
   commit phase its state s is independent of the honest message m and fixes the
   value w s it committed to; it may halt before the opening (halt s); after
   seeing m it decides whether to open validly (opn s m).  Coins used in the
   opening phase are w.l.o.g. sampled into s.

     Real = Pr[ I0 ] : opens validly and rel m (w s)               (GN0)
     B    = Pr[ I1 ] : opens validly on mbar, and rel m (w s)       (GN1, Laur)
     V    = Pr[ Inv] : did not halt, but opened invalidly           (post-opening abort)

   Results:
     c5_ideal : Real <= B + sqrt (B * V)
     c4_ideal : Real <= sqrt B
   With no post-opening aborts (V = 0) C5 is exactly the Laur-Nyberg bound. *)

pragma Goals:printall.

require import AllCore Distr DBool RealSeries StdRing StdOrder RealExp.
import RField RealOrder.

type state, message.

op ds : state distr.
op md : message distr.
op w    : state -> message.
op halt : state -> bool.
op opn  : state -> message -> bool.
op rel  : message -> message -> bool.

section Hypotheses.

declare axiom ds_ll : is_lossless ds.
declare axiom md_ll : is_lossless md.
declare axiom halt_opn s m : halt s => !opn s m.

module I0 = {
  proc main() : bool = {
    var sm;
    sm <$ ds `*` md;
    return opn sm.`1 sm.`2 /\ rel sm.`2 (w sm.`1);
  }
}.

module I1 = {
  proc main() : bool = {
    var smm;
    smm <$ ds `*` (md `*` md);
    return opn smm.`1 smm.`2.`1 /\ rel smm.`2.`2 (w smm.`1);
  }
}.

module Inv = {
  proc main() : bool = {
    var sm;
    sm <$ ds `*` md;
    return !halt sm.`1 /\ !opn sm.`1 sm.`2;
  }
}.


(* ------------------------------------------------------------------ *)
(* generic facts                                                       *)

lemma mu_dprod_exp ['a 'b] (da : 'a distr) (db : 'b distr) (P : 'a * 'b -> bool) :
  mu (da `*` db) P = E da (fun a => mu db (fun b => P (a, b))).
proof.
rewrite dprod_dlet dletE /E; apply eq_sum => a /=; rewrite mulrC; congr.
have -> : (fun (b : 'b) => dunit (a, b)) = dunit \o (fun (b : 'b) => (a, b)) by done.
by rewrite -/(dmap db (fun b => (a, b))) dmapE.
qed.

lemma hasE01 ['a] (d : 'a distr) (F : 'a -> real) :
  (forall x, 0%r <= F x <= 1%r) => hasE d F.
proof. by move=> h; apply (hasE_le _ _ (fun _ => 1%r)); [apply hasEC | smt()]. qed.

(* AM-GM with a free parameter, then optimise the parameter *)
lemma amgm_inf (X Y Z : real) :
  0%r <= Y => 0%r <= Z =>
  (forall t, 0%r < t => X <= (t * Y + Z / t) / 2%r) => X <= sqrt (Y * Z).
proof.
move=> ge0Y ge0Z h.
case: (Y = 0%r) => [eY|nY].
+ rewrite eY mul0r sqrt0; case: (X <= 0%r) => // /ltrNge gt0X.
  have gt0t : 0%r < Z / X + 1%r by smt(divr_ge0).
  have := h (Z / X + 1%r) gt0t; rewrite eY mulr0 /=.
  have : Z / (Z / X + 1%r) <= X.
  + rewrite ler_pdivr_mulr //; have -> : X * (Z / X + 1%r) = Z + X by field; smt().
    smt().
  smt().
case: (Z = 0%r) => [eZ|nZ].
+ rewrite eZ mulr0 sqrt0; case: (X <= 0%r) => // /ltrNge gt0X.
  have gtY : 0%r < Y by smt().
  have gt1t : 0%r < X / Y by smt(divr_gt0).
  have := h (X / Y) gt1t.
  move=> hX; have e : X / Y * Y = X by field; smt().
  smt().
have gtY : 0%r < Y by smt().
have gtZ : 0%r < Z by smt().
pose s := sqrt Y; pose r := sqrt Z.
have gts : 0%r < s by apply sqrt_gt0.
have gtr : 0%r < r by apply sqrt_gt0.
have sqK : forall x, 0%r <= x => sqrt x * sqrt x = x.
+ by move=> x ge0x; rewrite -sqrtM // -expr2 sqrtsq_ge0.
have eY : Y = s * s by rewrite /s sqK.
have eZ : Z = r * r by rewrite /r sqK.
have -> : sqrt (Y * Z) = s * r by rewrite sqrtM.
have gt2t : 0%r < r / s by apply divr_gt0.
have := h (r / s) gt2t.
have -> : r / s * Y + Z / (r / s) = 2%r * (s * r).
+ by rewrite eY eZ; field; smt().
smt().
qed.


(* ------------------------------------------------------------------ *)
(* per-state quantities                                                *)

op al (s : state) = mu md (opn s).
op q  (s : state) = mu md (fun m => rel m (w s)).
op f  (s : state) = mu md (fun m => opn s m /\ rel m (w s)).
op h  (s : state) = if halt s then 0%r else 1%r - al s.

lemma f_le s : 0%r <= f s <= al s /\ f s <= q s.
proof. by rewrite /f /al /q ge0_mu /=; split; apply mu_sub => /#. qed.

lemma al01 s : 0%r <= al s <= 1%r by smt(ge0_mu le1_mu).
lemma q01  s : 0%r <= q s <= 1%r by smt(ge0_mu le1_mu).
lemma h01  s : 0%r <= h s <= 1%r by smt(al01).

(* the key pointwise inequality: (f - al q)^2 <= al q (1 - al)^2 *)
lemma cov_sq (x a b : real) :
  0%r <= x => x <= a => x <= b => a <= 1%r => 0%r <= b =>
  0%r <= x - a * b => (x - a * b) * (x - a * b) <= (a * b) * ((1%r - a) * (1%r - a)).
proof.
move=> ge0x xa xb a1 ge0b D0.
have h1 : x - a * b <= x * (1%r - a).
+ have : a * x <= a * b by apply ler_wpmul2l; smt().
  have -> : x * (1%r - a) = x - a * x by ring.
  smt().
have h2 : x - a * b <= b * (1%r - a).
+ have -> : b * (1%r - a) = b - a * b by ring.
  smt().
have h3 : (x - a * b) * (x - a * b) <= (x * (1%r - a)) * (b * (1%r - a)).
+ by apply ler_pmul => //.
apply (ler_trans _ _ _ h3).
have -> : x * (1%r - a) * (b * (1%r - a)) = x * (b * ((1%r - a) * (1%r - a))) by ring.
have -> : a * b * ((1%r - a) * (1%r - a)) = a * (b * ((1%r - a) * (1%r - a))) by ring.
by apply ler_wpmul2r => //; smt().
qed.

lemma pointwise_c5 s t : 0%r < t =>
  f s <= al s * q s + (t * (al s * q s) + h s / t) / 2%r.
proof.
move=> gt0t.
have [[ge0f fa] fq] := f_le s.
have := al01 s; have := q01 s; move=> [ge0q q1] [ge0a a1].
case: (halt s) => hs.
+ have a0 : al s = 0%r.
  + by rewrite /al; apply mu0_false => m _ /=; apply halt_opn.
  rewrite /h hs a0 /=; smt().
rewrite /h hs /=.
pose D := f s - al s * q s; pose X := al s * q s; pose Y := (1%r - al s) * (1%r - al s).
case: (D <= 0%r) => [D0|/ltrNge D0].
+ have : 0%r <= (t * X + (1%r - al s) / t) / 2%r by smt(divr_ge0 mulr_ge0).
  smt().
have hD : D * D <= X * Y by apply cov_sq => //; smt().
have hY : Y <= 1%r - al s by smt().
pose R := (t * X + Y / t) / 2%r.
have ge0X : 0%r <= X by smt(mulr_ge0).
have ge0Y : 0%r <= Y by smt(mulr_ge0).
have ge0R : 0%r <= R by smt(divr_ge0 mulr_ge0).
have hR : X * Y <= R * R.
+ have e : R * R - X * Y = ((t * X - Y / t) / 2%r) * ((t * X - Y / t) / 2%r).
  + by rewrite /R; field; smt().
  have := ge0_sqr ((t * X - Y / t) / 2%r); rewrite expr2; smt().
have DR : D <= R.
+ case: (D <= R) => // /ltrNge.
  move=> RD; have : R * R < D * D by apply ltr_pmul => //.
  smt().
have : Y / t <= (1%r - al s) / t by apply ler_wpmul2r; smt(invr_ge0).
smt().
qed.

lemma pointwise_c4 s t : 0%r < t => f s <= (t * (al s * q s) + 1%r / t) / 2%r.
proof.
move=> gt0t.
have [[ge0f fa] fq] := f_le s.
have := al01 s; have := q01 s; move=> [ge0q q1] [ge0a a1].
pose X := al s * q s.
have hD : f s * f s <= X * 1%r by rewrite mulr1; apply ler_pmul.
pose R := (t * X + 1%r / t) / 2%r.
have ge0X : 0%r <= X by smt(mulr_ge0).
have ge0R : 0%r <= R by smt(divr_ge0 mulr_ge0).
have hR : X * 1%r <= R * R.
+ have e : R * R - X * 1%r = ((t * X - 1%r / t) / 2%r) * ((t * X - 1%r / t) / 2%r).
  + by rewrite /R; field; smt().
  have := ge0_sqr ((t * X - 1%r / t) / 2%r); rewrite expr2; smt().
case: (f s <= R) => // /ltrNge RD.
have : R * R < f s * f s by apply ltr_pmul => //.
smt().
qed.


(* ------------------------------------------------------------------ *)
(* the games as expectations                                           *)

lemma I0_E &m : Pr[ I0.main() @ &m : res ] = E ds f.
proof.
byphoare => //; proc; rnd; skip => />.
by rewrite mu_dprod_exp.
qed.

lemma I1_E &m : Pr[ I1.main() @ &m : res ] = E ds (fun s => al s * q s).
proof.
byphoare => //; proc; rnd; skip => />.
rewrite mu_dprod_exp; apply eq_exp => s _ /=.
by rewrite (dprodE (opn s) (fun m => rel m (w s))).
qed.

lemma Inv_E &m : Pr[ Inv.main() @ &m : res ] = E ds h.
proof.
byphoare => //; proc; rnd; skip => />.
rewrite mu_dprod_exp; apply eq_exp => s _ /=.
rewrite /h; case: (halt s) => hs /=; first by rewrite mu0.
by rewrite mu_not md_ll.
qed.


(* ------------------------------------------------------------------ *)
(* main results                                                        *)

lemma c5_family &m t : 0%r < t =>
  Pr[ I0.main() @ &m : res ]
  <= Pr[ I1.main() @ &m : res ]
   + (t * Pr[ I1.main() @ &m : res ] + Pr[ Inv.main() @ &m : res ] / t) / 2%r.
proof.
move=> gt0t; rewrite I0_E I1_E Inv_E.
pose B := E ds (fun s => al s * q s); pose V := E ds h.
have hB : hasE ds (fun s => al s * q s) by apply hasE01; smt(al01 q01 mulr_ge0 mulr_ile1).
have hH : hasE ds h by apply hasE01; apply h01.
have -> : B + (t * B + V / t) / 2%r
        = E ds (fun s => (1%r + t / 2%r) * (al s * q s) + (1%r / (2%r * t)) * h s).
+ rewrite expD; [by apply hasEZ | by apply hasEZ |].
  by rewrite !expZ /B /V; field; smt().
apply ler_exp.
+ by apply hasE01; smt(f_le al01).
+ by apply (hasE_le _ _ (fun s => (1%r + t / 2%r) + 1%r / (2%r * t))); [apply hasEC |
     move=> s /=; smt(al01 q01 h01 mulr_ge0 mulr_ile1 divr_ge0 ler_wpmul2l)].
move=> s /=; have := pointwise_c5 s t gt0t.
have -> : (1%r + t / 2%r) * (al s * q s) + 1%r / (2%r * t) * h s
        = al s * q s + (t * (al s * q s) + h s / t) / 2%r by field; smt().
done.
qed.

lemma c5_ideal &m :
  Pr[ I0.main() @ &m : res ]
  <= Pr[ I1.main() @ &m : res ]
   + sqrt (Pr[ I1.main() @ &m : res ] * Pr[ Inv.main() @ &m : res ]).
proof.
have := amgm_inf (Pr[ I0.main() @ &m : res ] - Pr[ I1.main() @ &m : res ])
                 Pr[ I1.main() @ &m : res ] Pr[ Inv.main() @ &m : res ] _ _ _.
+ by rewrite Pr[mu_ge0].
+ by rewrite Pr[mu_ge0].
+ by move=> t gt0t; have := c5_family &m t gt0t; smt().
smt().
qed.

lemma c4_ideal &m :
  Pr[ I0.main() @ &m : res ] <= sqrt (Pr[ I1.main() @ &m : res ]).
proof.
have := amgm_inf Pr[ I0.main() @ &m : res ] Pr[ I1.main() @ &m : res ] 1%r _ _ _ => //.
+ by rewrite Pr[mu_ge0].
+ move=> t gt0t; rewrite I0_E I1_E.
  have hB : hasE ds (fun s => al s * q s) by apply hasE01; smt(al01 q01 mulr_ge0 mulr_ile1).
  have -> : (t * E ds (fun s => al s * q s) + 1%r / t) / 2%r
          = E ds (fun s => (t / 2%r) * (al s * q s) + 1%r / (2%r * t)).
  + rewrite expD; [by apply hasEZ | by apply hasEC |].
    rewrite expZ expC; have := ds_ll; rewrite /is_lossless => ->; field; smt().
  apply ler_exp.
  + by apply hasE01; smt(f_le al01).
  + by apply (hasE_le _ _ (fun s => t / 2%r + 1%r / (2%r * t))); [apply hasEC |
       move=> s /=; smt(al01 q01 mulr_ge0 mulr_ile1 divr_ge0)].
  move=> s /=; have := pointwise_c4 s t gt0t.
  have -> : (t * (al s * q s) + 1%r / t) / 2%r
          = t / 2%r * (al s * q s) + 1%r / (2%r * t) by field; smt().
  done.
qed.

end section Hypotheses.
