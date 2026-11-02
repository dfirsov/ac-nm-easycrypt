(* Real-number and expectation facts shared by the C5 ideal-model proofs. *)

pragma Goals:printall.

require import AllCore Distr DBool RealSeries StdRing StdOrder RealExp.
import RField RealOrder.

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

(* the per-state C5 inequality, for f = E[a R], a = E[a], q = E[R] *)
lemma pw_c5 (f a q t : real) :
  0%r < t => 0%r <= f => f <= a => f <= q => 0%r <= a => a <= 1%r => 0%r <= q => q <= 1%r =>
  f <= a * q + (t * (a * q) + (1%r - a) / t) / 2%r.
proof.
move=> gt0t ge0f fa fq ge0a a1 ge0q q1.
pose D := f - a * q; pose X := a * q; pose Y := (1%r - a) * (1%r - a).
case: (D <= 0%r) => [D0|/ltrNge D0].
+ have : 0%r <= (t * X + (1%r - a) / t) / 2%r by smt(divr_ge0 mulr_ge0).
  smt().
have hD : D * D <= X * Y by apply cov_sq => //; smt().
have hY : Y <= 1%r - a by smt().
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
have : Y / t <= (1%r - a) / t by apply ler_wpmul2r; smt(invr_ge0).
smt().
qed.

lemma E_b2r ['a] (d : 'a distr) (P : 'a -> bool) : E d (fun x => b2r (P x)) = mu d P.
proof. by rewrite /E muE; apply eq_sum => x /=; case: (P x). qed.
