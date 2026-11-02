(* The analytic core of the reduction from simulation (paper, Appendix A): the pointwise inequality

     2t R - t(2+t) q + 1  <=  h_rho(R, q) = (R + (1-R) rho) / (rho + q (1-rho)),
     rho = 1/(1+t)^2,

   which turns the geometric mixture of first-hit partition tests into the
   C5_t inequality  Real <= (1 + t/2) B + V/(2t).  With a = 1+t and
   z = q (a^2 - 1) the two cases are  (1 - z)(1 + z) <= 1  and
   (2a - 1 - z)(1 + z) <= a^2, i.e.  0 <= (a - 1 - z)^2.                    *)

require import AllCore StdRing StdOrder StdBigop RealExp.
import RField RealOrder Bigreal BRA.

op rho (t : real) = 1%r / ((1%r + t) * (1%r + t)).

op h (t : real) (r : bool) (q : real) =
  ((if r then 1%r else rho t)) / (rho t + q * (1%r - rho t)).

lemma pointwise (t q : real) (r : bool) : 0%r < t => 0%r <= q <= 1%r =>
  2%r * t * b2r r - t * (2%r + t) * q + 1%r <= h t r q.
proof.
move=> gt0t [ge0q le1q].
pose a := 1%r + t; pose z := q * (a * a - 1%r).
have gt1a : 1%r < a by smt().
have ge0z : 0%r <= z by rewrite /z; smt().
have aa0 : a * a <> 0%r by smt().
have rhoE : rho t = 1%r / (a * a) by done.
have den : rho t + q * (1%r - rho t) = (1%r + z) / (a * a).
+ by rewrite rhoE /z; field; rewrite expr2.
have lhs : t * (2%r + t) * q = z by rewrite /z /a; ring.
have pos : 0%r < (1%r + z) / (a * a) by smt().
rewrite /h den lhs; case: r => _ /=.
+ rewrite invf_div ler_pdivl_mulr 1:/#.
  have -> : (2%r * t - z + 1%r) * (1%r + z) = (2%r * a - 1%r - z) * (1%r + z) by rewrite /a; ring.
  have -> : a * a = (2%r * a - 1%r - z) * (1%r + z) + (a - 1%r - z) * (a - 1%r - z) by ring.
  by rewrite ler_addl -expr2 ge0_sqr.
rewrite rhoE.
have -> : 1%r / (a * a) / ((1%r + z) / (a * a)) = 1%r / (1%r + z) by field; rewrite ?expr2 //; smt().
rewrite ler_pdivl_mulr 1:/#.
have -> : (-z + 1%r) * (1%r + z) = 1%r - z * z by ring.
by rewrite ler_subl_addr ler_addl -expr2 ge0_sqr.
qed.


(* ------------------------------------------------------------------ *)
(* the truncated geometric mixture of first-hit scores                 *)
(*   g_k(R, q) = R (1 + (1-q) + ... + (1-q)^(k-1)) + (1-R) (1-q)^(k-1)  *)
(*   w_k = rho (1-rho)^(k-1),   mix_K = sum_{k=1..K} w_k g_k            *)

op S (q : real) (n : int) = bigi predT (fun j => (1%r - q) ^ j) 0 n.

op g (q : real) (r : bool) (k : int) = if r then S q k else (1%r - q) ^ (k - 1).

op w (t : real) (k : int) = rho t * (1%r - rho t) ^ (k - 1).

op mix (t q : real) (r : bool) (K : int) =
  bigi predT (fun k => w t k * g q r k) 1 (K + 1).

lemma rho_bounds t : 0%r < t => 0%r < rho t < 1%r.
proof.
move=> gt0t; rewrite /rho; split; first smt().
by move=> _; rewrite ltr_pdivr_mulr; smt().
qed.

lemma S_succ q n : 0 <= n => S q (n + 1) = S q n + (1%r - q) ^ n.
proof. by move=> ge0n; rewrite /S big_int_recr. qed.

lemma S_bounds q n : 0%r <= q <= 1%r => 0 <= n => 0%r <= S q n <= n%r.
proof.
move=> [ge0q le1q]; elim: n => [|n ge0n ih]; first by rewrite /S big_geq.
rewrite S_succ // fromintD.
have : 0%r <= (1%r - q) ^ n <= 1%r by smt(expr_ge0 exprn_ile1).
smt().
qed.

lemma mix_succ t q r K : 0 <= K =>
  mix t q r (K + 1) = mix t q r K + w t (K + 1) * g q r (K + 1).
proof. by move=> ge0K; rewrite /mix big_int_recr 1:/#. qed.

lemma mix_false t q K : 0 <= K =>
  (rho t + q * (1%r - rho t)) * mix t q false K
  = rho t * (1%r - ((1%r - rho t) * (1%r - q)) ^ K).
proof.
elim: K => [|K ge0K ih]; first by rewrite /mix big_geq // expr0.
rewrite mix_succ // mulrDr ih /w /g /= (exprMn _ _ (K + 1)) 1:/# !exprS //.
rewrite exprMn //; ring.
qed.

lemma mix_true t q K : 0 <= K =>
  (rho t + q * (1%r - rho t)) * mix t q true K
  = 1%r - ((1%r - rho t) * (1%r - q)) ^ K
    - (rho t + q * (1%r - rho t)) * (1%r - rho t) ^ K * S q K.
proof.
elim: K => [|K ge0K ih]; first by rewrite /mix /S !big_geq // expr0.
rewrite mix_succ // mulrDr ih /w /g /= S_succ // (exprMn _ _ (K + 1)) 1:/# !exprS //.
rewrite exprMn //; ring.
qed.

(* the mixture of the first K tests dominates the C5_t integrand up to
   the geometric tail (1-rho)^K (K + 1/rho), with 1/rho = (1+t)^2       *)
lemma mix_lower (t q : real) (r : bool) (K : int) :
  0%r < t => 0%r <= q <= 1%r => 0 <= K =>
  2%r * t * b2r r - t * (2%r + t) * q + 1%r
  <= mix t q r K + (1%r - rho t) ^ K * (K%r + 1%r / rho t).
proof.
move=> gt0t [ge0q le1q] ge0K.
have hp := pointwise t q r gt0t _; first by split.
have [gt0r lt1r] := rho_bounds t gt0t.
pose D := rho t + q * (1%r - rho t).
have geD : rho t <= D by rewrite /D; smt().
have gt0D : 0%r < D by smt().
have [ge0P le1P] : 0%r <= (1%r - rho t) ^ K <= 1%r.
+ smt(expr_ge0 exprn_ile1).
have [ge0Q le1Q] : 0%r <= (1%r - q) ^ K <= 1%r.
+ smt(expr_ge0 exprn_ile1).
have XK : ((1%r - rho t) * (1%r - q)) ^ K = (1%r - rho t) ^ K * (1%r - q) ^ K.
+ by rewrite exprMn.
have [ge0S leS] : 0%r <= S q K <= K%r by apply S_bounds.
have ge1i : 1%r <= 1%r / rho t by rewrite ler_pdivl_mulr //; smt().
apply (ler_trans (h t r q)) => //; rewrite /h -/D.
case: r hp => _ /=.
+ have e : mix t q true K = (1%r - ((1%r - rho t) * (1%r - q)) ^ K) / D
                            - (1%r - rho t) ^ K * S q K.
  + apply (mulfI D); first smt().
    by rewrite (mix_true t q K ge0K) -/D; field; smt().
  rewrite e XK.
  have : (1%r - rho t) ^ K * (1%r - q) ^ K / D <= (1%r - rho t) ^ K / rho t.
  + rewrite ler_pdivr_mulr // mulrAC ler_pdivl_mulr //.
    by apply ler_pmul; smt().
  have : (1%r - rho t) ^ K * S q K <= (1%r - rho t) ^ K * K%r by apply ler_wpmul2l.
  have -> : inv D = (1%r - (1%r - rho t) ^ K * (1%r - q) ^ K) / D
                      + (1%r - rho t) ^ K * (1%r - q) ^ K / D by field; smt().
  smt().
have e : mix t q false K = rho t * (1%r - ((1%r - rho t) * (1%r - q)) ^ K) / D.
+ apply (mulfI D); first smt().
  by rewrite (mix_false t q K ge0K) -/D; field; smt().
rewrite e XK.
have : rho t * ((1%r - rho t) ^ K * (1%r - q) ^ K) / D <= (1%r - rho t) ^ K.
+ rewrite ler_pdivr_mulr // mulrC; apply ler_pmul; smt().
have -> : rho t / D = rho t * (1%r - (1%r - rho t) ^ K * (1%r - q) ^ K) / D
                      + rho t * ((1%r - rho t) ^ K * (1%r - q) ^ K) / D by field; smt().
have : (1%r - rho t) ^ K <= (1%r - rho t) ^ K * (K%r + 1%r / rho t).
+ by rewrite -{1}(mulr1 ((1%r - rho t) ^ K)); apply ler_wpmul2l => //; smt().
smt().
qed.


(* ------------------------------------------------------------------ *)
(* the weight sums used by the reduction (with x = 1 - rho):           *)
(*   sum_{k<=K} w_k            = 1 - x^K                    <= 1        *)
(*   rho   sum_{k<=K} k w_k      = 1 - x^K (K rho + 1)        so <= 1/rho *)
(*   2rho^2 sum_{k<=K} C(k,2) w_k = 2x - x^K Q_K, Q_K >= 0   so <= x/rho^2 *)

lemma sum_w t K : 0 <= K =>
  bigi predT (fun k => w t k) 1 (K + 1) = 1%r - (1%r - rho t) ^ K.
proof.
elim: K => [|K ge0K ih]; first by rewrite big_geq // expr0.
rewrite big_int_recr 1:/# /= ih /w.
have -> : K + 1 - 1 = K by ring.
by rewrite exprS //; ring.
qed.

lemma sum_kw t K : 0 <= K =>
  rho t * bigi predT (fun k => k%r * w t k) 1 (K + 1)
  = 1%r - (1%r - rho t) ^ K * (K%r * rho t + 1%r).
proof.
elim: K => [|K ge0K ih]; first by rewrite big_geq // expr0.
rewrite big_int_recr 1:/# /= mulrDr ih /w.
have -> : K + 1 - 1 = K by ring.
by rewrite exprS // fromintD; ring.
qed.

lemma sum_c2w t K : 0 <= K =>
  2%r * rho t * rho t * bigi predT (fun k => k%r * (k%r - 1%r) / 2%r * w t k) 1 (K + 1)
  = 2%r * (1%r - rho t)
    - (1%r - rho t) ^ K * (rho t * rho t * K%r * (K%r - 1%r) + 2%r * rho t * (K%r - 1%r) + 2%r).
proof.
elim: K => [|K ge0K ih]; first by rewrite big_geq // expr0; ring.
rewrite big_int_recr 1:/# /= mulrDr ih /w.
have -> : K + 1 - 1 = K by ring.
by rewrite exprS // fromintD; field.
qed.

lemma sum_bounds t K : 0%r < t => 0 <= K =>
     bigi predT (fun k => w t k) 1 (K + 1) <= 1%r
  /\ bigi predT (fun k => k%r * w t k) 1 (K + 1) <= (1%r + t) ^ 2
  /\ bigi predT (fun k => k%r * (k%r - 1%r) / 2%r * w t k) 1 (K + 1) <= (1%r + t) ^ 4.
proof.
move=> gt0t ge0K.
have [gt0r lt1r] := rho_bounds t gt0t.
have ge0x : 0%r <= (1%r - rho t) ^ K by apply expr_ge0; smt().
have rinv : 1%r / rho t = (1%r + t) ^ 2.
+ rewrite /rho expr2; have h : (1%r + t) * (1%r + t) <> 0%r by smt().
  field => //; rewrite expr2; smt().
split; first by rewrite sum_w //; smt().
split.
+ have h := sum_kw t K ge0K.
  have : bigi predT (fun k => k%r * w t k) 1 (K + 1) <= 1%r / rho t.
  + rewrite ler_pdivl_mulr // mulrC h.
    have : 0%r <= (1%r - rho t) ^ K * (K%r * rho t + 1%r) by apply mulr_ge0; smt().
    smt().
  by rewrite rinv.
have h := sum_c2w t K ge0K.
have hQ : 0%r <= rho t * rho t * K%r * (K%r - 1%r) + 2%r * rho t * (K%r - 1%r) + 2%r.
+ case: (K = 0) => [-> /= | neK]; first smt().
  have hk : 0%r <= K%r - 1%r by smt().
  have : 0%r <= rho t * rho t * K%r * (K%r - 1%r).
  + by apply mulr_ge0 => //; apply mulr_ge0; [apply mulr_ge0 |]; smt().
  have : 0%r <= 2%r * rho t * (K%r - 1%r) by apply mulr_ge0 => //; smt().
  smt().
have : bigi predT (fun k => k%r * (k%r - 1%r) / 2%r * w t k) 1 (K + 1)
       <= (1%r - rho t) / (rho t * rho t).
+ rewrite ler_pdivl_mulr 1:/# mulrC.
  have : 0%r <= (1%r - rho t) ^ K
              * (rho t * rho t * K%r * (K%r - 1%r) + 2%r * rho t * (K%r - 1%r) + 2%r).
  + by apply mulr_ge0.
  move: h; pose S := bigi _ _ _ _; pose P := (1%r - rho t) ^ K * _.
  move=> h hP.
  have -> : rho t * rho t * S = (2%r * rho t * rho t * S) / 2%r by field.
  rewrite h; smt().
have : (1%r - rho t) / (rho t * rho t) <= (1%r + t) ^ 4.
+ have -> : (1%r + t) ^ 4 = (1%r / rho t) * (1%r / rho t) by rewrite rinv -exprD_nneg.
  have -> : 1%r / rho t * (1%r / rho t) = 1%r / (rho t * rho t).
  + by field; [smt() | rewrite expr2; smt()].
  apply ler_wpmul2r; [apply invr_ge0; smt() | smt()].
smt().
qed.


(* ------------------------------------------------------------------ *)
(* choosing t: for B <= V the family (1 + t/2) B + V/(2t) + err(t)/(2t) *)
(* comes within V/(2T) of B + sqrt(BV), with err(t) = (1+t)^2 e +       *)
(* (1+t)^4 c bounded by its value at T                                 *)

lemma err_le (t T e c : real) : 1%r <= t => t <= T => 0%r <= e => 0%r <= c =>
  ((1%r + t) ^ 2 * e + (1%r + t) ^ 4 * c) / (2%r * t)
  <= 2%r * T * e + 8%r * T ^ 3 * c.
proof.
move=> ge1t leT ge0e ge0c.
rewrite ler_pdivr_mulr 1:/#.
have h2 : (1%r + t) ^ 2 <= 4%r * t * t by rewrite expr2; smt().
have h4 : (1%r + t) ^ 4 <= 16%r * (t * t) * (t * t).
+ have -> : (1%r + t) ^ 4 = (1%r + t) ^ 2 * (1%r + t) ^ 2 by rewrite -exprD_nneg.
  have g0 : 0%r <= (1%r + t) ^ 2 by apply expr_ge0; smt().
  have -> : 16%r * (t * t) * (t * t) = (4%r * t * t) * (4%r * t * t) by ring.
  by apply ler_pmul => //.
have t3 : t * t * t <= T ^ 3.
+ have -> : T ^ 3 = T * T * T by rewrite (exprS _ 2) // expr2; ring.
  smt(ler_pmul).
have : (1%r + t) ^ 2 * e <= 4%r * t * t * e by smt().
have : (1%r + t) ^ 4 * c <= 16%r * (t * t) * (t * t) * c by smt().
have : 4%r * t * t * e <= 2%r * T * e * (2%r * t).
+ have -> : 4%r * t * t * e = (4%r * t * e) * t by ring.
  have -> : 2%r * T * e * (2%r * t) = (4%r * t * e) * T by ring.
  by apply ler_wpmul2l => //; smt().
have : 16%r * (t * t) * (t * t) * c <= 8%r * T ^ 3 * c * (2%r * t).
+ have -> : 16%r * (t * t) * (t * t) * c = (16%r * t * c) * (t * t * t) by ring.
  have -> : 8%r * T ^ 3 * c * (2%r * t) = (16%r * t * c) * T ^ 3 by ring.
  by apply ler_wpmul2l => //; smt().
smt().
qed.

lemma choose_t (B V e c T : real) :
  0%r <= B => B <= V => 1%r <= T => 0%r <= e => 0%r <= c =>
  exists t, 1%r <= t <= T /\
    (1%r + t / 2%r) * B + V / (2%r * t)
      + ((1%r + t) ^ 2 * e + (1%r + t) ^ 4 * c) / (2%r * t)
    <= B + sqrt (B * V) + V / (2%r * T) + 2%r * T * e + 8%r * T ^ 3 * c.
proof.
move=> ge0B leBV ge1T ge0e ge0c.
pose a := sqrt B; pose b := sqrt V.
have ge0a : 0%r <= a by apply ge0_sqrt.
have ge0b : 0%r <= b by apply ge0_sqrt.
have eB : B = a * a by rewrite /a -expr2 sqsqrt.
have eV : V = b * b by rewrite /b -expr2 sqsqrt //; smt().
have eBV : sqrt (B * V) = a * b by rewrite sqrtM //; smt().
have leab : a <= b by apply sqrt_mono => //; smt().
case: (B = 0%r) => [B0 | neB].
+ (* no baseline: take t = T *)
  exists T; split; first smt().
  have := err_le T T e c ge1T _ ge0e ge0c => //.
  move=> h; rewrite B0 mul0r sqrt0; smt().
have gt0a : 0%r < a by rewrite /a; apply sqrt_gt0; smt().
case: (b <= T * a) => [small | big].
+ (* the optimal t = b / a is admissible *)
  exists (b / a); split.
  + by split; [rewrite ler_pdivl_mulr // | rewrite ler_pdivr_mulr //]; smt().
  have := err_le (b / a) T e c _ _ ge0e ge0c.
  + by rewrite ler_pdivl_mulr //; smt().
  + by rewrite ler_pdivr_mulr //; smt().
  have gt0b : 0%r < b by smt().
  have -> : (1%r + b / a / 2%r) * B + V / (2%r * (b / a)) = B + sqrt (B * V).
  + by rewrite eBV eB eV; field; smt().
  have : 0%r <= V / (2%r * T) by apply divr_ge0; smt().
  smt().
(* t = T: the clipped choice costs at most V / (2T) *)
exists T; split; first smt().
have := err_le T T e c ge1T _ ge0e ge0c => //.
have : T * B / 2%r <= sqrt (B * V).
+ rewrite eBV eB.
  have : T * a <= b by smt().
  have : T * a * a <= b * a by smt(ler_pmul2r).
  smt().
have -> : (1%r + T / 2%r) * B + V / (2%r * T) = B + T * B / 2%r + V / (2%r * T) by field; smt().
smt().
qed.
