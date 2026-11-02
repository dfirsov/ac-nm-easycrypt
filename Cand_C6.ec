(* Candidate C6: Laur's complemented two-world game (exercise 0717),
   generalised, and why it is too weak.

   Real game (b = 0, 1):
     pk <$ Gen; (m0, m1) <@ A.init(pk); (c, d) <$ Commit pk m_b;
     (c', T) <@ A.commit(c);  (T an efficient test, chosen at commit time)
     if (c' <> c) { (d', m') <@ A.decommit(m_b, d) }
     world 0 wins iff  valid /\ T m'      world 1 wins iff  valid /\ !T m'
     Adv6 = Pr[W0] + Pr[W1] - 1.
   Since Pr[W1] = 1 - Pr1[valid /\ T] - Pr1[!valid], C6 says
     Pr0[valid /\ T] <= Pr1[valid /\ T] + Pr1[!valid] + eps,
   i.e. it is candidate C3 (abort charged linearly), with the two worlds split.

   Model: an ideal commitment extended with an alpha-mauling functionality.
   After the commit phase the adversary's state s is independent of b and m.
   Either it committed blindly to s.`y, or it mauled c into c' that opens to
   s.`f m, which works only with probability alpha (coin u, sampled by the
   functionality and revealed only with the opening d).  After seeing m it
   decides whether to open (s.`opn).  Randomness of the adversary is in ds.

   Results:
     c6_sound    : alpha <= 1/2  =>  Adv6 <= 0 for every adversary
                   (alpha = 0 is the plain ideal commitment)
     c6_maul     : the mauling adversary has Adv6 = 2 alpha - 1, so 1/2 is
                   the exact threshold
     maul_c5     : the same mauling adversary, in the C5 game with R = (=),
                   has Real = alpha, B = alpha * cp, V = 1 - alpha, where cp
                   is the collision probability of md
     maul_c5_adv : hence Adv_C5 = alpha - alpha cp - sqrt (alpha cp (1 - alpha)),
                   which is about alpha when cp is negligible.
   So a 1/3-malleable functionality satisfies C6 but violates every
   sparse-relation bound Real <= q + negl that the protocol proofs need, and
   C5 rejects it.                                                           *)

pragma Goals:printall.

require import AllCore Distr DBool RealSeries StdRing StdOrder RealExp.
import Biased RField RealOrder.

type message.

type strat = {
  m0   : message;
  m1   : message;
  test : message -> bool;
  maul : bool;
  y    : message;
  f    : message -> message;
  opn  : message -> bool;
}.

op alpha : real.
section Hypotheses.

declare axiom alpha_ge0 : 0%r <= alpha.
declare axiom alpha_le1 : alpha <= 1%r.

op value (s : strat) (m : message) = if s.`maul then s.`f m else s.`y.
op valid (s : strat) (u : bool) (m : message) = s.`opn m /\ (s.`maul => u).

op W0 (ds : strat distr) =
  mu (ds `*` dbiased alpha) (fun (su : strat * bool) =>
    valid su.`1 su.`2 su.`1.`m0 /\ su.`1.`test (value su.`1 su.`1.`m0)).

op W1 (ds : strat distr) =
  mu (ds `*` dbiased alpha) (fun (su : strat * bool) =>
    valid su.`1 su.`2 su.`1.`m1 /\ !su.`1.`test (value su.`1 su.`1.`m1)).

op Adv6 (ds : strat distr) = W0 ds + W1 ds - 1%r.


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

lemma clamp_alpha : clamp alpha = alpha.
proof. smt(alpha_ge0 alpha_le1). qed.


(* ------------------------------------------------------------------ *)
(* C6 is sound below the threshold                                     *)

lemma pointwise_c6 s : alpha <= 1%r / 2%r =>
  mu (dbiased alpha) (fun u => valid s u s.`m0 /\ s.`test (value s s.`m0))
  + mu (dbiased alpha) (fun u => valid s u s.`m1 /\ !s.`test (value s s.`m1))
  <= 1%r.
proof.
move=> le_half; rewrite !dbiasedE clamp_alpha /valid /value /=.
case: (s.`maul) => /= _; smt(alpha_ge0).
qed.

lemma c6_sound (ds : strat distr) : is_lossless ds => alpha <= 1%r / 2%r =>
  Adv6 ds <= 0%r.
proof.
move=> ds_ll le_half; rewrite /Adv6 /W0 /W1 !mu_dprod_exp /=.
rewrite -expD; 1,2: by apply hasE01 => s; smt(ge0_mu le1_mu).
have : E ds (fun s => mu (dbiased alpha) (fun u => valid s u s.`m0 /\ s.`test (value s s.`m0))
                   + mu (dbiased alpha) (fun u => valid s u s.`m1 /\ !s.`test (value s s.`m1)))
       <= E ds (fun _ => 1%r).
+ apply ler_exp; last by move=> s /=; apply pointwise_c6.
  + apply (hasE_le _ _ (fun _ => 2%r)); first by apply hasEC.
    by move=> s /=; smt(ge0_mu le1_mu).
  by apply hasEC.
rewrite expC; move: ds_ll; rewrite /is_lossless => -> /= h; rewrite subr_le0; exact h.
qed.

(* the threshold is exact *)
lemma c6_maul (s : strat) :
  s.`maul => (forall m, s.`f m = m) => (forall m, s.`opn m) =>
  s.`test = pred1 s.`m0 => s.`m0 <> s.`m1 =>
  Adv6 (dunit s) = 2%r * alpha - 1%r.
proof.
move=> hm hf ho ht hne; rewrite /Adv6 /W0 /W1 !mu_dprod_exp !exp_dunit /=.
rewrite !dbiasedE clamp_alpha /valid /value hm !hf !ho ht /pred1 /=.
have -> /= : s.`m1 <> s.`m0 by smt().
ring.
qed.

(* ------------------------------------------------------------------ *)
(* the same mauling adversary in the C5 game                           *)

op Real5 (ds : strat distr) (md : message distr) (rel : message -> message -> bool) =
  mu (ds `*` (dbiased alpha `*` md)) (fun (x : strat * (bool * message)) =>
    valid x.`1 x.`2.`1 x.`2.`2 /\ rel x.`2.`2 (value x.`1 x.`2.`2)).

op B5 (ds : strat distr) (md : message distr) (rel : message -> message -> bool) =
  mu (ds `*` (dbiased alpha `*` (md `*` md))) (fun (x : strat * (bool * (message * message))) =>
    valid x.`1 x.`2.`1 x.`2.`2.`1 /\ rel x.`2.`2.`2 (value x.`1 x.`2.`2.`1)).

op V5 (ds : strat distr) (md : message distr) =
  mu (ds `*` (dbiased alpha `*` md)) (fun (x : strat * (bool * message)) =>
    !valid x.`1 x.`2.`1 x.`2.`2).

op cp (md : message distr) = mu (md `*` md) (fun (p : message * message) => p.`2 = p.`1).

lemma maul_c5 (s : strat) (md : message distr) : is_lossless md =>
  s.`maul => (forall m, s.`f m = m) => (forall m, s.`opn m) =>
     Real5 (dunit s) md (=) = alpha
  /\ B5 (dunit s) md (=) = alpha * cp md
  /\ V5 (dunit s) md = 1%r - alpha.
proof.
move=> md_ll hm hf ho; rewrite /Real5 /B5 /V5 !mu_dprod_exp !exp_dunit /=.
do! split.
+ rewrite (@mu_eq _ _ (fun (x : bool * message) => (fun (u : bool) => u) x.`1)) 1:/#.
  by rewrite (dprodEl _ _ (fun (u : bool) => u)) md_ll dbiasedE clamp_alpha.
+ rewrite (@mu_eq _ _ (fun (x : bool * (message * message)) =>
             (fun u => u) x.`1 /\ (fun (p : message * message) => p.`2 = p.`1) x.`2)) 1:/#.
  by rewrite (dprodE (fun (u : bool) => u) (fun (p : message * message) => p.`2 = p.`1)) dbiasedE clamp_alpha.
rewrite (@mu_eq _ _ (fun (x : bool * message) => (fun (u : bool) => !u) x.`1)) 1:/#.
by rewrite (dprodEl _ _ (fun (u : bool) => !u)) md_ll dbiasedE clamp_alpha.
qed.

lemma maul_c5_adv (s : strat) (md : message distr) : is_lossless md =>
  s.`maul => (forall m, s.`f m = m) => (forall m, s.`opn m) =>
  Real5 (dunit s) md (=) - B5 (dunit s) md (=)
    - sqrt (B5 (dunit s) md (=) * V5 (dunit s) md)
  = alpha - alpha * cp md - sqrt (alpha * cp md * (1%r - alpha)).
proof. by move=> md_ll hm hf ho; have [-> [-> ->]] := maul_c5 s md md_ll hm hf ho. qed.

(* ------------------------------------------------------------------ *)
(* C3 (Real <= B + V) is sound below the threshold: every adversary in  *)
(* the alpha-mauling model with alpha <= 1/2 satisfies it (paper,       *)
(* Proposition "c3", part 1).  Together with maul_c5_adv this shows     *)
(* that C3 accepts 1/2-malleable functionalities.                      *)

lemma pointwise_c3 (s : strat) (md : message distr) (rel : message -> message -> bool) :
  is_lossless md => alpha <= 1%r / 2%r =>
  mu (dbiased alpha `*` md) (fun (x : bool * message) =>
       valid s x.`1 x.`2 /\ rel x.`2 (value s x.`2))
  <= mu (dbiased alpha `*` (md `*` md)) (fun (x : bool * (message * message)) =>
       valid s x.`1 x.`2.`1 /\ rel x.`2.`2 (value s x.`2.`1))
   + mu (dbiased alpha `*` md) (fun (x : bool * message) => !valid s x.`1 x.`2).
proof.
move=> md_ll le_half.
case: (s.`maul) => hm.
+ (* a mauling state can open only when the functionality succeeds *)
  have h1 : mu (dbiased alpha `*` md) (fun (x : bool * message) =>
                valid s x.`1 x.`2 /\ rel x.`2 (value s x.`2))
          <= mu (dbiased alpha `*` md) (fun (x : bool * message) => (fun (u : bool) => u) x.`1).
  + by apply mu_sub => x /=; rewrite /valid hm.
  have h2 : mu (dbiased alpha `*` md) (fun (x : bool * message) => (fun (u : bool) => !u) x.`1)
          <= mu (dbiased alpha `*` md) (fun (x : bool * message) => !valid s x.`1 x.`2).
  + by apply mu_sub => x /=; rewrite /valid hm /#.
  move: h1 h2; rewrite (dprodEl _ _ (fun (u : bool) => u)) (dprodEl _ _ (fun (u : bool) => !u)).
  rewrite md_ll !dbiasedE clamp_alpha /=.
  smt(ge0_mu).
(* a blind state opens the fixed value s.`y *)
have eL : mu (dbiased alpha `*` md) (fun (x : bool * message) =>
              valid s x.`1 x.`2 /\ rel x.`2 (value s x.`2))
        = mu md (fun m => s.`opn m /\ rel m s.`y).
+ rewrite (@mu_eq _ _ (fun (x : bool * message) =>
             (fun m => s.`opn m /\ rel m s.`y) x.`2)) 1:/#.
  by rewrite (dprodEr _ _ (fun m => s.`opn m /\ rel m s.`y)) dbiased_ll.
have eB : mu (dbiased alpha `*` (md `*` md)) (fun (x : bool * (message * message)) =>
              valid s x.`1 x.`2.`1 /\ rel x.`2.`2 (value s x.`2.`1))
        = mu md (fun m => s.`opn m) * mu md (fun n => rel n s.`y).
+ rewrite (@mu_eq _ _ (fun (x : bool * (message * message)) =>
             (fun (p : message * message) => s.`opn p.`1 /\ rel p.`2 s.`y) x.`2)) 1:/#.
  rewrite (dprodEr _ _ (fun (p : message * message) => s.`opn p.`1 /\ rel p.`2 s.`y)).
  by rewrite dbiased_ll (dprodE (fun m => s.`opn m) (fun n => rel n s.`y)).
have eV : mu (dbiased alpha `*` md) (fun (x : bool * message) => !valid s x.`1 x.`2)
        = 1%r - mu md (fun m => s.`opn m).
+ rewrite (@mu_eq _ _ (fun (x : bool * message) => (fun m => !s.`opn m) x.`2)) 1:/#.
  rewrite (dprodEr _ _ (fun m => !s.`opn m)) dbiased_ll /=.
  by rewrite mu_not md_ll.
rewrite eL eB eV.
have f_le_e : mu md (fun m => s.`opn m /\ rel m s.`y) <= mu md (fun m => s.`opn m).
+ by apply mu_sub => m /#.
have f_le_q : mu md (fun m => s.`opn m /\ rel m s.`y) <= mu md (fun n => rel n s.`y).
+ by apply mu_sub => m /#.
have : 0%r <= (1%r - mu md (fun m => s.`opn m)) * (1%r - mu md (fun n => rel n s.`y)).
+ by apply mulr_ge0; smt(le1_mu).
smt().
qed.

lemma c3_sound (ds : strat distr) (md : message distr) (rel : message -> message -> bool) :
  is_lossless ds => is_lossless md => alpha <= 1%r / 2%r =>
  Real5 ds md rel <= B5 ds md rel + V5 ds md.
proof.
move=> ds_ll md_ll le_half; rewrite /Real5 /B5 /V5 !mu_dprod_exp /=.
rewrite -expD; 1,2: by apply hasE01 => s; smt(ge0_mu le1_mu).
apply ler_exp; last by move=> s /=; apply pointwise_c3.
+ by apply hasE01 => s; smt(ge0_mu le1_mu).
apply (hasE_le _ _ (fun _ => 2%r)); first by apply hasEC.
by move=> s /=; smt(ge0_mu le1_mu).
qed.

end section Hypotheses.
