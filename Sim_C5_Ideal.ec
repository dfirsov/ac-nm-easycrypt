(* Simulation-based NM implies AC-NM: the distribution-level part of the
   reduction (paper, Appendix A, Lemmas "test" and "mix").

   The adversary is described statistically: on challenge m, its run is a
   lossless distribution run m over outcomes Halt | Ref | Opn y.  md, R, run
   and the fallback value ystar are declared operators, so every lemma holds
   for all of them; Sim_C5_Game.ec applies the results to the reflected run
   distribution of an abstract adversary after its initialisation.

   The k-point first-hit partition test samples u <- dlist md k and a
   uniform index J, and runs the adversary on u_J; the test relation is
   R'(x, y) = [x = u_{jst u y}], where jst u y is the first index related
   to y (0 if there is none).  After a halt the test opens ystar, which
   loses if ystar is the challenge.

   Proved here (no admits):
     jst_insert_pos/0, none_hit   first-hit combinatorics, (1-q)^j for fresh samples
     dtest_fall, halt_part        the halting part of world J, up to Pr[u_J = ystar]
     dtest_hit                    the hit part of world J, via dlist_insert (the
                                  entries other than the challenge are fresh)
     sum_cJ                       summed over the worlds, the hit probabilities are
                                  exactly g_k (Sim_C5_Core.g)
     test_real                    E[ v g_k(R, q) ] + hsum k - k Pr[ystar]
                                  <= sum_J Pr[world J wins]  ( = k Real_k)
     prior_le, E_pairs,           the baseline with collisions:
     base_bound                   k E[prior_k] <= 1 + C(k,2) cp
     sim_c5_ideal                 THE THEOREM (unconditional, linear):
       2t Real <= t (2 + t) B + V
                  + sum_k w_k (sum_J Pr[world J wins] - k E[prior_k])
                  + sum_k w_k (haltp - hsum k)
                  + (sum_k k w_k) Pr[ystar] + (1+t)^4 cp + (1-rho)^K (K + 1 + 1/rho)
   where hsum k = sum_J Pr[halt /\ J = jst u ystar] and haltp = Pr[halt].
   The first sum is the CNM-AP advantage of the mixed test (times Z), the
   second the advantage of a hiding distinguisher (times 2Z), and the third
   the fallback collision; Sim_C5_Game.ec identifies them at game level. *)

pragma Goals:printall.

require import AllCore List FSet Distr DBool DList RealSeries RealFLub StdRing StdOrder StdBigop.
require Sim_C5_Core.
import RField RealOrder Bigreal BRA.

type msg.

(* the outcome of one run of the adversary *)
type outc = [ Halt | Ref | Opn of msg ].

(* md, R, run and ystar are declared: every lemma below holds for all of
   them (the section generalises over them), which is how the game-level
   proof (Sim_C5_Game.ec) applies these results to the run distribution of
   a concrete adversary after its initialisation. *)
section Hypotheses.

declare op md : msg distr.
declare op R  : msg -> msg -> bool.

(* q y = Pr[ n <- md : R n y ] *)
op q (y : msg) : real = mu md (fun n => R n y).

(* the adversary: its run on challenge m, and the fallback value *)
declare op run : msg -> outc distr.
declare op ystar : msg.

(* Pr[halt] in the AC-NM experiment *)
op haltp : real = E md (fun m => mu (run m) (pred1 Halt)).

(* the k-test in world J: u <- dlist md k, run the adversary on u_J *)
op dtest (k J : int) : (msg list * outc) distr =
  dlet (dlist md k) (fun u => dmap (run (nth witness u J)) (fun o => (u, o))).

(* the first index of u related to y, or 0 if there is none *)
op jst (u : msg list) (y : msg) : int =
  let j = find (fun a => R a y) u in if j < size u then j else 0.

(* success of the test in world J: the challenge u_J is the cell of the
   opened value; after a halt the fallback opens ystar, which also loses if
   ystar is the challenge itself (its commitment may equal c) *)
op win (J : int) (x : msg list * outc) : bool =
  let u = x.`1 in
  match x.`2 with
  | Halt  => nth witness u J = nth witness u (jst u ystar) /\ nth witness u J <> ystar
  | Ref   => false
  | Opn y => nth witness u J = nth witness u (jst u y)
  end.

(* the hit probability of world J, for a run on m with outcome o *)
op cJ (k J : int) (m : msg) (o : outc) : real =
  match o with
  | Halt  => 0%r
  | Ref   => 0%r
  | Opn y => mu (dlist md (k - 1)) (fun rest => jst (insert m rest J) y = J)
  end.

(* v g_k(R, q) for one run: the first-hit score of the opened value *)
op vg (k : int) (m : msg) (o : outc) : real =
  match o with
  | Halt  => 0%r
  | Ref   => 0%r
  | Opn y => Sim_C5_Core.g (q y) (R m y) k
  end.

(* the number of equal pairs i < j in u *)
op pairs (u : msg list) : int =
  with u = []     => 0
  with u = a :: t => count (pred1 a) t + pairs t.

(* the CNM-AP baseline of the k-test: md' is a uniform entry of u, and
   R'(x, y) = [x = u_{jst u y}] *)
op priork (u : msg list) : real =
  flub (fun y => mu (dmap (drange 0 (size u)) (nth witness u))
                    (pred1 (nth witness u (jst u y)))).

(* the collision probability of md *)
op cp : real = mu (md `*` md) (fun (p : msg * msg) => p.`1 = p.`2).

(* counts capped at the expected list size, so that they are bounded *)
op cntk (k : int) (a : msg) (t : msg list) : int =
  if size t = k then count (pred1 a) t else 0.
op pairsk (k : int) (u : msg list) : int =
  if size u = k then pairs u else 0.

(* the AC-NM quantities of the adversary, per outcome *)
op realf (m : msg) (o : outc) : real =
  match o with Halt => 0%r | Ref => 0%r | Opn y => b2r (R m y) end.
op bf (o : outc) : real =
  match o with Halt => 0%r | Ref => 0%r | Opn y => q y end.
op vf (o : outc) : real =
  match o with Halt => 0%r | Ref => 1%r | Opn y => 0%r end.
op pvf (o : outc) : real =
  match o with Halt => 0%r | Ref => 0%r | Opn y => 1%r end.

op RealS : real = E md (fun m => E (run m) (realf m)).
op Bl    : real = E md (fun m => E (run m) bf).
op Vl    : real = E md (fun m => E (run m) vf).
op Pv    : real = E md (fun m => E (run m) pvf).

(* the C5_t integrand on a valid opening *)
op lin (t : real) (m : msg) (o : outc) : real =
  match o with
  | Halt  => 0%r
  | Ref   => 0%r
  | Opn y => 2%r * t * b2r (R m y) - t * (2%r + t) * q y + 1%r
  end.

(* the halting part of the k-test, summed over the worlds: halt and J is
   the cell of ystar.  If halting did not depend on the challenge this would
   be exactly haltp; in general the gap haltp - hsum k is the advantage of
   a hiding distinguisher (Sim_C5_Game.ec). *)
op hsum (k : int) : real =
  bigi predT (fun J => mu (dtest k J)
                (fun (x : msg list * outc) => x.`2 = Halt /\ J = jst x.`1 ystar)) 0 k.

declare axiom md_ll : is_lossless md.
declare axiom run_ll m : is_lossless (run m).

(* -------------------------------------------------------------------- *)
(* (H1) the first hit in insert m rest j                                *)

lemma jst_insert_pos (m y : msg) (rest : msg list) (j : int) :
  0 < j <= size rest =>
  jst (insert m rest j) y = j
  <=> R m y /\ all (fun a => !R a y) (take j rest).
proof.
move=> [gt0j lej]; rewrite /jst /insert /= find_cat.
have szt : size (take j rest) = j by rewrite size_take; smt().
rewrite szt size_cat /= size_take 1:/# size_drop 1:/#.
have -> : all (fun a => !R a y) (take j rest) = !has (fun a => R a y) (take j rest).
+ by rewrite -all_predC.
case: (has (fun a => R a y) (take j rest)) => hh /=.
+ have := has_find (fun a => R a y) (take j rest); rewrite hh szt /= => lt.
  smt(find_ge0).
by case: (R m y) => hm /=; smt(find_ge0 find_size).
qed.

lemma jst_insert_0 (m y : msg) (rest : msg list) :
  jst (insert m rest 0) y = 0
  <=> R m y \/ all (fun a => !R a y) rest.
proof.
rewrite insert0 /jst /=.
case: (R m y) => hm /=; first smt().
have -> : all (fun a => !R a y) rest = !has (fun a => R a y) rest by rewrite -all_predC.
have := has_find (fun a => R a y) rest.
smt(find_ge0 find_size).
qed.

(* -------------------------------------------------------------------- *)
(* (H2) no hit among the first j fresh samples                          *)

lemma none_hit (y : msg) (j n : int) : 0 <= j <= n =>
  mu (dlist md n) (fun rest => all (fun a => !R a y) (take j rest))
  = (1%r - q y) ^ j.
proof.
move=> [ge0j lejn].
rewrite (mu_eq_support _ _ (fun xs => forall i, i \in rangeset 0 j =>
                                         (fun a => !R a y) (nth witness xs i))).
+ move=> xs; rewrite supp_dlist 1:/# => -[szxs _] /=.
  rewrite -(all_nthP (fun a => !R a y) (take j xs) witness) size_take 1:/#.
  rewrite (_ : (if j < size xs then j else size xs) = j) 1:/#.
  apply eq_iff; split => h i.
  + by rewrite mem_rangeset => hi; have := h i hi; rewrite nth_take 1,2:/#.
  by move=> hi; rewrite nth_take 1,2:/#; apply h; rewrite mem_rangeset.
rewrite (dlist_setE witness md (fun a => !R a y) n (rangeset 0 j)).
+ by apply md_ll.
+ smt().
+ by move=> i; rewrite mem_rangeset /#.
rewrite card_rangeset (_ : max 0 (j - 0) = j) 1:/#.
by rewrite mu_not md_ll /q.
qed.

(* -------------------------------------------------------------------- *)
(* S1: the halting part of world J                                      *)

(* -------------------------------------------------------------------- *)
(* S2: summed over the worlds, the halting part is at least Pr[halt]    *)

lemma jst_range (u : msg list) (y : msg) : 0 < size u => 0 <= jst u y < size u.
proof. by move=> gt0; rewrite /jst /=; smt(find_ge0). qed.

lemma sum_partition ['a] (d : 'a distr) (f : 'a -> int) (i : int) : 0 <= i =>
  bigi predT (fun J => mu d (fun x => f x = J)) 0 i = mu d (fun x => 0 <= f x < i).
proof.
elim: i => [|i ge0i ih].
+ by rewrite big_geq // (_ : (fun x => 0 <= f x < 0) = pred0) 1:/# mu0.
rewrite big_int_recr //= ih.
rewrite (mu_eq _ (fun x => 0 <= f x < i + 1) (predU (fun x => 0 <= f x < i) (fun x => f x = i))) 1:/#.
by rewrite mu_disjoint 1:/#.
qed.

lemma halt_sum (k : int) : 1 <= k =>
  1%r <= bigi predT (fun J => mu (dlist md k)
                     (fun u => nth witness u J = nth witness u (jst u ystar))) 0 k.
proof.
move=> ge1k.
have : bigi predT (fun J => mu (dlist md k) (fun u => jst u ystar = J)) 0 k = 1%r.
+ rewrite sum_partition 1:/#.
  rewrite (mu_eq_support _ _ predT); last by apply dlist_ll; apply md_ll.
  by move=> u; rewrite supp_dlist 1:/# => -[szu _]; smt(jst_range).
move=> <-; apply ler_sum => J _ /=.
by apply mu_sub => u /= ->.
qed.

(* -------------------------------------------------------------------- *)
(* S3: the hit part of world J, via dlist_insert                        *)

lemma mu_dlet_E ['a 'b] (d : 'a distr) (F : 'a -> 'b distr) (P : 'b -> bool) :
  mu (dlet d F) P = E d (fun x => mu (F x) P).
proof. by rewrite dletE /E; apply eq_sum => x /=; ring. qed.

lemma exp_b2r ['a] (d : 'a distr) (P : 'a -> bool) :
  E d (fun x => b2r (P x)) = mu d P.
proof. by rewrite /E muE; apply eq_sum => x /=; case: (P x). qed.

lemma dtest_hit (k J : int) : 0 <= J < k =>
  mu (dtest k J) (fun (x : msg list * outc) => exists y, x.`2 = Opn y /\ jst x.`1 y = J)
  = E md (fun m => E (run m) (fun o => cJ k J m o)).
proof.
move=> [ge0J ltJk].
have dl : dlist md k = dmap (md `*` dlist md (k - 1)) (fun (x : msg * msg list) => insert x.`1 x.`2 J).
+ have := dlist_insert witness J (k - 1) md _ _; 1,2: smt().
  by rewrite (_ : k - 1 + 1 = k) 1:/#.
rewrite /dtest dl dlet_dmap dprod_dlet dlet_dlet mu_dlet_E.
apply eq_exp => m _ /=.
rewrite dlet_dlet.
rewrite (in_eq_dlet _ (fun (r : msg list) => dmap (run m) (fun o => (insert m r J, o)))).
+ move=> r; rewrite supp_dlist 1:/# => -[szr _] /=.
  by rewrite dlet_unit /= nth_insert 1:/#.
rewrite (_ : (fun (r : msg list) => dmap (run m) (fun (o : outc) => (insert m r J, o)))
           = (fun r => dlet (run m) (fun o => dunit (insert m r J, o)))).
+ by apply fun_ext => r; rewrite -dlet_dunit.
rewrite dlet_swap mu_dlet_E.
apply eq_exp => o _ /=.
rewrite (_ : (fun (x1 : msg list) => dunit (insert m x1 J, o))
           = dunit \o (fun (x1 : msg list) => (insert m x1 J, o))) //.
rewrite dlet_dunit dmapE /(\o) /cJ.
case: o => [| | y] /=.
+ by rewrite (_ : (fun (_ : msg list) => false) = pred0) // mu0.
+ by rewrite (_ : (fun (_ : msg list) => false) = pred0) // mu0.
by apply mu_eq => r /=; smt().
qed.

(* -------------------------------------------------------------------- *)
(* S4: summed over the worlds, the hit probabilities are exactly g_k    *)

lemma cJ_pos (k J : int) (m y : msg) : 0 < J < k =>
  cJ k J m (Opn y) = if R m y then (1%r - q y) ^ J else 0%r.
proof.
move=> [gt0J ltJk]; rewrite /cJ /=.
rewrite (mu_eq_support _ _ (fun rest => R m y /\ all (fun a => !R a y) (take J rest))).
+ move=> r; rewrite supp_dlist 1:/# => -[szr _] /=.
  by rewrite jst_insert_pos 1:/#.
case: (R m y) => hm /=; first by apply none_hit; smt().
by rewrite (_ : (fun (_ : msg list) => false) = pred0) // mu0.
qed.

lemma cJ_0 (k : int) (m y : msg) : 0 < k =>
  cJ k 0 m (Opn y) = if R m y then 1%r else (1%r - q y) ^ (k - 1).
proof.
move=> gt0k; rewrite /cJ /=.
rewrite (mu_eq_support _ _ (fun rest => R m y \/ all (fun a => !R a y) (take (k - 1) rest))).
+ move=> r; rewrite supp_dlist 1:/# => -[szr _] /=.
  by rewrite -(insert0 m r) jst_insert_0 take_oversize 1:/#.
case: (R m y) => hm /=.
+ rewrite (_ : (fun (_ : msg list) => true) = predT) //.
  by apply dlist_ll; apply md_ll.
by apply none_hit; smt().
qed.

lemma sum_cJ (k : int) (m : msg) (o : outc) : 0 < k =>
  bigi predT (fun J => cJ k J m o) 0 k = vg k m o.
proof.
move=> gt0k; case: o => [| | y].
+ by rewrite /vg /cJ /= big1_eq.
+ by rewrite /vg /cJ /= big1_eq.
rewrite /vg /= (big_ltn 0 k) 1:// /= cJ_0 //.
rewrite (eq_big_int 1 k _ (fun J => if R m y then (1%r - q y) ^ J else 0%r)).
+ by move=> J hJ /=; rewrite cJ_pos /#.
rewrite /Sim_C5_Core.g; case: (R m y) => hm /=.
+ rewrite /Sim_C5_Core.S (big_ltn 0 k) 1:// /= expr0.
  done.
by rewrite big1_eq.
qed.

(* -------------------------------------------------------------------- *)
(* S5: linearity for finite sums of bounded functions                   *)

lemma hasE01 ['a] (d : 'a distr) (F : 'a -> real) :
  (forall x, 0%r <= F x <= 1%r) => hasE d F.
proof. by move=> h; apply (hasE_le _ _ (fun _ => 1%r)); [apply hasEC | smt()]. qed.

lemma exp01 ['a] (d : 'a distr) (F : 'a -> real) :
  (forall x, 0%r <= F x <= 1%r) => 0%r <= E d F <= 1%r.
proof.
move=> h; split; first by apply exp_ge0 => x; smt().
move=> _; apply (ler_trans (E d (fun (_ : 'a) => 1%r))).
+ apply ler_exp; [by apply hasE01 | by apply hasEC | smt()].
by rewrite expC; smt(le1_mu).
qed.

lemma exp01k ['a] (c : real) (d : 'a distr) (F : 'a -> real) : 0%r <= c =>
  (forall x, 0%r <= F x <= c) => 0%r <= E d F <= c.
proof.
move=> ge0c h; split; first by apply exp_ge0 => x; smt().
move=> _; apply (ler_trans (E d (fun (_ : 'a) => c))).
+ apply ler_exp; [ | by apply hasEC | smt()].
  by apply (hasE_le _ _ (fun _ => c)); [apply hasEC | smt()].
by rewrite expC; smt(le1_mu ge0_mu).
qed.

lemma sum_exp ['a] (d : 'a distr) (f : int -> 'a -> real) (k : int) :
  0 <= k => (forall J x, 0%r <= f J x <= 1%r) =>
  bigi predT (fun J => E d (f J)) 0 k = E d (fun x => bigi predT (fun J => f J x) 0 k).
proof.
move=> ge0k hf; elim: k ge0k => [|k ge0k ih].
+ by rewrite big_geq // (eq_exp _ _ (fun _ => 0%r)) => [x _ /=|]; [rewrite big_geq | rewrite expC].
rewrite big_int_recr //= ih.
have hsum : forall x, 0%r <= bigi predT (fun J => f J x) 0 k <= k%r.
+ move=> x; split; first by apply sumr_ge0 => J _; smt().
  have := ler_sum predT (fun J => f J x) (fun _ => 1%r) (range 0 k) _; 1: smt().
  have -> : bigi predT (fun (_ : int) => 1%r) 0 k = k%r.
  + by rewrite sumri_const // intmulr /=.
  done.
rewrite -expD.
+ apply (hasE_le _ _ (fun _ => k%r)); first by apply hasEC.
  by move=> x /=; have := hsum x; smt().
+ by apply hasE01 => x; apply hf.
by apply eq_exp => x _ /=; rewrite big_int_recr.
qed.

(* -------------------------------------------------------------------- *)
(* S6: the per-k inequality                                             *)

lemma cJ_01 (k J : int) (m : msg) (o : outc) : 0%r <= cJ k J m o <= 1%r.
proof. by rewrite /cJ; case: o => /= *; smt(ge0_mu le1_mu). qed.

(* the fallback loses only if ystar is the challenge *)
lemma dtest_fall (k J : int) : 0 <= J < k =>
  mu (dtest k J) (fun (x : msg list * outc) => nth witness x.`1 J = ystar) = mu1 md ystar.
proof.
move=> [ge0J ltJk].
have dl : dlist md k = dmap (md `*` dlist md (k - 1)) (fun (x : msg * msg list) => insert x.`1 x.`2 J).
+ have := dlist_insert witness J (k - 1) md _ _; 1,2: smt().
  by rewrite (_ : k - 1 + 1 = k) 1:/#.
rewrite /dtest mu_dlet_E.
rewrite (eq_exp _ _ (fun u => b2r (nth witness u J = ystar))).
+ move=> u _ /=; rewrite dmapE /(\o) /=.
  case: (nth witness u J = ystar) => _ /=.
  + by rewrite (_ : (fun (_ : outc) => true) = predT) // run_ll.
  by rewrite (_ : (fun (_ : outc) => false) = pred0) // mu0.
rewrite exp_b2r dl dmapE /(\o) /=.
rewrite (mu_eq_support _ _ (fun (x : msg * msg list) => pred1 ystar x.`1)).
+ move=> -[m r]; rewrite supp_dprod supp_dlist 1:/# /= => -[_ [szr _]].
  by rewrite nth_insert 1:/# /pred1.
by rewrite (dprodEl md (dlist md (k - 1)) (pred1 ystar)) (dlist_ll md (k - 1) md_ll).
qed.

(* the halting part of world J, with the fallback collision *)
lemma halt_part (k J : int) : 0 <= J < k =>
  mu (dtest k J) (fun (x : msg list * outc) => x.`2 = Halt /\ J = jst x.`1 ystar)
  <= mu (dtest k J) (fun (x : msg list * outc) => x.`2 = Halt /\ win J x) + mu1 md ystar.
proof.
move=> hJ; rewrite -(dtest_fall k J hJ).
have h := mu_sub (dtest k J)
  (fun (x : msg list * outc) => x.`2 = Halt /\ J = jst x.`1 ystar)
  (predU (fun (x : msg list * outc) => x.`2 = Halt /\ win J x)
         (fun (x : msg list * outc) => nth witness x.`1 J = ystar)) _.
+ by move=> -[u o] /= [-> ->]; rewrite /predU /win /=; smt().
by move: h; rewrite mu_or; smt(ge0_mu).
qed.

lemma test_real (k : int) : 1 <= k =>
  E md (fun m => E (run m) (fun o => vg k m o)) + hsum k - k%r * mu1 md ystar
  <= bigi predT (fun J => mu (dtest k J) (win J)) 0 k.
proof.
move=> ge1k.
(* split each world into its halting part and its hit part *)
have hsplit : forall J, 0 <= J < k =>
    mu (dtest k J) (fun (x : msg list * outc) => x.`2 = Halt /\ J = jst x.`1 ystar)
  - mu1 md ystar
  + E md (fun m => E (run m) (fun o => cJ k J m o))
  <= mu (dtest k J) (win J).
+ move=> J hJ; have := halt_part k J hJ; rewrite -dtest_hit //.
  have : mu (dtest k J) (fun (x : msg list * outc) => x.`2 = Halt /\ win J x)
       + mu (dtest k J) (fun (x : msg list * outc) => exists y, x.`2 = Opn y /\ jst x.`1 y = J)
       <= mu (dtest k J) (win J).
  + rewrite -mu_disjoint; first by move=> x /#.
    apply mu_sub => -[u o] /=; rewrite /predU /win /=; case: o => [| | y] /=; smt().
  smt().
have : bigi predT (fun J =>
           mu (dtest k J) (fun (x : msg list * outc) => x.`2 = Halt /\ J = jst x.`1 ystar)
         - mu1 md ystar
         + E md (fun m => E (run m) (fun o => cJ k J m o))) 0 k
       <= bigi predT (fun J => mu (dtest k J) (win J)) 0 k.
+ apply ler_sum_seq => J /mem_range hJ _ /=; apply hsplit; smt().
rewrite big_split /= big_split /= sumri_const 1:/#.
have -> : bigi predT (fun J => E md (fun m => E (run m) (fun o => cJ k J m o))) 0 k
        = E md (fun m => E (run m) (vg k m)).
+ rewrite sum_exp 1:/#.
  + by move=> J m; apply exp01 => o; apply cJ_01.
  apply eq_exp => m _ /=; rewrite sum_exp 1:/#; first by move=> J o; apply cJ_01.
  by apply eq_exp => o _ /=; rewrite sum_cJ 1:/#.
rewrite /hsum intmulr (_ : k - 0 = k) 1:/#.
by move=> h; apply: (ler_trans _ _ _ _ h); apply lerr_eq; ring.
qed.

(* -------------------------------------------------------------------- *)
(* B1: the baseline of the k-test, with collisions                      *)

lemma pairs_ge0 (u : msg list) : 0 <= pairs u.
proof. by elim: u => [|a t ih] //=; smt(count_ge0). qed.

lemma count_le_pairs (v : msg) (u : msg list) : count (pred1 v) u <= 1 + pairs u.
proof.
elim: u => [|a t ih] /=; first done.
rewrite /pred1; case: (a = v) => [-> | ne] /=.
+ by rewrite b2i1; smt(pairs_ge0).
rewrite b2i0 /=.
have := ih; rewrite /pred1; smt(count_ge0).
qed.

lemma prior_le (u : msg list) : 0 < size u =>
  priork u <= (1 + pairs u)%r / (size u)%r.
proof.
move=> gt0; apply flub_le_ub => y /=.
rewrite dmapE /(\o) drangeE /=.
pose v := nth witness u (jst u y).
have -> : count (fun i => pred1 v (nth witness u i)) (range 0 (size u))
        = count (pred1 v) u.
+ have := count_map (fun i => nth witness u i) (pred1 v) (range 0 (size u)).
  by rewrite map_nth_range => ->.
apply ler_pmul2r; first by apply invr_gt0; smt().
by rewrite le_fromint; apply count_le_pairs.
qed.

(* -------------------------------------------------------------------- *)
(* B2: E[ pairs ] = C(k,2) cp                                           *)

lemma hasE_supp ['a] (d : 'a distr) (f : 'a -> real) (c : real) :
  (forall x, x \in d => `|f x| <= c) => hasE d f.
proof.
move=> h; have hg : hasE d (fun x => if x \in d then f x else 0%r).
+ apply (hasE_le _ _ (fun _ => c)); first by apply hasEC.
  by move=> x /=; case: (x \in d) => [/h | _]; smt().
move: hg; rewrite /hasE; apply eq_summable => x /=.
by case: (x \in d) => // /supportPn ->.
qed.


lemma exp_dprod ['a 'b] (da : 'a distr) (db : 'b distr) (f : 'a * 'b -> real) (c : real) :
  (forall x, `|f x| <= `|c|) =>
  E (da `*` db) f = E da (fun a => E db (fun b => f (a, b))).
proof.
move=> hf; rewrite dprod_dlet exp_dlet.
+ by apply (hasE_le _ _ (fun _ => c)); [apply hasEC | smt()].
apply eq_exp => a _ /=; rewrite exp_dlet.
+ by apply (hasE_le _ _ (fun _ => c)); [apply hasEC | smt()].
by apply eq_exp => b _ /=; rewrite exp_dunit.
qed.

lemma pairs_le (u : msg list) : pairs u <= size u * size u.
proof. by elim: u => [|a t ih] //=; smt(count_size size_ge0). qed.

lemma cntk_bound (k : int) (a : msg) (t : msg list) : 0 <= k =>
  `|(cntk k a t)%r| <= `|k%r|.
proof.
move=> ge0k; rewrite /cntk; case: (size t = k) => hs /=; last smt().
have h1 := count_size (pred1 a) t; have h2 := count_ge0 (pred1 a) t.
rewrite ger0_norm 1:le_fromint // ger0_norm 1:le_fromint // le_fromint; smt().
qed.

lemma pairsk_bound (k : int) (u : msg list) : 0 <= k =>
  `|(pairsk k u)%r| <= `|(k * k)%r|.
proof.
move=> ge0k; rewrite /pairsk; case: (size u = k) => hs /=; last smt().
have h1 := pairs_le u; have h2 := pairs_ge0 u; rewrite hs in h1.
rewrite ger0_norm 1:le_fromint 1:// ger0_norm 1:le_fromint 1:/# le_fromint //.
qed.

lemma E_count (a : msg) (k : int) : 0 <= k =>
  E (dlist md k) (fun t => (cntk k a t)%r) = k%r * mu1 md a.
proof.
elim: k => [|k ge0k ih].
+ by rewrite dlist0 // exp_dunit /cntk.
rewrite dlistS // exp_dmap.
+ by apply (hasE_le _ _ (fun _ => (k + 1)%r)); [apply hasEC | move=> x /=; apply cntk_bound; smt()].
rewrite (eq_exp _ _ (fun (p : msg * msg list) => b2r (p.`1 = a) + (cntk k a p.`2)%r)).
+ move=> [b t]; rewrite supp_dprod supp_dlist // => -[_ [szt _]] /=.
  rewrite /(\o) /cntk /= szt /= (_ : 1 + k = k + 1) 1:/# /= fromintD.
  by case: (b = a) => h /=; rewrite ?b2i1 ?b2i0.
rewrite expD.
+ by apply (hasE_le _ _ (fun _ => 1%r)); [apply hasEC | smt()].
+ by apply (hasE_le _ _ (fun _ => k%r)); [apply hasEC | move=> x /=; apply cntk_bound; smt()].
rewrite exp_b2r (dprodEl _ _ (fun b => b = a)) dlist_ll; first by apply md_ll.
rewrite (exp_dprod _ _ _ k%r); first by move=> x /=; apply cntk_bound; smt().
rewrite /= expC md_ll ih /=.
rewrite (_ : (fun (b : msg) => b = a) = pred1 a) 1:/# fromintD; ring.
qed.

lemma cp_E : cp = E md (fun a => mu1 md a).
proof.
rewrite /cp dprod_dlet mu_dlet_E; apply eq_exp => a _ /=.
rewrite mu_dlet_E (eq_exp _ _ (fun b => b2r (a = b))).
+ by move=> b _ /=; rewrite dunitE.
by rewrite exp_b2r; apply mu_eq => b /#.
qed.

lemma E_pairs (k : int) : 0 <= k =>
  E (dlist md k) (fun u => (pairsk k u)%r) = (k * (k - 1))%r / 2%r * cp.
proof.
elim: k => [|k ge0k ih].
+ by rewrite dlist0 // exp_dunit /pairsk.
rewrite dlistS // exp_dmap.
+ by apply (hasE_le _ _ (fun _ => ((k + 1) * (k + 1))%r)); [apply hasEC | move=> x /=; apply pairsk_bound; smt()].
rewrite (eq_exp _ _ (fun (p : msg * msg list) => (cntk k p.`1 p.`2)%r + (pairsk k p.`2)%r)).
+ move=> [b t]; rewrite supp_dprod supp_dlist // => -[_ [szt _]] /=.
  by rewrite /(\o) /cntk /pairsk /= szt /= (_ : 1 + k = k + 1) 1:/# /= fromintD.
rewrite expD.
+ by apply (hasE_le _ _ (fun _ => k%r)); [apply hasEC | move=> x /=; apply cntk_bound; smt()].
+ by apply (hasE_le _ _ (fun _ => (k * k)%r)); [apply hasEC | move=> x /=; apply pairsk_bound; smt()].
rewrite (exp_dprod _ _ _ k%r); first by move=> x /=; apply cntk_bound; smt().
rewrite (exp_dprod _ _ _ (k * k)%r); first by move=> x /=; apply pairsk_bound; smt().
rewrite /= (eq_exp _ _ (fun a => k%r * mu1 md a)).
+ by move=> a _ /=; rewrite E_count.
rewrite expZ -cp_E expC md_ll ih /=.
by rewrite !fromintM !fromintD; field.
qed.

(* -------------------------------------------------------------------- *)
(* B3: the baseline bound  k E[prior_k] <= 1 + C(k,2) cp                *)

lemma priork_01 (u : msg list) : 0%r <= priork u <= 1%r.
proof.
split.
+ apply (ler_trans _ _ _ (ge0_mu (dmap (drange 0 (size u)) (nth witness u))
                     (pred1 (nth witness u (jst u witness))))).
  apply (flub_upper_bound (fun y => mu (dmap (drange 0 (size u)) (nth witness u))
                                      (pred1 (nth witness u (jst u y)))) witness).
  by exists 1%r => y /=; apply le1_mu.
by move=> _; apply flub_le_ub => y /=; apply le1_mu.
qed.

lemma base_bound (k : int) : 1 <= k =>
  k%r * E (dlist md k) priork <= 1%r + (k * (k - 1))%r / 2%r * cp.
proof.
move=> ge1k.
have : E (dlist md k) priork
       <= E (dlist md k) (fun u => (1%r + (pairsk k u)%r) / k%r).
+ apply in_ler_exp.
  + by apply hasE01 => u; apply priork_01.
  + apply (hasE_le _ _ (fun _ => (1 + k * k)%r)); first by apply hasEC.
    move=> u /=; have := pairsk_bound k u _; first smt().
    have := pairs_ge0 u; rewrite /pairsk; case: (size u = k) => /= _; smt().
  move=> u; rewrite supp_dlist 1:/# => -[szu _].
  have := prior_le u _; first smt().
  move=> h; rewrite /pairsk /= szu /=; smt().
move=> h.
have heq : E (dlist md k) (fun u => (1%r + (pairsk k u)%r) / k%r)
       = 1%r / k%r + 1%r / k%r * E (dlist md k) (fun u => (pairsk k u)%r).
+ rewrite (eq_exp _ (fun u => (1%r + (pairsk k u)%r) / k%r)
                   (fun u => 1%r / k%r + 1%r / k%r * (pairsk k u)%r)).
  + by move=> u _ /=; field; smt().
  rewrite expD.
  + by apply hasEC.
  + apply hasEZ; apply (hasE_le _ _ (fun _ => (k * k)%r)); first by apply hasEC.
    by move=> u /=; apply pairsk_bound; smt().
  rewrite expC dlist_ll /=; first by apply md_ll.
  rewrite (eq_exp _ (fun x => (pairsk k x)%r / k%r) (fun x => inv k%r * (pairsk k x)%r)) 1:/#.
  by rewrite expZ; ring.
move: h; rewrite heq E_pairs 1:/# => h.
have : k%r * E (dlist md k) priork
       <= k%r * (1%r / k%r + 1%r / k%r * ((k * (k - 1))%r / 2%r * cp)).
+ by apply ler_wpmul2l; [smt() | exact h].
have -> : k%r * (1%r / k%r + 1%r / k%r * ((k * (k - 1))%r / 2%r * cp))
        = 1%r + (k * (k - 1))%r / 2%r * cp by field; smt().
done.
qed.

(* -------------------------------------------------------------------- *)
(* C: assembly                                                          *)

lemma q01 y : 0%r <= q y <= 1%r.
proof. by rewrite /q; smt(ge0_mu le1_mu). qed.

lemma outcome_partition : Pv + Vl + haltp = 1%r.
proof.
have h : forall m, E (run m) pvf + E (run m) vf + mu (run m) (pred1 Halt) = 1%r.
+ move=> m; rewrite -exp_b2r -expD.
  + by apply hasE01 => o; rewrite /pvf; case: o.
  + by apply hasE01 => o; rewrite /vf; case: o.
  rewrite -expD.
  + by apply (hasE_le _ _ (fun _ => 2%r)); [apply hasEC | move=> o /=; rewrite /pvf /vf; case: o].
  + by apply hasE01 => o /=; rewrite /pred1; case: (o = Halt).
  rewrite (eq_exp _ _ (fun _ => 1%r)).
  + by move=> o _ /=; rewrite /pvf /vf /pred1; case: o.
  by rewrite expC run_ll.
rewrite /Pv /Vl /haltp -expD.
+ by apply hasE01 => m; apply exp01 => o; rewrite /pvf; case: o.
+ by apply hasE01 => m; apply exp01 => o; rewrite /vf; case: o.
rewrite -expD.
+ apply (hasE_le _ _ (fun _ => 2%r)); first by apply hasEC.
  move=> m /=; have := exp01 (run m) pvf _; first by move=> o; rewrite /pvf; case: o.
  have := exp01 (run m) vf _; first by move=> o; rewrite /vf; case: o.
  smt().
+ by apply hasE01 => m; smt(ge0_mu le1_mu).
rewrite (eq_exp _ _ (fun _ => 1%r)) => [m _ /= | ]; first by apply h.
by rewrite expC md_ll.
qed.

lemma lin_E (t : real) : 0%r <= t =>
  E md (fun m => E (run m) (lin t m)) = 2%r * t * RealS - t * (2%r + t) * Bl + Pv.
proof.
move=> ge0t.
have hb : forall m, E (run m) (lin t m)
                  = 2%r * t * E (run m) (realf m) - t * (2%r + t) * E (run m) bf
                    + E (run m) pvf.
+ move=> m; rewrite -!expZ -expB.
  + by apply hasEZ; apply hasE01 => o; rewrite /realf; case: o => //= y; smt().
  + by apply hasEZ; apply hasE01 => o; rewrite /bf; case: o => //= y; apply q01.
  rewrite -expD.
  + apply (hasE_le _ _ (fun _ => 2%r * t + t * (2%r + t))); first by apply hasEC.
    move=> o /=; rewrite /realf /bf; case: o => [| | y] /=; first 2 smt().
    have := q01 y; case: (R m y) => _ /=; smt().
  + by apply hasE01 => o; rewrite /pvf; case: o.
  by apply eq_exp => o _ /=; rewrite /lin /realf /bf /pvf; case: o.
rewrite (eq_exp _ _ (fun m => 2%r * t * E (run m) (realf m) - t * (2%r + t) * E (run m) bf
                               + E (run m) pvf)) => [m _ /= | ]; first by apply hb.
rewrite /RealS /Bl /Pv -!expZ -expB.
+ by apply hasEZ; apply hasE01 => m; apply exp01 => o; rewrite /realf; case: o => //= y; smt().
+ by apply hasEZ; apply hasE01 => m; apply exp01 => o; rewrite /bf; case: o => //= y; apply q01.
rewrite -expD.
+ apply (hasE_le _ _ (fun _ => 2%r * t + t * (2%r + t))); first by apply hasEC.
  move=> m /=.
  have := exp01 (run m) (realf m) _; first by move=> o; rewrite /realf; case: o => //= y; smt().
  have := exp01 (run m) bf _; first by move=> o; rewrite /bf; case: o => //= y; apply q01.
  smt().
+ by apply hasE01 => m; apply exp01 => o; rewrite /pvf; case: o.
done.
qed.

lemma lin_le_mix (t : real) (K : int) (m : msg) (o : outc) : 0%r < t => 0 <= K =>
  lin t m o
  <= bigi predT (fun k => Sim_C5_Core.w t k * vg k m o) 1 (K + 1)
     + (1%r - Sim_C5_Core.rho t) ^ K * (K%r + 1%r / Sim_C5_Core.rho t) * pvf o.
proof.
move=> gt0t ge0K; case: o => [| | y] /=.
+ by rewrite /lin /vg /pvf /= big1_eq.
+ by rewrite /lin /vg /pvf /= big1_eq.
rewrite /lin /vg /pvf /=.
by have := Sim_C5_Core.mix_lower t (q y) (R m y) K gt0t (q01 y) ge0K; rewrite /Sim_C5_Core.mix.
qed.

lemma sum_exp_range ['a] (d : 'a distr) (f : int -> 'a -> real) (m n : int) (c : real) :
  m <= n => (forall J x, m <= J < n => 0%r <= f J x <= c) =>
  bigi predT (fun J => E d (f J)) m n = E d (fun x => bigi predT (fun J => f J x) m n).
proof.
move=> lemn.
have [j [-> ge0j]] : exists j, n = m + j /\ 0 <= j by exists (n - m); smt().
elim: j ge0j => [|j ge0j ih] hf.
+ by rewrite big_geq // (eq_exp _ _ (fun _ => 0%r)) => [x _ /=|]; [rewrite big_geq | rewrite expC].
rewrite addzA big_int_recr 1:/# /= ih; first by move=> J x hJ; apply hf; smt().
have hsum : forall x, 0%r <= bigi predT (fun J => f J x) m (m + j) <= j%r * c.
+ move=> x; split; first by apply sumr_ge0_seq => J /mem_range hJ _ /=; smt().
  move=> _; have := ler_sum_seq predT (fun J => f J x) (fun _ => c) (range m (m + j)) _.
  + by move=> J /mem_range hJ _ /=; smt().
  by rewrite sumri_const 1:/# intmulr /=; smt().
rewrite -expD.
+ apply (hasE_le _ _ (fun _ => j%r * c)); first by apply hasEC.
  by move=> x /=; have := hsum x; smt().
+ by apply (hasE_le _ _ (fun _ => c)); [apply hasEC | move=> x /=; smt()].
by apply eq_exp => x _ /=; rewrite big_int_recr 1:/#.
qed.

lemma vg_bounds (k : int) (m : msg) (o : outc) : 1 <= k => 0%r <= vg k m o <= k%r.
proof.
move=> ge1k; rewrite /vg; case: o => [| | y] /=; first 2 smt().
rewrite /Sim_C5_Core.g; case: (R m y) => _ /=.
+ by apply Sim_C5_Core.S_bounds; [apply q01 | smt()].
have := q01 y; smt(expr_ge0 exprn_ile1).
qed.

lemma w_bounds (t : real) (k : int) : 0%r < t => 1 <= k =>
  0%r <= Sim_C5_Core.w t k <= 1%r.
proof.
move=> gt0t ge1k; have [gt0r lt1r] := Sim_C5_Core.rho_bounds t gt0t.
rewrite /Sim_C5_Core.w; split.
+ by apply mulr_ge0; [smt() | apply expr_ge0; smt()].
move=> _; have : (1%r - Sim_C5_Core.rho t) ^ (k - 1) <= 1%r by apply exprn_ile1; smt().
have : 0%r <= (1%r - Sim_C5_Core.rho t) ^ (k - 1) by apply expr_ge0; smt().
smt().
qed.

lemma wvg_bound (t : real) (k K : int) (m : msg) (o : outc) :
  0%r < t => 1 <= k <= K =>
  0%r <= Sim_C5_Core.w t k * vg k m o <= K%r.
proof.
move=> gt0t [ge1k lekK].
have [w0 w1] := w_bounds t k gt0t ge1k.
have [v0 v1] := vg_bounds k m o ge1k.
split; first by apply mulr_ge0.
move=> _; apply (ler_trans (1%r * k%r)); last by rewrite mul1r le_fromint.
by apply ler_pmul.
qed.

lemma sumwvg_bound (t : real) (K : int) (m : msg) (o : outc) : 0%r < t => 0 <= K =>
  0%r <= bigi predT (fun k => Sim_C5_Core.w t k * vg k m o) 1 (K + 1) <= (K * K)%r.
proof.
move=> gt0t ge0K; split.
+ by apply sumr_ge0_seq => k /mem_range hk _ /=; have := wvg_bound t k K m o gt0t _; smt().
move=> _; apply (ler_trans (bigi predT (fun _ => K%r) 1 (K + 1))).
+ by apply ler_sum_seq => k /mem_range hk _ /=; have := wvg_bound t k K m o gt0t _; smt().
by rewrite sumri_const 1:/# intmulr fromintM /=; smt().
qed.

lemma lin_bound (t : real) (m : msg) (o : outc) : 0%r <= t =>
  `|lin t m o| <= 2%r * t + t * (2%r + t) + 1%r.
proof.
move=> ge0t; rewrite /lin; case: o => [| | y] /=; first 2 smt().
have := q01 y; case: (R m y) => _ /=; smt(mulr_ge0).
qed.

(* -------------------------------------------------------------------- *)
(* the theorem: CNM-AP for the mixed test implies the C5_t inequality   *)

lemma sim_c5_ideal (t : real) (K : int) :
  0%r < t => 1 <= K =>
  2%r * t * RealS
  <= t * (2%r + t) * Bl + Vl
   + bigi predT (fun k => Sim_C5_Core.w t k *
        (bigi predT (fun J => mu (dtest k J) (win J)) 0 k - k%r * E (dlist md k) priork)) 1 (K + 1)
   + bigi predT (fun k => Sim_C5_Core.w t k * (haltp - hsum k)) 1 (K + 1)
   + bigi predT (fun k => k%r * Sim_C5_Core.w t k) 1 (K + 1) * mu1 md ystar
   + (1%r + t) ^ 4 * cp
   + (1%r - Sim_C5_Core.rho t) ^ K * (K%r + 1%r + 1%r / Sim_C5_Core.rho t).
proof.
move=> gt0t ge1K.
have [gt0r lt1r] := Sim_C5_Core.rho_bounds t gt0t.
have [sw [skw sc2w]] := Sim_C5_Core.sum_bounds t K gt0t _; first smt().
pose w := Sim_C5_Core.w t.
pose EVG := fun k => E md (fun m => E (run m) (fun o => vg k m o)).
pose T := fun k => bigi predT (fun J => mu (dtest k J) (win J)) 0 k.
pose EP := fun k => E (dlist md k) priork.
pose X := (1%r - Sim_C5_Core.rho t) ^ K.
pose tau := X * (K%r + 1%r / Sim_C5_Core.rho t).
have ge0X : 0%r <= X by apply expr_ge0; smt().
have le1X : X <= 1%r by apply exprn_ile1; smt().
have ge0tau0 : 0%r <= tau by rewrite /tau; apply mulr_ge0 => //; smt(divr_ge0).
have ge0KK : 0%r <= (K * K)%r by rewrite le_fromint; smt().
have ge0h : 0%r <= haltp by rewrite /haltp; apply exp_ge0 => m _; apply ge0_mu.
have ge0cp : 0%r <= cp by rewrite /cp ge0_mu.
have [ge0Pv le1Pv] : 0%r <= Pv <= 1%r.
+ by apply exp01 => m; apply exp01 => o; rewrite /pvf; case: o.
have ge0V : 0%r <= Vl by apply exp_ge0 => m _; apply exp_ge0 => o _; rewrite /vf; case: o.
(* 1. the weighted per-k inequalities (test_real) *)
pose f := mu1 md ystar.
have h1 : bigi predT (fun k => w k * (EVG k + hsum k - k%r * f)) 1 (K + 1)
          <= bigi predT (fun k => w k * T k) 1 (K + 1).
+ apply ler_sum_seq => k /mem_range hk _ /=.
  by apply ler_wpmul2l; [smt(w_bounds) | apply test_real; smt()].
(* 2. the baseline (base_bound) *)
have hB : bigi predT (fun k => w k * (k%r * EP k)) 1 (K + 1)
          <= bigi predT (fun k => w k) 1 (K + 1)
           + bigi predT (fun k => k%r * (k%r - 1%r) / 2%r * w k) 1 (K + 1) * cp.
+ apply (ler_trans (bigi predT (fun k => w k + k%r * (k%r - 1%r) / 2%r * w k * cp) 1 (K + 1))).
  + apply ler_sum_seq => k /mem_range hk _ /=.
    have hb := base_bound k _; first smt().
    have -> : w k + k%r * (k%r - 1%r) / 2%r * w k * cp
            = w k * (1%r + (k * (k - 1))%r / 2%r * cp) by rewrite fromintM fromintB; ring.
    by apply ler_wpmul2l; [smt(w_bounds) | rewrite /EP /=].
  by rewrite big_split mulr_suml.
have hT : bigi predT (fun k => w k * T k) 1 (K + 1)
        = bigi predT (fun k => w k * (T k - k%r * EP k)) 1 (K + 1)
        + bigi predT (fun k => w k * (k%r * EP k)) 1 (K + 1).
+ by rewrite -big_split; apply eq_big_seq => k _ /=; ring.
(* 3. the left-hand side as an expectation of the mixture *)
have h3 : bigi predT (fun k => w k * (EVG k + hsum k - k%r * f)) 1 (K + 1)
        = E md (fun m => E (run m) (fun o => bigi predT (fun k => w k * vg k m o) 1 (K + 1)))
          + (haltp * bigi predT (fun k => w k) 1 (K + 1)
             - bigi predT (fun k => w k * (haltp - hsum k)) 1 (K + 1))
          - bigi predT (fun k => k%r * w k) 1 (K + 1) * f.
+ have -> : bigi predT (fun k => w k * (EVG k + hsum k - k%r * f)) 1 (K + 1)
          = bigi predT (fun k => E md (fun m => E (run m) (fun o => w k * vg k m o))) 1 (K + 1)
          + (haltp * bigi predT (fun k => w k) 1 (K + 1)
             - bigi predT (fun k => w k * (haltp - hsum k)) 1 (K + 1))
          - bigi predT (fun k => k%r * w k) 1 (K + 1) * f.
  + rewrite (eq_big_seq _ (fun k => (E md (fun m => E (run m) (fun o => w k * vg k m o))
               + (haltp * w k - w k * (haltp - hsum k))) - k%r * w k * f)).
    + move=> k _ /=.
      have -> : E md (fun m => E (run m) (fun o => w k * vg k m o)) = w k * EVG k.
      + by rewrite /EVG /= -expZ; apply eq_exp => m _ /=; rewrite -expZ.
      ring.
    rewrite (mulr_sumr _ _ _ haltp) (mulr_suml _ _ _ f) sumrB -big_split sumrB.
    by apply eq_big_seq => k _ /=.
  congr; congr; rewrite (sum_exp_range _ _ 1 (K + 1) K%r) 1:/#.
  + move=> k m hk /=; apply (exp01k K%r); first smt().
    by move=> o; apply wvg_bound; smt().
  apply eq_exp => m _ /=; rewrite (sum_exp_range _ _ 1 (K + 1) K%r) 1:/# //.
  by move=> k o hk /=; apply wvg_bound; smt().
(* 4. the mixture dominates the integrand (mix_lower) *)
have h4 : E md (fun m => E (run m) (lin t m))
          <= E md (fun m => E (run m) (fun o => bigi predT (fun k => w k * vg k m o) 1 (K + 1)))
           + tau * Pv.
+ clear h1 h3 hB hT.
  pose L := 2%r * t + t * (2%r + t) + 1%r.
  have ge0L : 0%r <= L by smt(mulr_ge0).
  apply (ler_trans (E md (fun m => E (run m)
           (fun o => bigi predT (fun k => w k * vg k m o) 1 (K + 1) + tau * pvf o)))).
  + apply ler_exp.
    + apply (hasE_le _ _ (fun _ => L)); first by apply hasEC.
      move=> m /=; have := exp_norm (run m) (lin t m) _.
      + by apply (hasE_le _ _ (fun _ => L)); [apply hasEC | move=> o /=; have := lin_bound t m o _; smt()].
      have := exp01k L (run m) (fun o => `|lin t m o|) ge0L _.
      + by move=> o /=; have := lin_bound t m o _; smt().
      smt().
    + apply (hasE_le _ _ (fun _ => (K * K)%r + tau)); first by apply hasEC.
      move=> m /=; have := exp01k ((K * K)%r + tau) (run m)
         (fun o => bigi predT (fun k => w k * vg k m o) 1 (K + 1) + tau * pvf o) _ _.
      + smt().
      + move=> o /=; have hs := sumwvg_bound t K m o gt0t _; first smt().
        have ht : 0%r <= tau by rewrite /tau; apply mulr_ge0 => //; smt().
        by move: hs; rewrite /pvf /w; case: o => [| | y] /= hs; smt().
      move=> hh; have ht : 0%r <= tau by rewrite /tau; apply mulr_ge0 => //; smt().
      have : 0%r <= (K * K)%r by rewrite le_fromint; smt().
      move=> hk; case: hh => hh0 hh1; rewrite ger0_norm // ger0_norm //.
      by apply addr_ge0.
    move=> m /=; apply ler_exp.
    + by apply (hasE_le _ _ (fun _ => L)); [apply hasEC | move=> o /=; have := lin_bound t m o _; smt()].
    + apply (hasE_le _ _ (fun _ => (K * K)%r + tau)); first by apply hasEC.
      move=> o /=; have hs := sumwvg_bound t K m o gt0t _; first smt().
      have ht : 0%r <= tau by rewrite /tau; apply mulr_ge0 => //; smt().
      by move: hs; rewrite /pvf /w; case: o => [| | y] /= hs; smt().
    by move=> o /=; apply lin_le_mix; smt().
  have hsb : forall m o, 0%r <= bigi predT (fun k => w k * vg k m o) 1 (K + 1) <= (K * K)%r.
  + by move=> m o; rewrite /w; apply sumwvg_bound; smt().
  have hin : forall m, E (run m) (fun o => bigi predT (fun k => w k * vg k m o) 1 (K + 1) + tau * pvf o)
             = E (run m) (fun o => bigi predT (fun k => w k * vg k m o) 1 (K + 1))
             + tau * E (run m) pvf.
  + move=> m; rewrite expD.
    + by apply (hasE_le _ _ (fun _ => (K * K)%r)); [apply hasEC | move=> o /=; have := hsb m o; smt()].
    + by apply hasEZ; apply hasE01 => o; rewrite /pvf; case: o.
    by rewrite expZ.
  rewrite (eq_exp _ _ (fun m => E (run m) (fun o => bigi predT (fun k => w k * vg k m o) 1 (K + 1))
                                + tau * E (run m) pvf)) => [m _ /= | ]; first by apply hin.
  rewrite expD.
  + apply (hasE_le _ _ (fun _ => (K * K)%r)); first by apply hasEC.
    move=> m /=.
    have hE := exp01k (K * K)%r (run m) (fun o => bigi predT (fun k => w k * vg k m o) 1 (K + 1)) _ _.
    + by rewrite le_fromint; smt().
    + by move=> o; apply hsb.
    by case: hE => e0 e1; rewrite ger0_norm // ger0_norm.
  + by apply hasEZ; apply hasE01 => m; apply exp01 => o; rewrite /pvf; case: o.
  by rewrite expZ /Pv.
have hl := lin_E t _; first smt().
have hp := outcome_partition.
have hsw : bigi predT (fun k => w k) 1 (K + 1) = 1%r - X by apply Sim_C5_Core.sum_w; smt().
(* 5. combine *)
have p2 : bigi predT (fun k => k%r * (k%r - 1%r) / 2%r * w k) 1 (K + 1) * cp
          <= (1%r + t) ^ 4 * cp by apply ler_wpmul2r.
have le1h : haltp <= 1%r by smt().
have p3 : haltp * X <= X.
+ have : haltp * X <= 1%r * X by apply ler_wpmul2r.
  smt().
have ge0tau : 0%r <= tau by rewrite /tau; apply mulr_ge0 => //; smt().
have p4 : tau * Pv <= tau.
+ have : tau * Pv <= tau * 1%r by apply ler_wpmul2l.
  smt().
have etau : X + tau = X * (K%r + 1%r + 1%r / Sim_C5_Core.rho t) by rewrite /tau; ring.
have eh : haltp * bigi predT (fun k => w k) 1 (K + 1) = haltp - haltp * X by rewrite hsw; ring.
move: h1 h3 h4 hl hp hsw hB hT p2 p3 p4 etau eh.
pose S1 := bigi predT (fun k => w k * (EVG k + hsum k - k%r * f)) 1 (K + 1).
pose ST := bigi predT (fun k => w k * T k) 1 (K + 1).
pose SA := bigi predT (fun k => w k * (T k - k%r * EP k)) 1 (K + 1).
pose SB := bigi predT (fun k => w k * (k%r * EP k)) 1 (K + 1).
pose SD := bigi predT (fun k => w k * (haltp - hsum k)) 1 (K + 1).
pose SW := bigi predT (fun k => w k) 1 (K + 1).
pose SKW := bigi predT (fun k => k%r * w k) 1 (K + 1).
pose SC := bigi predT (fun k => k%r * (k%r - 1%r) / 2%r * w k) 1 (K + 1).
pose EM := E md (fun m => E (run m) (fun o => bigi predT (fun k => w k * vg k m o) 1 (K + 1))).
pose EL := E md (fun m => E (run m) (lin t m)).
have -> : bigi predT (fun k => w k * (bigi predT (fun J => mu (dtest k J) (win J)) 0 k
                                     - k%r * E (dlist md k) priork)) 1 (K + 1) = SA by done.
smt().
qed.

end section Hypotheses.
