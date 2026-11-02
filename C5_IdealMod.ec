(* C5 is sound at the module level for "ideal-commitment" adversaries.

   P.ex1 is an arbitrary (stateful) commit phase; its result x fixes the
   message distribution dm x, the relation relx x, the committed value wx x,
   and whether the adversary halts (haltx x).  The honest message m <$ dm x is
   chosen afterwards (so the commit phase is independent of it), P.ex2(x, m)
   is the opening phase (b = "opened validly"), and n <$ dm x is independent.

     Real = Pr[ !halt /\ b /\ R m w ],  B = Pr[ !halt /\ b /\ R n w ],
     V    = Pr[ !halt /\ !b ]
     c5_mod :  Real <= B + sqrt (B * V)

   The proof reflects both phases (C5_Avg.averaging), applies the per-state
   inequality pw_c5 and optimises the AM-GM parameter (amgm_inf).          *)

pragma Goals:printall.

require import AllCore Distr DBool RealSeries StdRing StdOrder RealExp.
require import C5_Real.
require C5_Avg.
import RField RealOrder.

type xt, msg, wt.   (* wt: the opened value; msg for a single commitment,
                       a list of messages for a vector of commitments *)

op dm : xt -> msg distr.

clone import C5_Avg as Av with type xt <- xt, type msg <- msg, op dm <- dm.

op wx    : xt -> wt.
op haltx : xt -> bool.
op relx  : xt -> msg -> wt -> bool.

axiom dm_ll x : is_lossless (dm x).

op ev0 (r : xt * msg * bool * msg) = !haltx r.`1 /\ r.`3 /\ relx r.`1 r.`2 (wx r.`1).
op ev1 (r : xt * msg * bool * msg) = !haltx r.`1 /\ r.`3 /\ relx r.`1 r.`4 (wx r.`1).
op ev2 (r : xt * msg * bool * msg) = !haltx r.`1 /\ !r.`3.
op evb (r : xt * msg * bool * msg) = !haltx r.`1 /\ r.`3.

lemma mu_const ['a] (d : 'a distr) (c : bool) : is_lossless d => mu d (fun _ => c) = b2r c.
proof. by move=> ll; case: c => _ /=; [apply ll | apply mu0]. qed.

lemma exp0 ['a] (d : 'a distr) (g : 'a -> real) : (forall x, x \in d => g x = 0%r) => E d g = 0%r.
proof. by move=> h; rewrite (eq_exp _ _ (fun _ => 0%r)) // expC. qed.

section.

declare module P <: Two.

declare axiom ex2_ll : islossless P.ex2.

lemma c5_mod &m :
  Pr[ G0(P).main() @ &m : ev0 res ]
  <= Pr[ G0(P).main() @ &m : ev1 res ]
   + sqrt (Pr[ G0(P).main() @ &m : ev1 res ] * Pr[ G0(P).main() @ &m : ev2 res ]).
proof.
elim (averaging P) => D1 D2 [hD1 [hD2 hav]].
pose d1 := D1 (glob P){m}.
pose a  := fun (xg : xt * glob P) (m : msg) => mu (D2 xg.`2 (xg.`1, m)) (fun b => b).
pose al := fun (xg : xt * glob P) => E (dm xg.`1) (a xg).
pose q  := fun (xg : xt * glob P) => mu (dm xg.`1) (fun m => relx xg.`1 m (wx xg.`1)).
pose f  := fun (xg : xt * glob P) =>
             E (dm xg.`1) (fun m => a xg m * b2r (relx xg.`1 m (wx xg.`1))).
pose nh := fun (xg : xt * glob P) => b2r (!haltx xg.`1).
have a01 : forall (xg : xt * glob P) m, 0%r <= a xg m <= 1%r by smt(ge0_mu le1_mu).
have hEa : forall (xg : xt * glob P), hasE (dm xg.`1) (a xg) by move=> xg; apply hasE01 => m; apply a01.
(* Real *)
have r0 : Pr[ G0(P).main() @ &m : ev0 res ] = E d1 (fun xg => nh xg * f xg).
+ rewrite (hav &m ev0); apply eq_exp => xg _ /=.
  rewrite /nh /f -expZ; apply eq_exp => m _ /=.
  rewrite (eq_exp _ _ (fun b => b2r (!haltx xg.`1 /\ b /\ relx xg.`1 m (wx xg.`1)))).
  + by move=> b _ /=; rewrite /ev0 /= mu_const 1:dm_ll.
  rewrite E_b2r /a /=.
  case: (haltx xg.`1) => /= _; first by apply mu0_false.
  by case: (relx xg.`1 m (wx xg.`1)) => /= _; [done | apply mu0_false].
(* B *)
have r1 : Pr[ G0(P).main() @ &m : ev1 res ] = E d1 (fun xg => nh xg * (al xg * q xg)).
+ rewrite (hav &m ev1); apply eq_exp => xg _ /=.
  rewrite /nh /al /q; case: (haltx xg.`1) => hx /=.
  + apply exp0 => m _ /=; apply exp0 => b _ /=.
    by apply mu0_false => n _; rewrite /ev1 /= hx.
  rewrite mulrC -expZ; apply eq_exp => m _ /=.
  rewrite (eq_exp _ _ (fun b => mu (dm xg.`1) (fun n => relx xg.`1 n (wx xg.`1)) * b2r b)).
  + move=> b _ /=; rewrite /ev1 /= hx /=.
    by case: b => /= _; [done | apply mu0_false].
  by rewrite expZ E_b2r /a mulrC.
(* Pr[ !halt /\ b ] *)
have rb : Pr[ G0(P).main() @ &m : evb res ] = E d1 (fun xg => nh xg * al xg).
+ rewrite (hav &m evb); apply eq_exp => xg _ /=.
  rewrite /nh /al; case: (haltx xg.`1) => hx /=.
  + apply exp0 => m _ /=; apply exp0 => b _ /=.
    by apply mu0_false => n _; rewrite /evb /= hx.
  apply eq_exp => m _ /=.
  rewrite (eq_exp _ _ (fun b => b2r b)).
  + by move=> b _ /=; rewrite /evb /= hx /= mu_const 1:dm_ll.
  by rewrite E_b2r /a.
(* Pr[ !halt ] only depends on the first phase *)
have rh : Pr[ G0(P).main() @ &m : !haltx res.`1 ] = E d1 nh.
+ have -> : Pr[ G0(P).main() @ &m : !haltx res.`1 ] = Pr[ W1(P).p() @ &m : !haltx res ].
  + byequiv => //; proc *; inline G0(P).main.
    wp; rnd{1}; call{1} (: true ==> true); first by proc; call ex2_ll.
    by rnd{1}; inline W1(P).p; wp; call (: true); auto => />; smt(dm_ll).
  have := hD1 &m (fun (xg : xt * glob P) => !haltx xg.`1); rewrite /= => <-.
  by rewrite /d1 /nh E_b2r.
(* V *)
have r2 : Pr[ G0(P).main() @ &m : ev2 res ] = E d1 (fun xg => nh xg * (1%r - al xg)).
+ have hs : Pr[ G0(P).main() @ &m : !haltx res.`1 ]
          = Pr[ G0(P).main() @ &m : evb res ] + Pr[ G0(P).main() @ &m : ev2 res ].
  + by rewrite Pr[mu_split (res.`3)]; congr; rewrite Pr[mu_eq] /#.
  have hnh : hasE d1 nh by apply hasE01 => xg; rewrite /nh; case: (haltx xg.`1).
  have hna : hasE d1 (fun xg => nh xg * al xg).
  + apply hasE01 => xg; rewrite /nh /al.
    have h1 := ler_exp (dm xg.`1) (a xg) (fun _ => 1%r) (hEa xg) (hasEC _ _) _; first smt().
    have h0 := exp_ge0 (dm xg.`1) (a xg) _; first smt().
    move: h1; rewrite expC dm_ll /=; case: (haltx xg.`1) => /= /#.
  have : E d1 (fun xg => nh xg * (1%r - al xg)) = E d1 nh - E d1 (fun xg => nh xg * al xg).
  + have e1 : E d1 (fun xg => nh xg - nh xg * al xg) = E d1 nh - E d1 (fun xg => nh xg * al xg).
    + by apply Distr.expB; [exact hnh | exact hna].
    rewrite -e1; apply eq_exp => xg _ /=; ring.
  smt().
(* per-state facts *)
have al01 : forall (xg : xt * glob P), 0%r <= al xg <= 1%r.
+ move=> xg; rewrite /al.
  have h1 := ler_exp (dm xg.`1) (a xg) (fun _ => 1%r) (hEa xg) (hasEC _ _) _; first smt().
  have h0 := exp_ge0 (dm xg.`1) (a xg) _; first smt().
  by move: h1; rewrite expC dm_ll /= => ->.
have q01 : forall (xg : xt * glob P), 0%r <= q xg <= 1%r by smt(ge0_mu le1_mu).
have hEf : forall (xg : xt * glob P),
    hasE (dm xg.`1) (fun m => a xg m * b2r (relx xg.`1 m (wx xg.`1))).
+ by move=> xg; apply hasE01 => m /=; smt().
have fp : forall (xg : xt * glob P), 0%r <= f xg /\ f xg <= al xg /\ f xg <= q xg.
+ move=> xg; rewrite /f /al /q; split; first by apply exp_ge0 => m _ /=; smt().
  split.
  + by apply ler_exp; [exact (hEf xg) | exact (hEa xg) | move=> m /=; smt()].
  rewrite -E_b2r; apply ler_exp; first exact (hEf xg).
  + by apply hasE01 => m /=; smt().
  by move=> m /=; smt().
have hB0 : 0%r <= Pr[ G0(P).main() @ &m : ev1 res ] by rewrite Pr[mu_ge0].
have hV0 : 0%r <= Pr[ G0(P).main() @ &m : ev2 res ] by rewrite Pr[mu_ge0].
(* the t-family, then optimise t *)
have fam : forall t, 0%r < t =>
    Pr[ G0(P).main() @ &m : ev0 res ] - Pr[ G0(P).main() @ &m : ev1 res ]
    <= (t * Pr[ G0(P).main() @ &m : ev1 res ] + Pr[ G0(P).main() @ &m : ev2 res ] / t) / 2%r.
+ move=> t gt0t; rewrite r0 r1 r2.
  have hX : hasE d1 (fun xg => nh xg * (al xg * q xg)).
  + by apply hasE01 => xg; rewrite /nh; case: (haltx xg.`1) => /=; smt(mulr_ge0 mulr_ile1).
  have hY : hasE d1 (fun xg => nh xg * (1%r - al xg)).
  + by apply hasE01 => xg; rewrite /nh; case: (haltx xg.`1) => /=; smt().
  have hle : E d1 (fun xg => nh xg * f xg)
          <= E d1 (fun xg => (1%r + t / 2%r) * (nh xg * (al xg * q xg))
                           + (1%r / (2%r * t)) * (nh xg * (1%r - al xg))).
  + apply ler_exp.
    + by apply hasE01 => xg; rewrite /nh; case: (haltx xg.`1) => /=; smt().
    + apply (hasE_le _ _ (fun _ => (1%r + t / 2%r) + 1%r / (2%r * t))); first by apply hasEC.
      move=> xg /=; have h1 := al01 xg; have h2 := q01 xg.
      have ge0c : 0%r <= 1%r / (2%r * t) by smt(divr_ge0).
      have hp : 0%r <= al xg * q xg <= 1%r by smt(mulr_ge0 mulr_ile1).
      rewrite /nh; case: (haltx xg.`1) => /=; first smt().
      have : 1%r / (2%r * t) * (1%r - al xg) <= 1%r / (2%r * t) by smt(ler_wpmul2l).
      have : (1%r + t / 2%r) * (al xg * q xg) <= 1%r + t / 2%r by smt(ler_wpmul2l).
      smt(mulr_ge0).
    move=> xg /=; rewrite /nh; case: (haltx xg.`1) => /=; first smt().
    have [h0 [hfa hfq]] := fp xg.
    have := pw_c5 (f xg) (al xg) (q xg) t gt0t h0 hfa hfq _ _ _ _; 1..4: smt().
    have -> : (1%r + t / 2%r) * (al xg * q xg) + 1%r / (2%r * t) * (1%r - al xg)
            = al xg * q xg + (t * (al xg * q xg) + (1%r - al xg) / t) / 2%r by field; smt().
    done.
  move: hle; rewrite Distr.expD; [by apply hasEZ | by apply hasEZ |].
  rewrite !expZ => hle.
  have -> : (t * E d1 (fun xg => nh xg * (al xg * q xg)) + E d1 (fun xg => nh xg * (1%r - al xg)) / t) / 2%r
          = (1%r + t / 2%r) * E d1 (fun xg => nh xg * (al xg * q xg))
          + 1%r / (2%r * t) * E d1 (fun xg => nh xg * (1%r - al xg))
          - E d1 (fun xg => nh xg * (al xg * q xg)) by field; smt().
  smt().
have := amgm_inf (Pr[ G0(P).main() @ &m : ev0 res ] - Pr[ G0(P).main() @ &m : ev1 res ])
                 Pr[ G0(P).main() @ &m : ev1 res ] Pr[ G0(P).main() @ &m : ev2 res ] hB0 hV0 fam.
smt().
qed.

end section.
