(* Lindell, "Comparison-Based Key Exchange and the Security of the Numeric
   Comparison Mode in Bluetooth v2.1", CT-RSA 2009, Appendix A,
   Definition A.1 (non-malleability with respect to opening).

   Experiment Expt^real_{A,R,D}:            Experiment Expt^sim_{A',R,D}:
     1. z <- A                                1. z <- A'
     2. m1 <- D(z)                            2. m1 <- D(z)
     3. (com1, dec1) <- P1(m1)                3. (sigma, m2) <- A'
     4. com2 <- A(com1)                       4. output R(sigma, m1, m2)
     5. (sigma, dec2) <- A(com1, dec1)
     6. m2 <- P2(com2, dec2)
     7. output com1 <> com2 /\ R(sigma, m1, m2)

   Definition A.1: for every PPT A, every PPT-samplable D and every
   poly-time R there is a PPT A' with Pr[real] < Pr[sim] + negl.

   We show that no scheme satisfies it, in two independent ways.

   (1) unsat_sigma: the state sigma is output after dec1, so it can carry
       m1.  With R(sigma, m1, m2) = [sigma = m1], an adversary wins the real
       experiment with probability 1 against every correct scheme with two
       distinct commitment values, while every simulator (of any complexity)
       wins with probability at most the largest atom of D.
   (2) unsat_bot: even with sigma independent of the opening, the receiver's
       output m2 may be "bottom" (None), and the relation may depend on it:
       an adversary that opens its own honest commitment only when m1 = a
       wins with probability >= 1 - gamma, every simulator with probability
       <= 1/2 for D uniform on {a, b}.  This is the selective-refusal
       attack of Firsov-Laur-Zhuchko (ICTAC'22).

   The simulator is given more power than Definition A.1 grants (it may be
   any module, and may output bottom), so the results only get stronger.  *)

pragma Goals:printall.

require import AllCore List Distr DBool StdRing StdOrder.
import RField RealOrder.

type message, commitment, decom, aux.

(* the scheme: P1 commits, P2 opens (None = reject) *)
op Commit : message -> (commitment * decom) distr.
op Open   : commitment -> decom -> message option.

(* sigma may be any string; a message suffices for the attack *)
type state = message.

module type AdvL = {
  proc init() : aux
  proc commit(c1 : commitment) : commitment
  proc open(c1 : commitment, d1 : decom) : state * decom
}.

module type SimL = {
  proc init() : aux
  proc out() : state * message option
}.

module ExpReal(A : AdvL) = {
  proc main(D : aux -> message distr,
            R : state -> message -> message option -> bool) : bool = {
    var z, m1, c1, d1, c2, s, d2, m2;
    z        <@ A.init();
    m1       <$ D z;
    (c1, d1) <$ Commit m1;
    c2       <@ A.commit(c1);
    (s, d2)  <@ A.open(c1, d1);
    m2       <- Open c2 d2;
    return c1 <> c2 /\ R s m1 m2;
  }
}.

module ExpSim(S : SimL) = {
  proc main(D : aux -> message distr,
            R : state -> message -> message option -> bool) : bool = {
    var z, m1, s, m2;
    z       <@ S.init();
    m1      <$ D z;
    (s, m2) <@ S.out();
    return R s m1 m2;
  }
}.

(* -------------------------------------------------------------------- *)
(* (1) the state channel                                                *)

op ca, cb : commitment.          (* two distinct commitment values *)

module Asig : AdvL = {
  proc init() : aux = { return witness; }
  proc commit(c1 : commitment) : commitment = {
    return if c1 = ca then cb else ca;
  }
  proc open(c1 : commitment, d1 : decom) : state * decom = {
    return (oget (Open c1 d1), witness);
  }
}.

op Rsig (s : state) (m1 : message) (m2 : message option) : bool = s = m1.

(* the simulator's output does not see m1: sample m1 last *)
module ExpSim2(S : SimL) = {
  proc main(D : aux -> message distr,
            R : state -> message -> message option -> bool) : bool = {
    var z, m1, s, m2;
    z       <@ S.init();
    (s, m2) <@ S.out();
    m1      <$ D z;
    return R s m1 m2;
  }
}.

lemma sim_swap (S <: SimL) &m DD RR :
  Pr[ExpSim(S).main(DD, RR) @ &m : res] = Pr[ExpSim2(S).main(DD, RR) @ &m : res].
proof.
byequiv => //; proc; swap{1} 2 1; sim.
qed.

section Sigma.

declare axiom ca_cb : ca <> cb.
declare axiom Commit_ll m : is_lossless (Commit m).
declare axiom correct m c d : (c, d) \in Commit m => Open c d = Some m.

lemma real_sigma (D : aux -> message distr) &m :
  (forall z, is_lossless (D z)) =>
  Pr[ExpReal(Asig).main(D, Rsig) @ &m : res] = 1%r.
proof.
move=> Dll; byphoare (_ : arg = (D, Rsig) ==> _) => //.
conseq (: arg = (D, Rsig) ==> true) (: arg = (D, Rsig) ==> res) => //.
+ proc; inline *; wp; rnd; rnd; wp; skip => /> m1 _ cd cd_in.
  split; first smt(ca_cb).
  by rewrite /Rsig (correct m1 cd.`1 cd.`2) -?pairS.
proc; inline *; wp; rnd; rnd; wp; skip => />.
rewrite (mu_eq _ _ predT); first by move=> m; rewrite /predT Commit_ll.
by apply Dll.
qed.

(* any simulator, even unbounded *)
lemma sim_sigma (S <: SimL) (DD : aux -> message distr) (dl : real) &m :
  (forall z x, mu1 (DD z) x <= dl) =>
  Pr[ExpSim(S).main(DD, Rsig) @ &m : res] <= dl.
proof.
move=> hD; rewrite (sim_swap S &m DD Rsig).
byphoare (_ : arg = (DD, Rsig) ==> _) => //; proc.
seq 2 : (D = DD /\ R = Rsig) 1%r dl 0%r 0%r => //.
+ rnd; auto => />.
  + move=> &h; rewrite /Rsig (mu_eq _ (fun (x : message) => s{h} = x) (pred1 s{h})) 1:/#.
    by apply hD.
  by have := hD witness witness; smt(ge0_mu).
by hoare; call (: true); call (: true); skip.
qed.

lemma unsat_sigma (S <: SimL) (DD : aux -> message distr) (dl : real) &m :
  (forall z, is_lossless (DD z)) => (forall z x, mu1 (DD z) x <= dl) =>
  1%r - dl <= Pr[ExpReal(Asig).main(DD, Rsig) @ &m : res]
            - Pr[ExpSim(S).main(DD, Rsig) @ &m : res].
proof.
move=> Dll hD; rewrite (real_sigma DD &m Dll).
by have := sim_sigma S DD dl &m hD; smt().
qed.

end section Sigma.

(* -------------------------------------------------------------------- *)
(* (2) the bottom channel: selective refusal, with sigma unused         *)

op a, b, w0 : message.   (* D is uniform on {a, b}; the adversary commits to w0 *)
op dbad : decom.         (* a decommitment that P2 rejects *)
op gam : real.           (* unpredictability of commitments *)

op Dab (z : aux) : message distr = duniform [a; b].

(* the relation ignores sigma; it holds on bottom exactly when m1 = a *)
op Rbot (s : state) (m1 : message) (m2 : message option) : bool =
  if m1 = a then m2 = None else m2 = Some w0.

module Abot : AdvL = {
  var c2 : commitment
  var d2 : decom

  proc init() : aux = { return witness; }
  proc commit(c1 : commitment) : commitment = {
    (c2, d2) <$ Commit w0;
    return c2;
  }
  proc open(c1 : commitment, d1 : decom) : state * decom = {
    return (witness, if oget (Open c1 d1) = a then dbad else d2);
  }
}.

section Bottom.

declare axiom a_b : a <> b.
declare axiom Commit_ll' m : is_lossless (Commit m).
declare axiom correct' m c d : (c, d) \in Commit m => Open c d = Some m.
declare axiom reject c : Open c dbad = None.
declare axiom unpred m c : mu (Commit m) (fun (x : commitment * decom) => x.`1 = c) <= gam.

lemma real_bot &m :
  1%r - gam <= Pr[ExpReal(Abot).main(Dab, Rbot) @ &m : res].
proof.
byphoare (_ : arg = (Dab, Rbot) ==> _) => //; proc; inline *.
seq 4 : (D = Dab /\ R = Rbot /\ (m1 = a \/ m1 = b) /\ Open c1 d1 = Some m1)
        1%r (1%r - gam) 0%r 0%r => //.
+ conseq (: _ ==> true)
         (: (D, R) = (Dab, Rbot) ==> D = Dab /\ R = Rbot /\ (m1 = a \/ m1 = b)
                                      /\ Open c1 d1 = Some m1) => //.
  + wp; rnd; rnd; wp; skip => /> m1 hm1 cd hcd.
    split; first by move: hm1; rewrite /Dab supp_duniform.
    by apply (correct' m1 cd.`1 cd.`2); rewrite -pairS.
  wp; rnd; rnd; wp; skip => />.
  rewrite (mu_eq _ _ predT); first by move=> m; rewrite /predT Commit_ll'.
  by rewrite /Dab duniform_ll.
+ wp; rnd (fun (cd : commitment * decom) => cd.`1 <> c1 /\ Open cd.`1 cd.`2 = Some w0).
  skip => /> &h hm1 ho; split.
  + rewrite (mu_eq_support _ _ (fun (cd : commitment * decom) => !(cd.`1 = c1{h}))).
    + move=> cd hcd /=; rewrite (correct' w0 cd.`1 cd.`2) -?pairS //.
    rewrite (mu_eq _ _ (predC (fun (cd : commitment * decom) => cd.`1 = c1{h}))) 1:/#.
    by rewrite mu_not Commit_ll'; have := unpred w0 c1{h}; smt().
  move=> _ v _ hne hv; rewrite ho /=.
  split; first by rewrite eq_sym.
  by split => [-> /= | hna]; [apply reject | rewrite hna].
qed.

(* any simulator, even unbounded: its output is independent of m1 *)
lemma sim_bot (S <: SimL) &m :
  Pr[ExpSim(S).main(Dab, Rbot) @ &m : res] <= 1%r / 2%r.
proof.
rewrite (sim_swap S &m Dab Rbot).
byphoare (_ : arg = (Dab, Rbot) ==> _) => //; proc.
seq 2 : (D = Dab /\ R = Rbot) 1%r (1%r / 2%r) 0%r 0%r => //.
+ rnd; auto => />.
  + move=> &h; rewrite /Dab duniformE /= a_b /= /Rbot /= (eq_sym b a) a_b /=.
    by case: (m2{h}) => [|x] /=; smt().
  smt().
by hoare; call (: true); call (: true); skip.
qed.

lemma unsat_bot (S <: SimL) &m :
  1%r / 2%r - gam <= Pr[ExpReal(Abot).main(Dab, Rbot) @ &m : res]
                   - Pr[ExpSim(S).main(Dab, Rbot) @ &m : res].
proof. by have := real_bot &m; have := sim_bot S &m; smt(). qed.

end section Bottom.

(* -------------------------------------------------------------------- *)
(* (1') the state channel with valid openings: the relation is false on *)
(*      bottom, as in the valid relations of Di Crescenzo-Katz-         *)
(*      Ostrovsky-Smith, so (1) does not depend on bottom at all        *)

op w1 : message.          (* the adversary commits honestly to w1 *)
op gam1 : real.

op Rsig1 (s : state) (m1 : message) (m2 : message option) : bool =
  s = m1 /\ m2 <> None.

lemma Rsig1_bot s m1 : !Rsig1 s m1 None.
proof. by rewrite /Rsig1. qed.

module Asig1 : AdvL = {
  var d2 : decom

  proc init() : aux = { return witness; }
  proc commit(c1 : commitment) : commitment = {
    var c2;
    (c2, d2) <$ Commit w1;
    return c2;
  }
  proc open(c1 : commitment, d1 : decom) : state * decom = {
    return (oget (Open c1 d1), d2);
  }
}.

section Sigma1.

declare axiom Commit_ll1 m : is_lossless (Commit m).
declare axiom correct1 m c d : (c, d) \in Commit m => Open c d = Some m.
declare axiom unpred1 m c : mu (Commit m) (fun (x : commitment * decom) => x.`1 = c) <= gam1.

lemma real_sigma1 (DD : aux -> message distr) &m :
  (forall z, is_lossless (DD z)) =>
  1%r - gam1 <= Pr[ExpReal(Asig1).main(DD, Rsig1) @ &m : res].
proof.
move=> Dll; byphoare (_ : arg = (DD, Rsig1) ==> _) => //; proc; inline *.
seq 4 : (D = DD /\ R = Rsig1 /\ Open c1 d1 = Some m1) 1%r (1%r - gam1) 0%r 0%r => //.
+ conseq (: _ ==> true) (: (D, R) = (DD, Rsig1) ==> D = DD /\ R = Rsig1 /\ Open c1 d1 = Some m1) => //.
  + wp; rnd; rnd; wp; skip => /> m1 _ cd hcd.
    by apply (correct1 m1 cd.`1 cd.`2); rewrite -pairS.
  wp; rnd; rnd; wp; skip => />.
  rewrite (mu_eq _ _ predT); first by move=> m; rewrite /predT Commit_ll1.
  by rewrite Dll.
+ wp; rnd (fun (cd : commitment * decom) => cd.`1 <> c1 /\ Open cd.`1 cd.`2 = Some w1).
  skip => /> &h ho; split.
  + rewrite (mu_eq_support _ _ (fun (cd : commitment * decom) => !(cd.`1 = c1{h}))).
    + move=> cd hcd /=; rewrite (correct1 w1 cd.`1 cd.`2) -?pairS //.
    rewrite (mu_eq _ _ (predC (fun (cd : commitment * decom) => cd.`1 = c1{h}))) 1:/#.
    by rewrite mu_not Commit_ll1; have := unpred1 w1 c1{h}; smt().
  move=> _ v _ hne hv; rewrite ho /=.
  by split; [rewrite eq_sym | rewrite /Rsig1 hv].
qed.

lemma sim_sigma1 (S <: SimL) (DD : aux -> message distr) (dl : real) &m :
  (forall z x, mu1 (DD z) x <= dl) =>
  Pr[ExpSim(S).main(DD, Rsig1) @ &m : res] <= dl.
proof.
move=> hD; rewrite (sim_swap S &m DD Rsig1).
byphoare (_ : arg = (DD, Rsig1) ==> _) => //; proc.
seq 2 : (D = DD /\ R = Rsig1) 1%r dl 0%r 0%r => //.
+ rnd; auto => />.
  + move=> &h; apply (ler_trans (mu (DD z{h}) (pred1 s{h}))).
    + by apply mu_sub => x; rewrite /Rsig1 /pred1 /#.
    by apply hD.
  by have := hD witness witness; smt(ge0_mu).
by hoare; call (: true); call (: true); skip.
qed.

lemma unsat_sigma1 (S <: SimL) (DD : aux -> message distr) (dl : real) &m :
  (forall z, is_lossless (DD z)) => (forall z x, mu1 (DD z) x <= dl) =>
  1%r - gam1 - dl <= Pr[ExpReal(Asig1).main(DD, Rsig1) @ &m : res]
                   - Pr[ExpSim(S).main(DD, Rsig1) @ &m : res].
proof.
move=> Dll hD; have := real_sigma1 DD &m Dll; have := sim_sigma1 S DD dl &m hD.
smt().
qed.

end section Sigma1.
