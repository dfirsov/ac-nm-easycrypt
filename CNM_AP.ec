(* Comparison-based non-malleability against the a-priori baseline.

   The adversary's success in the real game is compared against
     prior(M, R) = sup_w Pr[n <- M : R n w],
   i.e. the best success probability of any strategy that never sees
   anything correlated with the committed message.  *)

pragma Goals:printall.

require import AllCore Distr DBool RealFLub StdRing StdOrder.
import Biased RField RealOrder.

type pubkey, message, commitment, openingkey.

type relation = message -> message -> bool.

(* the commitment scheme is a triple of algorithms (Gen, Commit, Verify) *)
op Gen : pubkey distr.
op Commit (pk : pubkey) (m : message) : (commitment * openingkey) distr.
op Verify : pubkey -> message * (commitment * openingkey) -> bool.

axiom Gen_ll : is_lossless Gen.
axiom Com_ll pk m : is_lossless (Commit pk m).


(* ------------------------------------------------------------------ *)
(* the a-priori baseline                                               *)

op prior (md : message distr) (rel : relation) : real =
  flub (fun w => mu md (fun n => rel n w)).

lemma prior_ub md rel w : mu md (fun n => rel n w) <= prior md rel.
proof.
apply (flub_upper_bound (fun w => mu md (fun n => rel n w))).
by exists 1%r => x /=; apply le1_mu.
qed.

lemma prior_le1 md rel : prior md rel <= 1%r.
proof. by apply flub_le_ub => x /=; apply le1_mu. qed.

lemma prior_ge0 md rel : 0%r <= prior md rel.
proof.
have := prior_ub md rel witness.
have := ge0_mu md (fun n => rel n witness).
smt().
qed.


(* ------------------------------------------------------------------ *)
(* the definition                                                      *)

module type AdvCNM = {
  proc init(pk : pubkey) : message distr * relation
  proc commit(c : commitment) : commitment
  proc decommit(m : message, d : openingkey) : openingkey * message
}.

(* the adversary sees the opening (m, d) before opening its own commitment;
   the only trivial attack is to forward c and open it to m *)
module RealG(A : AdvCNM) = {
  var m, m' : message
  var c, c' : commitment

  proc main() : bool = {
    var pk, md, rel, d, d';
    pk         <$ Gen;
    (md, rel)  <@ A.init(pk);
    m          <$ md;
    (c, d)     <$ Commit pk m;
    c'         <@ A.commit(c);
    (d', m')   <@ A.decommit(m, d);
    return Verify pk (m', (c', d')) /\ rel m m' /\ !(c' = c /\ m' = m);
  }
}.

module Base(A : AdvCNM) = {
  proc main() : bool = {
    var pk, md, rel, b;
    pk         <$ Gen;
    (md, rel)  <@ A.init(pk);
    b          <$ dbiased (prior md rel);
    return b;
  }
}.

(* A scheme is CNM-AP secure iff for every efficient A the advantage
     Pr[RealG(A).main() : res] - Pr[Base(A).main() : res]
   is negligible.  Note that the advantage is one-sided.            *)


(* ------------------------------------------------------------------ *)
(* key lemma: any strategy whose output w is fixed before the message  *)
(* is sampled succeeds with probability at most E[prior]               *)

op qfill (p b : real) = if p < 1%r then (b - p) / (1%r - p) else 0%r.

module Fin1 = {
  proc f(md : message distr, rel : relation, w : message) : bool = {
    var n;
    n <$ md;
    return rel n w;
  }
}.

module Fin3 = {
  proc f(md : message distr, rel : relation, w : message) : bool = {
    var n, y;
    n <$ md;
    y <$ dbiased (qfill (mu md (fun n => rel n w)) (prior md rel));
    return rel n w \/ y;
  }
}.

module Fin2 = {
  proc f(md : message distr, rel : relation, w : message) : bool = {
    var b;
    b <$ dbiased (prior md rel);
    return b;
  }
}.

lemma fin13 : equiv[ Fin1.f ~ Fin3.f : ={arg} ==> res{1} => res{2} ].
proof. by proc; rnd{2}; rnd; skip => /> *; apply dbiased_ll. qed.

lemma qfill_in01 p b : 0%r <= p => p <= b => b <= 1%r =>
  0%r <= qfill p b <= 1%r.
proof.
move=> ge0p lepb leb1; rewrite /qfill; case (p < 1%r) => // ltp1.
have h1 : 0%r < 1%r - p by smt().
split => [|_].
+ by apply divr_ge0; smt().
by rewrite ler_pdivr_mulr //; smt().
qed.

lemma fin3_pr md0 rel0 w0 : is_lossless md0 =>
  phoare[ Fin3.f : arg = (md0, rel0, w0) ==> res ] = (prior md0 rel0).
proof.
move=> md0_ll; proc.
pose p := mu md0 (fun n => rel0 n w0).
pose q := qfill p (prior md0 rel0).
have p_ge0 : 0%r <= p by apply ge0_mu.
have p_le : p <= prior md0 rel0 by apply prior_ub.
have q01 := qfill_in01 p (prior md0 rel0) p_ge0 p_le (prior_le1 md0 rel0).
seq 1 : (rel n w) p 1%r (1%r - p) q (md = md0 /\ rel = rel0 /\ w = w0).
+ by auto.
+ by rnd; skip => /> /#.
+ by rnd; skip => /> *; rewrite dbiased_ll.
+ by rnd; skip => />; rewrite mu_not md0_ll.
+ by rnd; skip => /> ; rewrite dbiasedE /= clamp_id //.
move=> /> ; rewrite /q /qfill /=.
case (p < 1%r) => [ltp1 | /lerNgt gep1].
+ by field; smt().
have := prior_le1 md0 rel0.
rewrite mulr0 addr0 => h.
by apply ler_anti; rewrite p_le /=; apply (ler_trans 1%r).
qed.

lemma fin32 : equiv[ Fin3.f ~ Fin2.f : ={arg} /\ is_lossless md{1} ==> ={res} ].
proof.
bypr (res{1}) (res{2}) => //.
move=> &1 &2 a [eqa ll].
have [#] eq_md eq_rel eq_w : md{1} = md{2} /\ rel{1} = rel{2} /\ w{1} = w{2} by smt().
have -> : Pr[Fin2.f(md{2}, rel{2}, w{2}) @ &2 : res = a]
        = mu1 (dbiased (prior md{1} rel{1})) a.
+ by byphoare (_: arg = (md{2}, rel{2}, w{2}) ==> _) => //; proc; rnd; skip => />;
     rewrite eq_md eq_rel.
have hll : Pr[Fin3.f(md{1}, rel{1}, w{1}) @ &1 : true] = 1%r.
+ byphoare (_: arg = (md{1}, rel{1}, w{1}) ==> true) => //.
  by proc; auto => />; rewrite ll /=; smt(dbiased_ll).
have hp : Pr[Fin3.f(md{1}, rel{1}, w{1}) @ &1 : res] = prior md{1} rel{1}.
+ by byphoare (fin3_pr md{1} rel{1} w{1} ll).
rewrite dbiased1E clamp_id; first smt(prior_ge0 prior_le1).
case a => _.
+ by rewrite -hp; rewrite Pr[mu_eq] => /#.
have -> : Pr[Fin3.f(md{1}, rel{1}, w{1}) @ &1 : res = false]
        = Pr[Fin3.f(md{1}, rel{1}, w{1}) @ &1 : !res] by rewrite Pr[mu_eq] => /#.
by rewrite Pr[mu_not] hll hp.
qed.

lemma fin12 : equiv[ Fin1.f ~ Fin2.f : ={arg} /\ is_lossless md{1} ==> res{1} => res{2} ].
proof.
transitivity Fin3.f (={arg} ==> res{1} => res{2})
                    (={arg} /\ is_lossless md{1} ==> ={res}).
+ by move=> /> &1 &2 *; exists arg{1}.
+ by move=> /> /#.
+ by conseq fin13.
by conseq fin32.
qed.

(* a strategy that outputs a distribution, a relation and a guess *)
module type Oblivious = {
  proc run() : message distr * relation * message
}.

module IdealO(P : Oblivious) = {
  proc main() : bool = {
    var md, rel, w, r;
    (md, rel, w) <@ P.run();
    r            <@ Fin1.f(md, rel, w);
    return r;
  }
}.

module BaseO(P : Oblivious) = {
  proc main() : bool = {
    var md, rel, w, r;
    (md, rel, w) <@ P.run();
    r            <@ Fin2.f(md, rel, w);
    return r;
  }
}.

section Oblivious.

declare module P <: Oblivious.

declare axiom P_md_ll : hoare[ P.run : true ==> is_lossless res.`1 ].

lemma oblivious_le_base &m :
  Pr[ IdealO(P).main() @ &m : res ] <= Pr[ BaseO(P).main() @ &m : res ].
proof.
byequiv => //; proc.
call fin12.
conseq (: ={glob P} ==> ={md, rel, w}) _ (: true ==> is_lossless md) => //.
+ by call P_md_ll.
by call (: true).
qed.

end section Oblivious.
