(* The converse direction: CNM-AP implies simulation-based NM, provided
   simulators may be computationally unbounded.  A single universal
   simulator suffices: it ignores the adversary and outputs an
   eps-maximiser of  w |-> Pr[n <- M : R n w].

   Together with sim_implies_ap (CNM_AP_Sim.ec), which holds for any
   simulator, this gives:

     CNM-AP  <=>  simulation-based NM with unbounded simulators.       *)

pragma Goals:printall.

require import AllCore Distr DBool RealFLub RealLub StdRing StdOrder.
require import CNM_AP CNM_AP_Sim.
import Biased RField RealOrder.

op best (md : message distr) (rel : relation) (eps : real) : message =
  choiceb (fun w => prior md rel - eps < mu md (fun n => rel n w)) witness.

lemma best_spec md rel eps : 0%r < eps =>
  prior md rel - eps < mu md (fun n => rel n (best md rel eps)).
proof.
move=> gt0_eps.
have ex : exists w, prior md rel - eps < mu md (fun n => rel n w).
+ have hl : has_lub (fun r => exists a, (fun w => mu md (fun n => rel n w)) a = r).
  + by apply has_fub_lub; exists 1%r => x /=; apply le1_mu.
  have [e [[a <-] h]] := lub_adherent _ hl eps gt0_eps.
  by exists a; rewrite /prior /flub.
have := choicebP (fun w => prior md rel - eps < mu md (fun n => rel n w)) witness ex.
by rewrite /best.
qed.

(* the universal (inefficient) simulator *)
module SBest : Sim = {
  var eps : real

  proc out(pk : pubkey, md : message distr, rel : relation) : message = {
    return best md rel eps;
  }
}.

(* Fin3 with its internal coins exposed *)
module Fin4 = {
  var hit, y : bool

  proc f(md : message distr, rel : relation, w : message) : bool = {
    var n;
    n   <$ md;
    hit <- rel n w;
    y   <$ dbiased (qfill (mu md (fun n => rel n w)) (prior md rel));
    return hit \/ y;
  }
}.

lemma fin43 : equiv[ Fin4.f ~ Fin3.f : ={arg} ==> ={res} ].
proof. by proc; auto. qed.

lemma fin42 : equiv[ Fin4.f ~ Fin2.f : ={arg} /\ is_lossless md{1} ==> ={res} ].
proof.
transitivity Fin3.f (={arg} ==> ={res}) (={arg} /\ is_lossless md{1} ==> ={res}).
+ by move=> /> &1 &2 *; exists arg{1}.
+ by move=> /> /#.
+ by conseq fin43.
by conseq fin32.
qed.

(* the extra coin y only fires with probability prior - p *)
lemma fin4_bad md0 rel0 w0 : is_lossless md0 =>
  phoare[ Fin4.f : arg = (md0, rel0, w0) ==> !Fin4.hit /\ Fin4.y ]
  <= (prior md0 rel0 - mu md0 (fun n => rel0 n w0)).
proof.
move=> md0_ll; proc.
pose p := mu md0 (fun n => rel0 n w0).
pose q := qfill p (prior md0 rel0).
have p_ge0 : 0%r <= p by apply ge0_mu.
have p_le : p <= prior md0 rel0 by apply prior_ub.
have q01 := qfill_in01 p (prior md0 rel0) p_ge0 p_le (prior_le1 md0 rel0).
seq 2 : (!Fin4.hit) (1%r - p) q p 0%r (md = md0 /\ rel = rel0 /\ w = w0).
+ by auto.
+ wp; rnd.
  + by auto => />; rewrite mu_not md0_ll.
  by move=> _; have := le1_mu md0 (fun n => rel0 n w0); rewrite /p; smt().
+ rnd.
  + by auto => />; rewrite dbiasedE /= clamp_id.
  by move=> _; smt().
+ by hoare; rnd; skip => /> /#.
move=> />; rewrite /q /qfill.
case (p < 1%r) => [ltp1 | /lerNgt gep1].
+ have -> : (1%r - p) * ((prior md0 rel0 - p) / (1%r - p)) = prior md0 rel0 - p.
  + by field; smt().
  by rewrite /p.
rewrite mulr0 -/p.
by apply subr_ge0.
qed.

lemma fin4_bad_best e0 : 0%r < e0 =>
  phoare[ Fin4.f : is_lossless md /\ w = best md rel e0 ==> !Fin4.hit /\ Fin4.y ] <= e0.
proof.
move=> gt0_e0; bypr => &m0; split; first smt().
move=> [ll hw].
have h : Pr[ Fin4.f(md{m0}, rel{m0}, w{m0}) @ &m0 : !Fin4.hit /\ Fin4.y ]
      <= prior md{m0} rel{m0} - mu md{m0} (fun n => rel{m0} n w{m0}).
+ by byphoare (fin4_bad md{m0} rel{m0} w{m0} ll).
have := best_spec md{m0} rel{m0} e0 gt0_e0.
by rewrite -hw; smt().
qed.

module PB(A : AdvCNM) : Oblivious = {
  proc run() : message distr * relation * message = {
    var pk, md, rel, w;
    pk         <$ Gen;
    (md, rel)  <@ A.init(pk);
    w          <@ SBest.out(pk, md, rel);
    return (md, rel, w);
  }
}.

module G4(A : AdvCNM) = {
  proc main() : bool = {
    var md, rel, w, r;
    (md, rel, w) <@ PB(A).run();
    r            <@ Fin4.f(md, rel, w);
    return r;
  }
}.

section.

declare module A <: AdvCNM {-SBest, -Fin4}.

declare axiom A_md_ll : hoare[ A.init : true ==> is_lossless res.`1 ].

local lemma base_g4 &m :
  Pr[ Base(A).main() @ &m : res ] = Pr[ G4(A).main() @ &m : res ].
proof.
have -> : Pr[ Base(A).main() @ &m : res ] = Pr[ BaseO(PB(A)).main() @ &m : res ].
+ by byequiv => //; proc; inline *; wp; rnd; wp; call (: true); auto.
byequiv => //; proc.
call (: ={arg} /\ is_lossless md{1} ==> ={res}).
+ by symmetry; conseq fin42 => /> /#.
conseq (: ={glob A, glob SBest} ==> ={md, rel, w}) _ (: true ==> is_lossless md) => //.
+ by inline *; wp; call A_md_ll; auto.
by inline *; wp; call (: true); auto.
qed.

local lemma g4_hit &m :
  Pr[ G4(A).main() @ &m : Fin4.hit ] = Pr[ Ideal(A, SBest).main() @ &m : res ].
proof.
byequiv => //; proc; inline *.
wp; rnd{1}; wp; rnd; wp; call (: true); auto => /> *.
by apply dbiased_ll.
qed.

local lemma g4_split &m :
  Pr[ G4(A).main() @ &m : res ]
  <= Pr[ G4(A).main() @ &m : Fin4.hit ] + Pr[ G4(A).main() @ &m : !Fin4.hit /\ Fin4.y ].
proof.
have h0 : Pr[ G4(A).main() @ &m : res /\ !Fin4.hit /\ !Fin4.y ] = 0%r.
+ byphoare => //; hoare; proc; inline *; auto; call (: true); auto => /> /#.
rewrite Pr[mu_split Fin4.hit].
have -> : Pr[ G4(A).main() @ &m : res /\ !Fin4.hit ]
        = Pr[ G4(A).main() @ &m : (res /\ !Fin4.hit) /\ Fin4.y ]
        + Pr[ G4(A).main() @ &m : (res /\ !Fin4.hit) /\ !Fin4.y ]
  by rewrite Pr[mu_split Fin4.y].
have -> : Pr[ G4(A).main() @ &m : (res /\ !Fin4.hit) /\ !Fin4.y ] = 0%r.
+ by rewrite -h0; rewrite Pr[mu_eq] => /#.
have h1 : Pr[ G4(A).main() @ &m : res /\ Fin4.hit ] <= Pr[ G4(A).main() @ &m : Fin4.hit ].
+ by rewrite Pr[mu_sub] => /#.
have h2 : Pr[ G4(A).main() @ &m : (res /\ !Fin4.hit) /\ Fin4.y ]
       <= Pr[ G4(A).main() @ &m : !Fin4.hit /\ Fin4.y ].
+ by rewrite Pr[mu_sub] => /#.
smt().
qed.

local lemma g4_bad &m : 0%r < SBest.eps{m} =>
  Pr[ G4(A).main() @ &m : !Fin4.hit /\ Fin4.y ] <= SBest.eps{m}.
proof.
move=> gt0_eps.
byphoare (_: SBest.eps = SBest.eps{m} ==> _) => //; proc.
seq 1 : (w = best md rel SBest.eps /\ is_lossless md /\ SBest.eps = SBest.eps{m})
        1%r SBest.eps{m} 0%r 0%r => //.
+ by call (fin4_bad_best SBest.eps{m} gt0_eps); skip => /> /#.
by hoare; inline *; wp; call A_md_ll; auto => /> /#.
qed.

(* CNM-AP => sim-based NM with the universal unbounded simulator SBest *)
lemma base_le_ideal &m : 0%r < SBest.eps{m} =>
  Pr[ Base(A).main() @ &m : res ]
  <= Pr[ Ideal(A, SBest).main() @ &m : res ] + SBest.eps{m}.
proof.
move=> gt0_eps.
by rewrite base_g4 -g4_hit; have := g4_split &m; have := g4_bad &m gt0_eps; smt().
qed.

lemma ap_implies_sim &m (err : real) : 0%r < SBest.eps{m} =>
  Pr[ RealG(A).main() @ &m : res ] - Pr[ Base(A).main() @ &m : res ] <= err =>
  Pr[ RealG(A).main() @ &m : res ]
  <= Pr[ Ideal(A, SBest).main() @ &m : res ] + err + SBest.eps{m}.
proof. by move=> gt0_eps; have := base_le_ideal &m gt0_eps; smt(). qed.

end section.
