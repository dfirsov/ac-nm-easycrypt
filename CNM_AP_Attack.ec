(* Sanity check 1: the adversary from Firsov-Laur-Zhuchko (ICTAC'22),
   which breaks the Laur-Nyberg definition of every realistic scheme,
   has advantage <= 0 against the a-priori baseline, for EVERY scheme. *)

pragma Goals:printall.

require import AllCore Distr DBool List StdRing StdOrder RealFLub.
require import CNM_AP.
import Biased RField RealOrder.

op m1, m2 : message.

section Hypotheses.

declare axiom m1_neq_m2 : m1 <> m2.

lemma duni12_m1 : mu (duniform [m1; m2]) (pred1 m1) = 1%r / 2%r.
proof. rewrite duniform1E /=; smt(m1_neq_m2). qed.

(* the adversary from the paper; the relation is fixed in init *)
module AL : AdvCNM = {
  var pk : pubkey
  var c, c' : commitment
  var d' : openingkey

  proc init(x : pubkey) : message distr * relation = {
    pk <- x;
    return (duniform [m1; m2], fun (n v : message) => n = m1 /\ v = m1);
  }

  proc commit(y : commitment) : commitment = {
    c <- y;
    (c', d') <$ Commit pk m1;
    return c';
  }

  proc decommit(m : message, d : openingkey) : openingkey * message = {
    var c2, d2;
    (c2, d2) <$ Commit pk m2;
    return if Verify pk (m1, (c, d)) then (d', m1) else (d2, m2);
  }
}.

lemma AL_real &m : Pr[ RealG(AL).main() @ &m : res ] <= 1%r / 2%r.
proof.
have h1 : Pr[ RealG(AL).main() @ &m : RealG.m = m1] = 1%r / 2%r.
+ byphoare => //; proc; inline *.
  seq 5 : (RealG.m = m1) (1%r / 2%r) 1%r (1%r / 2%r) 0%r => //.
  + rnd (pred1 m1); wp; rnd predT; skip => />; rewrite Gen_ll duni12_m1 /=; smt().
  + by auto => /> *; smt(Com_ll).
  by hoare; auto.
have h2 : Pr[ RealG(AL).main() @ &m : res ] <= Pr[ RealG(AL).main() @ &m : RealG.m = m1].
+ byequiv (_: ={glob AL} ==> res{1} => RealG.m{2} = m1) => //.
  proc; inline *.
  by auto => /> /#.
by rewrite -h1.
qed.

lemma prior_AL :
  1%r / 2%r <= prior (duniform [m1; m2]) (fun (n v : message) => n = m1 /\ v = m1).
proof.
have := prior_ub (duniform [m1; m2]) (fun (n v : message) => n = m1 /\ v = m1) m1.
have e : mu (duniform [m1; m2]) (fun n => (fun (n v : message) => n = m1 /\ v = m1) n m1)
        = 1%r / 2%r by rewrite -duni12_m1; apply mu_eq => x /#.
by rewrite e.
qed.

lemma AL_base &m : 1%r / 2%r <= Pr[ Base(AL).main() @ &m : res ].
proof.
have -> : Pr[ Base(AL).main() @ &m : res ]
        = prior (duniform [m1; m2]) (fun (n v : message) => n = m1 /\ v = m1).
+ byphoare => //; proc; inline *; rnd; wp; rnd; skip => /> *.
  rewrite Gen_ll /= dbiasedE /= clamp_id //.
  by rewrite prior_ge0 prior_le1.
exact prior_AL.
qed.

lemma AL_adv &m :
  Pr[ RealG(AL).main() @ &m : res ] - Pr[ Base(AL).main() @ &m : res ] <= 0%r.
proof. by have := AL_real &m; have := AL_base &m; smt(). qed.

end section Hypotheses.
