(* Comparison-based non-malleability with respect to commitment (CNM-C).

   There is no decommit phase: the challenger extracts the value committed
   in c' itself, using an extraction key xk produced by Gen (a trapdoor in
   the CRS model, or an inefficient extractor for perfectly binding schemes).
   Hence the adversary cannot abort selectively after learning m, and the
   Laur-Nyberg idea of comparing against an independent sample n works:

     Adv(A) = Pr[NMC(A).main(false) : res] - Pr[NMC(A).main(true) : res]   *)

pragma Goals:printall.

require import AllCore Distr DBool.

type pubkey, xkey, message, commitment, openingkey.

type relation = message -> message -> bool.

op Gen : (pubkey * xkey) distr.
op Commit : pubkey -> message -> (commitment * openingkey) distr.
op Verify : pubkey -> message * (commitment * openingkey) -> bool.
op ext : xkey -> commitment -> message option.

axiom Gen_ll : is_lossless Gen.
axiom Com_ll pk m : is_lossless (Commit pk m).

(* functional *)
axiom S_correct pk xk m c d :
  (pk, xk) \in Gen => (c, d) \in Commit pk m => Verify pk (m, (c, d)).

(* perfectly binding w.r.t. extraction: every valid opening opens to ext *)
axiom ext_binding pk xk m c d :
  (pk, xk) \in Gen => Verify pk (m, (c, d)) => ext xk c = Some m.


(* ------------------------------------------------------------------ *)
(* the definition                                                      *)

module type AdvNMC = {
  proc init(pk : pubkey) : message distr * relation
  proc commit(c : commitment) : commitment
}.

module NMC(A : AdvNMC) = {
  var xk : xkey
  var m, n : message
  var c, c' : commitment

  proc main(b : bool) : bool = {
    var pk, md, rel, d;
    (pk, xk)   <$ Gen;
    (md, rel)  <@ A.init(pk);
    m          <$ md;
    n          <$ md;
    (c, d)     <$ Commit pk m;
    c'         <@ A.commit(c);
    return c' <> c /\ ext xk c' <> None /\ rel (if b then n else m) (oget (ext xk c'));
  }
}.


(* ------------------------------------------------------------------ *)
(* one-sided security is enough: negating the relation flips the sign  *)

module Neg(A : AdvNMC) : AdvNMC = {
  proc init(pk : pubkey) : message distr * relation = {
    var md, rel;
    (md, rel) <@ A.init(pk);
    return (md, fun x y => !rel x y);
  }

  proc commit(c : commitment) : commitment = {
    var c';
    c' <@ A.commit(c);
    return c';
  }
}.

section Negation.

declare module A <: AdvNMC {-NMC}.

local lemma neg_split &m b :
  Pr[ NMC(Neg(A)).main(b) @ &m : res ]
  = Pr[ NMC(A).main(b) @ &m : NMC.c' <> NMC.c /\ ext NMC.xk NMC.c' <> None ]
  - Pr[ NMC(A).main(b) @ &m : res ].
proof.
have -> : Pr[ NMC(Neg(A)).main(b) @ &m : res ]
        = Pr[ NMC(A).main(b) @ &m : (NMC.c' <> NMC.c /\ ext NMC.xk NMC.c' <> None) /\ !res ].
+ byequiv => //; proc; inline *; wp.
  call (: true); auto; call (: true); auto => /> /#.
have -> : Pr[ NMC(A).main(b) @ &m : NMC.c' <> NMC.c /\ ext NMC.xk NMC.c' <> None ]
        = Pr[ NMC(A).main(b) @ &m : (NMC.c' <> NMC.c /\ ext NMC.xk NMC.c' <> None) /\ res ]
        + Pr[ NMC(A).main(b) @ &m : (NMC.c' <> NMC.c /\ ext NMC.xk NMC.c' <> None) /\ !res ].
+ by rewrite Pr[mu_split res].
have -> : Pr[ NMC(A).main(b) @ &m : (NMC.c' <> NMC.c /\ ext NMC.xk NMC.c' <> None) /\ res ]
        = Pr[ NMC(A).main(b) @ &m : res ].
+ by byequiv => //; proc; call (: true); auto; call (: true); auto => /> /#.
by ring.
qed.

local lemma ok_eq &m :
  Pr[ NMC(A).main(false) @ &m : NMC.c' <> NMC.c /\ ext NMC.xk NMC.c' <> None ]
  = Pr[ NMC(A).main(true) @ &m : NMC.c' <> NMC.c /\ ext NMC.xk NMC.c' <> None ].
proof. by byequiv => //; proc; call (: true); auto; call (: true); auto. qed.

lemma neg_adv &m :
    Pr[ NMC(Neg(A)).main(false) @ &m : res ] - Pr[ NMC(Neg(A)).main(true) @ &m : res ]
  = - (Pr[ NMC(A).main(false) @ &m : res ] - Pr[ NMC(A).main(true) @ &m : res ]).
proof. by rewrite !neg_split ok_eq; ring. qed.

end section Negation.


(* ------------------------------------------------------------------ *)
(* CNM-C implies simulation-based NM w.r.t. commitment, with an        *)
(* explicit black-box simulator that runs A on a commitment to a fresh *)
(* sample and extracts.  The simulator never sees anything about m.   *)

module type Sim = {
  proc out(pk : pubkey, xk : xkey, md : message distr, rel : relation) : message
}.

module IdealC(A : AdvNMC, S : Sim) = {
  proc main() : bool = {
    var pk, xk, md, rel, w, m;
    (pk, xk)   <$ Gen;
    (md, rel)  <@ A.init(pk);
    w          <@ S.out(pk, xk, md, rel);
    m          <$ md;
    return rel m w;
  }
}.

module SA(A : AdvNMC) : Sim = {
  proc out(pk : pubkey, xk : xkey, md : message distr, rel : relation) : message = {
    var m', c, d, c';
    m'      <$ md;
    (c, d)  <$ Commit pk m';
    c'      <@ A.commit(c);
    return if c' <> c /\ ext xk c' <> None then oget (ext xk c') else witness;
  }
}.

section Simulation.

declare module A <: AdvNMC {-NMC}.

lemma g1_le_ideal &m :
  Pr[ NMC(A).main(true) @ &m : res ] <= Pr[ IdealC(A, SA(A)).main() @ &m : res ].
proof.
byequiv => //; proc; inline *.
swap{1} 4 2.
rnd; wp; call (: true); rnd; rnd; wp; call (: true); auto => /> /#.
qed.

(* the real success is matched by the simulator up to the CNM-C advantage *)
lemma cnmc_implies_sim &m :
  Pr[ NMC(A).main(false) @ &m : res ]
  <= Pr[ IdealC(A, SA(A)).main() @ &m : res ]
   + (Pr[ NMC(A).main(false) @ &m : res ] - Pr[ NMC(A).main(true) @ &m : res ]).
proof. by have := g1_le_ideal &m; smt(). qed.

end section Simulation.
