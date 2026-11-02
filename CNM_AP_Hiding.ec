(* CNM-AP implies hiding (for commitments with sufficiently random
   commitment values):
     Adv_hid(B) <= Adv_cnm(AH(B)) + gamma
   where gamma bounds the probability that a fresh commitment hits a
   fixed value.                                                          *)

pragma Goals:printall.

require import AllCore Distr DBool List StdRing StdOrder RealFLub.
require import CNM_AP.
import Biased RField RealOrder.

op m1, m2 : message.

section Hypotheses.

declare axiom m1_neq_m2 : m1 <> m2.

(* the scheme is functional *)
declare axiom S_correct pk m c d :
  pk \in Gen => (c, d) \in Commit pk m => Verify pk (m, (c, d)).

(* commitment values have min-entropy at least -log gamma *)
op gamma : real.

declare axiom Com_coll pk m c :
  mu (Commit pk m) (fun (cd : commitment * openingkey) => cd.`1 = c) <= gamma.

module type AdvHid = {
  proc guess(pk : pubkey, c : commitment) : bool
}.

module Hid(B : AdvHid) = {
  proc main() : bool = {
    var pk, b, b', c, d;
    pk      <$ Gen;
    b       <$ {0,1};
    (c, d)  <$ Commit pk (if b then m1 else m2);
    b'      <@ B.guess(pk, c);
    return b = b';
  }
}.

(* the NM adversary: guess the message from c, commit to the guess *)
module AH(B : AdvHid) : AdvCNM = {
  var pk : pubkey
  var mb : message
  var d' : openingkey

  proc init(x : pubkey) : message distr * relation = {
    pk <- x;
    return (duniform [m1; m2], fun (n v : message) => n = v);
  }

  proc commit(c : commitment) : commitment = {
    var b', c';
    b'       <@ B.guess(pk, c);
    mb       <- if b' then m1 else m2;
    (c', d') <$ Commit pk mb;
    return c';
  }

  proc decommit(m : message, d : openingkey) : openingkey * message = {
    return (d', mb);
  }
}.

lemma prior_eq12 : prior (duniform [m1; m2]) (fun (n v : message) => n = v) = 1%r / 2%r.
proof.
apply ler_anti; split.
+ apply flub_le_ub => w /=.
  by rewrite duniformE /= m1_neq_m2 /=; smt(m1_neq_m2).
have := prior_ub (duniform [m1; m2]) (fun (n v : message) => n = v) m1.
by rewrite /= duniformE /= m1_neq_m2 /=; smt(m1_neq_m2).
qed.

section.

declare module B <: AdvHid {-AH, -RealG}.

lemma AH_base &m : Pr[ Base(AH(B)).main() @ &m : res ] = 1%r / 2%r.
proof.
byphoare => //; proc; inline *; rnd; wp; rnd; skip => /> *.
rewrite Gen_ll /= dbiasedE /= prior_eq12 clamp_id //; smt().
qed.

local lemma hid_le_win &m :
  Pr[ Hid(B).main() @ &m : res ]
  <= Pr[ RealG(AH(B)).main() @ &m :
           Verify AH.pk (RealG.m', (RealG.c', AH.d')) /\ RealG.m = RealG.m' ].
proof.
byequiv => //; proc; inline *.
wp; rnd{2}; wp; call (: true); wp; rnd.
rnd (fun b => if b then m1 else m2) (fun m => m = m1); wp; rnd; skip => />.
move=> pk pk_in.
split; first by move=> m; rewrite supp_duniform /= => -[|] ->; smt(m1_neq_m2).
move=> _; split.
+ move=> m; rewrite supp_duniform /= => -[|] ->;
    rewrite duniform1E /= dbool1E; smt(m1_neq_m2).
move=> _ b _; split; first by rewrite supp_duniform /=; case b.
move=> _; split; first by case b => /=; smt(m1_neq_m2).
move=> _ cd _ r; rewrite Com_ll /= => -[c' d'] cd'_in _ /=.
by apply (S_correct pk).
qed.

local lemma copy_le &m :
  Pr[ RealG(AH(B)).main() @ &m : RealG.c' = RealG.c ] <= gamma.
proof.
byphoare => //; proc; inline *.
seq 9 : true 1%r gamma 0%r 0%r => //.
+ wp; rnd (fun (cd : commitment * openingkey) => cd.`1 = RealG.c).
  by skip => /> &hr; apply Com_coll.
move=> _; have := Com_coll witness witness witness.
have := ge0_mu (Commit witness witness) (fun (cd : commitment * openingkey) => cd.`1 = witness).
smt().
qed.

lemma cnm_ap_implies_hiding &m :
  Pr[ Hid(B).main() @ &m : res ] - 1%r / 2%r
  <= (Pr[ RealG(AH(B)).main() @ &m : res ] - Pr[ Base(AH(B)).main() @ &m : res ])
     + gamma.
proof.
rewrite AH_base.
have h1 := hid_le_win &m.
have h2 := copy_le &m.
have h3 : Pr[ RealG(AH(B)).main() @ &m :
                Verify AH.pk (RealG.m', (RealG.c', AH.d')) /\ RealG.m = RealG.m' ]
       <= Pr[ RealG(AH(B)).main() @ &m : res ]
        + Pr[ RealG(AH(B)).main() @ &m : RealG.c' = RealG.c ].
+ have -> : Pr[ RealG(AH(B)).main() @ &m : res ]
          + Pr[ RealG(AH(B)).main() @ &m : RealG.c' = RealG.c ]
          = Pr[ RealG(AH(B)).main() @ &m : res \/ RealG.c' = RealG.c ]
          + Pr[ RealG(AH(B)).main() @ &m : res /\ RealG.c' = RealG.c ].
  + by rewrite Pr[mu_or]; ring.
  have : Pr[ RealG(AH(B)).main() @ &m :
               Verify AH.pk (RealG.m', (RealG.c', AH.d')) /\ RealG.m = RealG.m' ]
      <= Pr[ RealG(AH(B)).main() @ &m : res \/ RealG.c' = RealG.c ].
  + byequiv => //; proc; inline *; wp; rnd; wp; call (: true); auto => /> /#.
  smt(ge0_mu).
smt().
qed.

end section.

end section Hypotheses.
