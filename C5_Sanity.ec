(* Sanity checks for C5:
   - schemes with a mauling map are rejected: Real - B - sqrt(B V) >= 1/2;
   - C5 implies hiding:  Adv_hid(B) <= Adv(AH(B)) + gamma.
   Both adversaries never open invalidly, so V = 0 and the sqrt term vanishes. *)

pragma Goals:printall.

require import AllCore Distr DBool List StdRing StdOrder RealExp.
require import C5.
import RField RealOrder.

op m1, m2 : message.

section Hypotheses.

declare axiom m1_neq_m2 : m1 <> m2.

lemma duni12_le (x : message) : mu1 (duniform [m1; m2]) x <= 1%r / 2%r.
proof. rewrite duniform1E /=; smt(m1_neq_m2). qed.

lemma supp12 x : x \in duniform [m1; m2] <=> x = m1 \/ x = m2.
proof. by rewrite supp_duniform. qed.


(* ------------------------------------------------------------------ *)
(* malleable schemes are rejected                                      *)

section Mauling.

op f : message -> message.
op mc : pubkey -> commitment -> commitment.
op mo : pubkey -> openingkey -> openingkey.

declare axiom maul pk m c d :
  pk \in Gen => (c, d) \in Commit pk m =>
  Verify pk (f m, (mc pk c, mo pk d)) /\ mc pk c <> c.

declare axiom f_12 : f m1 <> f m2.

module AM : AdvC5 = {
  var pk : pubkey

  proc init(x : pubkey) : message distr = {
    pk <- x;
    return duniform [m1; m2];
  }

  proc commit(c : commitment) : (commitment * relation) option = {
    return Some (mc pk c, fun (n v : message) => v = f n);
  }

  proc decommit(m : message, d : openingkey) : (openingkey * message) option = {
    return Some (mo pk d, f m);
  }
}.

lemma AM_real &m : Pr[ G(AM).main() @ &m : G.v /\ G.rel G.m G.m' ] = 1%r.
proof.
byphoare => //; proc; inline *; auto => />.
rewrite Gen_ll /= => pk pk_in.
split; first by apply duniform_ll.
move=> _ m _ n _; rewrite Com_ll /= => -[c d] cd_in /=.
by have [-> ->] := maul pk m c d pk_in cd_in.
qed.

lemma AM_inv &m : Pr[ G(AM).main() @ &m : G.opd /\ !G.v ] = 0%r.
proof.
byphoare => //; hoare; proc; inline *; auto => /> pk pk_in m _ n _ [c d] cd_in.
by have [-> _] := maul pk m c d pk_in cd_in.
qed.

lemma AM_bl &m : Pr[ G(AM).main() @ &m : G.v /\ G.rel G.n G.m' ] <= 1%r / 2%r.
proof.
have h : Pr[ G(AM).main() @ &m : G.v /\ G.rel G.n G.m' ]
      <= Pr[ G(AM).main() @ &m : G.n = G.m ].
+ byequiv => //; proc; inline *; auto => /> pk _ m m_in n n_in [c d] _.
  move: m_in n_in; rewrite !supp12; smt(f_12).
apply (ler_trans _ _ _ h).
byphoare => //; proc; inline *.
seq 6 : (G.n = G.m) (1%r / 2%r) 1%r (1%r / 2%r) 0%r => //.
+ seq 5 : (G.md = duniform [m1; m2]) 1%r (1%r / 2%r) 0%r 0%r => //.
  + by rnd (pred1 G.m); auto => />; smt(duni12_le).
  by hoare; auto.
by hoare; auto.
qed.

lemma AM_adv &m :
  1%r / 2%r <= Pr[ G(AM).main() @ &m : G.v /\ G.rel G.m G.m' ]
             - Pr[ G(AM).main() @ &m : G.v /\ G.rel G.n G.m' ]
             - sqrt (Pr[ G(AM).main() @ &m : G.v /\ G.rel G.n G.m' ]
                   * Pr[ G(AM).main() @ &m : G.opd /\ !G.v ]).
proof. by rewrite AM_real AM_inv mulr0 sqrt0; have := AM_bl &m; smt(). qed.

end section Mauling.


(* ------------------------------------------------------------------ *)
(* C5 implies hiding                                                   *)

op gamma : real.

declare axiom Com_correct pk m c d :
  pk \in Gen => (c, d) \in Commit pk m => Verify pk (m, (c, d)).

declare axiom Com_coll pk m c :
  mu (Commit pk m) (fun (cd : commitment * openingkey) => cd.`1 = c) <= gamma.

module type AdvHid = {
  proc guess(pk : pubkey, c : commitment) : bool
}.

module Hid(B : AdvHid) = {
  proc main() : bool = {
    var pk, b, b', c, d;
    pk       <$ Gen;
    b        <$ {0,1};
    (c, d)   <$ Commit pk (if b then m1 else m2);
    b'       <@ B.guess(pk, c);
    return b = b';
  }
}.

module AH(B : AdvHid) : AdvC5 = {
  var pk : pubkey
  var mb : message
  var d' : openingkey

  proc init(x : pubkey) : message distr = {
    pk <- x;
    return duniform [m1; m2];
  }

  proc commit(c : commitment) : (commitment * relation) option = {
    var b', c';
    b'       <@ B.guess(pk, c);
    mb       <- if b' then m1 else m2;
    (c', d') <$ Commit pk mb;
    return Some (c', fun (n v : message) => n = v);
  }

  proc decommit(m : message, d : openingkey) : (openingkey * message) option = {
    return Some (d', mb);
  }
}.

section Hiding.

declare module B <: AdvHid {-AH, -G}.

local lemma hid_le &m :
  Pr[ Hid(B).main() @ &m : res ] <= Pr[ G(AH(B)).main() @ &m : AH.mb = G.m ].
proof.
byequiv => //; proc; inline *.
wp; rnd{2}; wp; call (: true); wp; rnd; rnd{2}.
rnd (fun b => if b then m1 else m2) (fun m => m = m1); wp; rnd; skip => />.
move=> pk _; split => [m | _].
+ by rewrite supp12 => -[|] ->; smt(m1_neq_m2).
split => [m | _].
+ rewrite supp12 => -[|] ->; rewrite duniform1E /= dbool1E; smt(m1_neq_m2).
move=> b _; split; first by rewrite supp12; case b.
move=> _; split; first by case b => /=; smt(m1_neq_m2).
move=> _; split; first by apply duniform_ll.
by move=> _ n _ cd _ r; apply Com_ll.
qed.

local lemma g0_imp :
  hoare[ G(AH(B)).main : true ==>
         AH.mb = G.m => (G.v /\ G.rel G.m G.m') \/ G.c' = Some G.c ].
proof.
proc; inline *; auto; call (: true); auto => /> pk pk_in m _ n _ [c d] _ r [c' d'] cd'_in /=.
case: (c' = c) => //= _.
by move=> _; apply (Com_correct pk _ c' d' pk_in cd'_in).
qed.

local lemma inv0 : hoare[ G(AH(B)).main : true ==> !(G.opd /\ !G.v) ].
proof.
proc; inline *; auto; call (: true); auto => /> pk pk_in m _ n _ [c d] _ r [c' d'] cd'_in /=.
case: (c' = c) => //= _.
by apply (Com_correct pk _ c' d' pk_in cd'_in).
qed.

local lemma copy_le &m : Pr[ G(AH(B)).main() @ &m : G.c' = Some G.c ] <= gamma.
proof.
byphoare => //; proc; inline *.
seq 10 : true 1%r gamma 0%r 0%r => //.
+ wp; rnd (fun (cd : commitment * openingkey) => cd.`1 = G.c).
  by skip => /> &hr; apply Com_coll.
by move=> _; have := Com_coll witness witness witness; smt(ge0_mu).
qed.

local lemma g1_le &m : Pr[ G(AH(B)).main() @ &m : G.v /\ G.rel G.n G.m' ] <= 1%r / 2%r.
proof.
have h : Pr[ G(AH(B)).main() @ &m : G.v /\ G.rel G.n G.m' ]
      <= Pr[ G(AH(B)).main() @ &m : G.n = AH.mb ].
+ byequiv => //; proc; inline *; auto; call (: true); auto => /> /#.
apply (ler_trans _ _ _ h).
byphoare => //; proc; inline *.
swap 6 12.
seq 17 : (G.md = duniform [m1; m2]) 1%r (1%r / 2%r) 0%r 0%r => //.
+ by rnd (pred1 AH.mb); auto => />; smt(duni12_le).
by hoare; auto; call (: true); auto.
qed.

lemma cnm5_implies_hiding &m :
  Pr[ Hid(B).main() @ &m : res ] - 1%r / 2%r
  <= (Pr[ G(AH(B)).main() @ &m : G.v /\ G.rel G.m G.m' ]
      - Pr[ G(AH(B)).main() @ &m : G.v /\ G.rel G.n G.m' ]
      - sqrt (Pr[ G(AH(B)).main() @ &m : G.v /\ G.rel G.n G.m' ]
              * Pr[ G(AH(B)).main() @ &m : G.opd /\ !G.v ]))
     + gamma.
proof.
have -> : Pr[ G(AH(B)).main() @ &m : G.opd /\ !G.v ] = 0%r.
+ by byphoare => //; hoare; conseq inv0.
rewrite mulr0 sqrt0 /=.
have h1 := hid_le &m.
have h2 := copy_le &m.
have h3 := g1_le &m.
have h4 : Pr[ G(AH(B)).main() @ &m : AH.mb = G.m ]
       <= Pr[ G(AH(B)).main() @ &m : G.v /\ G.rel G.m G.m' ]
        + Pr[ G(AH(B)).main() @ &m : G.c' = Some G.c ].
+ have h0 : Pr[ G(AH(B)).main() @ &m :
                  AH.mb = G.m /\ !((G.v /\ G.rel G.m G.m') \/ G.c' = Some G.c) ] = 0%r.
  + by byphoare => //; hoare; conseq g0_imp => /#.
  have : Pr[ G(AH(B)).main() @ &m : AH.mb = G.m ]
      <= Pr[ G(AH(B)).main() @ &m : (G.v /\ G.rel G.m G.m') \/ G.c' = Some G.c ].
  + rewrite Pr[mu_split ((G.v /\ G.rel G.m G.m') \/ G.c' = Some G.c)] h0 /=.
    by rewrite Pr[mu_sub] => /#.
  rewrite Pr[mu_or]; smt(ge0_mu).
smt().
qed.

end section Hiding.

end section Hypotheses.
