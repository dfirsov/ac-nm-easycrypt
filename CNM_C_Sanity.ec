(* Sanity checks for CNM-C:
   - schemes with a mauling map on commitments are rejected (Adv >= 1/2);
   - CNM-C implies hiding:  Adv_hid(B) <= Adv(AH(B)) + gamma.            *)

pragma Goals:printall.

require import AllCore Distr DBool List StdRing StdOrder.
require import CNM_C.
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

op f : message -> message.
op mc : pubkey -> commitment -> commitment.

declare axiom maul pk xk m c d :
  (pk, xk) \in Gen => (c, d) \in Commit pk m =>
  ext xk (mc pk c) = Some (f m) /\ mc pk c <> c.

declare axiom f_12 : f m1 <> f m2.

module AM : AdvNMC = {
  var pk : pubkey

  proc init(x : pubkey) : message distr * relation = {
    pk <- x;
    return (duniform [m1; m2], fun (n v : message) => v = f n);
  }

  proc commit(c : commitment) : commitment = {
    return mc pk c;
  }
}.

lemma AM_g0 &m : Pr[ NMC(AM).main(false) @ &m : res ] = 1%r.
proof.
byphoare (_: !b ==> _) => //; proc; inline *; auto => />.
rewrite Gen_ll /= => &hr nb [pk xk] h /=.
split; first by apply duniform_ll.
move=> _ m _ n _; rewrite Com_ll /= => -[c d] cd_in /=.
have [-> ->] := maul pk xk m c d h cd_in.
done.
qed.

lemma AM_g1 &m : Pr[ NMC(AM).main(true) @ &m : res ] <= 1%r / 2%r.
proof.
have h : Pr[ NMC(AM).main(true) @ &m : res ] <= Pr[ NMC(AM).main(true) @ &m : NMC.n = NMC.m ].
+ byequiv => //; proc; inline *; auto => /> [pk xk] h m m_in n n_in [c d] cd_in.
  have [-> _] := maul pk xk m c d h cd_in.
  by move: m_in n_in; rewrite !supp12 /=; smt(f_12).
apply (ler_trans _ _ _ h).
byphoare => //; proc; inline *.
seq 6 : (NMC.n = NMC.m) (1%r / 2%r) 1%r (1%r / 2%r) 0%r => //.
+ seq 5 : (md = duniform [m1; m2]) 1%r (1%r / 2%r) 0%r 0%r => //.
  + by rnd (pred1 NMC.m); auto => />; smt(duni12_le).
  by hoare; auto.
by hoare; auto.
qed.

lemma AM_adv &m :
  1%r / 2%r <= Pr[ NMC(AM).main(false) @ &m : res ] - Pr[ NMC(AM).main(true) @ &m : res ].
proof. by rewrite AM_g0; have := AM_g1 &m; smt(). qed.


(* ------------------------------------------------------------------ *)
(* CNM-C implies hiding                                                *)

op gamma : real.

declare axiom Com_coll pk m c :
  mu (Commit pk m) (fun (cd : commitment * openingkey) => cd.`1 = c) <= gamma.

module type AdvHid = {
  proc guess(pk : pubkey, c : commitment) : bool
}.

module Hid(B : AdvHid) = {
  proc main() : bool = {
    var pk, xk, b, b', c, d;
    (pk, xk) <$ Gen;
    b        <$ {0,1};
    (c, d)   <$ Commit pk (if b then m1 else m2);
    b'       <@ B.guess(pk, c);
    return b = b';
  }
}.

module AH(B : AdvHid) : AdvNMC = {
  var pk : pubkey
  var mb : message

  proc init(x : pubkey) : message distr * relation = {
    pk <- x;
    return (duniform [m1; m2], fun (n v : message) => n = v);
  }

  proc commit(c : commitment) : commitment = {
    var b', c', d';
    b'       <@ B.guess(pk, c);
    mb       <- if b' then m1 else m2;
    (c', d') <$ Commit pk mb;
    return c';
  }
}.

section Hiding.

declare module B <: AdvHid {-AH, -NMC}.

local lemma hid_le &m :
  Pr[ Hid(B).main() @ &m : res ] <= Pr[ NMC(AH(B)).main(false) @ &m : AH.mb = NMC.m ].
proof.
byequiv => //; proc; inline *.
wp; rnd{2}; wp; call (: true); wp; rnd; rnd{2}.
rnd (fun b => if b then m1 else m2) (fun m => m = m1); wp; rnd; skip => />.
move=> [pk xk] _; split => [m | _].
+ by rewrite supp12 => -[|] ->; smt(m1_neq_m2).
split => [m | _].
+ rewrite supp12 => -[|] ->; rewrite duniform1E /= dbool1E; smt(m1_neq_m2).
move=> b _; split; first by rewrite supp12; case b.
move=> _; split; first by case b => /=; smt(m1_neq_m2).
move=> _; split; first by apply duniform_ll.
by move=> _ n _ cd _ r; apply Com_ll.
qed.

local lemma g0_imp :
  hoare[ NMC(AH(B)).main : !b ==> AH.mb = NMC.m => res \/ NMC.c' = NMC.c ].
proof.
proc; inline *; auto; call (: true); auto => /> &hr nb [pk xk] h m _ n _ [c d] _ r [c' d'] cd'_in /=.
have -> := ext_binding pk xk (if r then m1 else m2) c' d' h (S_correct pk xk _ _ _ h cd'_in).
smt().
qed.

local lemma copy_le &m : Pr[ NMC(AH(B)).main(false) @ &m : NMC.c' = NMC.c ] <= gamma.
proof.
byphoare => //; proc; inline *.
seq 10 : true 1%r gamma 0%r 0%r => //.
+ wp; rnd (fun (cd : commitment * openingkey) => cd.`1 = NMC.c).
  by skip => /> &hr; apply Com_coll.
by move=> _; have := Com_coll witness witness witness; smt(ge0_mu).
qed.

local lemma g1_le &m : Pr[ NMC(AH(B)).main(true) @ &m : res ] <= 1%r / 2%r.
proof.
have h : Pr[ NMC(AH(B)).main(true) @ &m : res ]
      <= Pr[ NMC(AH(B)).main(true) @ &m : NMC.n = AH.mb ].
+ byequiv => //; proc; inline *; auto; call (: true); auto => /> [pk xk] hg m _ n _ [c d] _ r [c' d'] cd'_in.
  have := ext_binding pk xk (if r then m1 else m2) c' d' hg (S_correct pk xk _ _ _ hg cd'_in).
  smt().
apply (ler_trans _ _ _ h).
byphoare => //; proc; inline *.
swap 6 6.
seq 11 : (md = duniform [m1; m2]) 1%r (1%r / 2%r) 0%r 0%r => //.
+ by rnd (pred1 AH.mb); auto => />; smt(duni12_le).
by hoare; auto; call (: true); auto.
qed.

lemma cnmc_implies_hiding &m :
  Pr[ Hid(B).main() @ &m : res ] - 1%r / 2%r
  <= (Pr[ NMC(AH(B)).main(false) @ &m : res ] - Pr[ NMC(AH(B)).main(true) @ &m : res ])
     + gamma.
proof.
have h1 := hid_le &m.
have h2 := copy_le &m.
have h3 := g1_le &m.
have h4 : Pr[ NMC(AH(B)).main(false) @ &m : AH.mb = NMC.m ]
       <= Pr[ NMC(AH(B)).main(false) @ &m : res ]
        + Pr[ NMC(AH(B)).main(false) @ &m : NMC.c' = NMC.c ].
+ have h0 : Pr[ NMC(AH(B)).main(false) @ &m :
                  AH.mb = NMC.m /\ !(res \/ NMC.c' = NMC.c) ] = 0%r.
  + by byphoare (_: !b ==> _) => //; hoare; conseq g0_imp => /#.
  have : Pr[ NMC(AH(B)).main(false) @ &m : AH.mb = NMC.m ]
      <= Pr[ NMC(AH(B)).main(false) @ &m : res \/ NMC.c' = NMC.c ].
  + rewrite Pr[mu_split (res \/ NMC.c' = NMC.c)] h0 /=.
    by rewrite Pr[mu_sub] => /#.
  rewrite Pr[mu_or]; smt(ge0_mu).
smt().
qed.

end section Hiding.

end section Hypotheses.
