(* CNM-AP implies binding (for commitments with sufficiently random
   commitment values):
     Adv_bind(BB) <= 2 * (Adv_cnm(AB(BB)) + gamma)
   This relies on the refined copy rule: only (c' = c /\ m' = m) is
   excluded, so re-using a commitment that can be opened in two ways
   counts as an attack.                                                  *)

pragma Goals:printall.

require import AllCore Distr DBool List StdRing StdOrder RealFLub.
require import CNM_AP.
import Biased RField RealOrder.

op m1, m2 : message.

section Hypotheses.

declare axiom m1_neq_m2 : m1 <> m2.

declare axiom S_correct pk m c d :
  pk \in Gen => (c, d) \in Commit pk m => Verify pk (m, (c, d)).

op gamma : real.

declare axiom Com_coll pk m c :
  mu (Commit pk m) (fun (cd : commitment * openingkey) => cd.`1 = c) <= gamma.

lemma gamma_ge0 : 0%r <= gamma.
proof.
have := Com_coll witness witness witness.
have := ge0_mu (Commit witness witness) (fun (cd : commitment * openingkey) => cd.`1 = witness).
smt().
qed.

lemma prior_pair (a b : message) : a <> b =>
  prior (duniform [a; b]) (fun (n v : message) => n = v) = 1%r / 2%r.
proof.
move=> neq_ab; apply ler_anti; split.
+ apply flub_le_ub => w /=.
  by rewrite duniformE /= neq_ab /=; smt().
have := prior_ub (duniform [a; b]) (fun (n v : message) => n = v) a.
by rewrite /= duniformE /= neq_ab /=; smt().
qed.

module type AdvBind = {
  proc find(pk : pubkey) : commitment * message * openingkey * message * openingkey
}.

module Bind(BB : AdvBind) = {
  proc main() : bool = {
    var pk, c, v0, d0, v1, d1;
    pk                  <$ Gen;
    (c, v0, d0, v1, d1) <@ BB.find(pk);
    return v0 <> v1 /\ Verify pk (v0, (c, d0)) /\ Verify pk (v1, (c, d1));
  }
}.

(* the NM adversary: if BB produced a double opening (v0, v1) of cb, use
   M = uniform {v0, v1} and open cb to whatever m turns out to be;
   otherwise commit honestly to m1 *)
module AB(BB : AdvBind) : AdvCNM = {
  var pk : pubkey
  var ok : bool
  var cb : commitment
  var v0, v1 : message
  var d0, d1, df : openingkey

  proc init(x : pubkey) : message distr * relation = {
    pk <- x;
    (cb, v0, d0, v1, d1) <@ BB.find(pk);
    ok <- v0 <> v1 /\ Verify pk (v0, (cb, d0)) /\ Verify pk (v1, (cb, d1));
    return (if ok then duniform [v0; v1] else duniform [m1; m2],
            fun (n v : message) => n = v);
  }

  proc commit(c : commitment) : commitment = {
    var c';
    if (ok) {
      c' <- cb;
    } else {
      (c', df) <$ Commit pk m1;
    }
    return c';
  }

  proc decommit(m : message, d : openingkey) : openingkey * message = {
    return if ok then ((if m = v0 then d0 else d1), m) else (df, m1);
  }
}.

(* an auxiliary game: an independent coin or a binding break *)
module H(BB : AdvBind) = {
  proc main() : bool = {
    var e, r;
    e <$ {0,1};
    r <@ Bind(BB).main();
    return r \/ e;
  }
}.

section.

declare module BB <: AdvBind {-AB, -RealG}.

declare axiom BB_ll : islossless BB.find.

lemma AB_base &m : Pr[ Base(AB(BB)).main() @ &m : res ] = 1%r / 2%r.
proof.
byphoare => //; proc; inline *; rnd; wp.
call (: true); first by apply BB_ll.
auto => /> *; rewrite Gen_ll /= => pk _ r /=.
rewrite dbiasedE /=.
case (r.`2 <> r.`4 /\ Verify pk (r.`2, (r.`1, r.`3)) /\ Verify pk (r.`4, (r.`1, r.`5))) => h /=.
+ by rewrite prior_pair; smt().
by rewrite prior_pair; smt(m1_neq_m2).
qed.

local lemma H_pr &m :
  Pr[ H(BB).main() @ &m : res ] = 1%r / 2%r + Pr[ Bind(BB).main() @ &m : res ] / 2%r.
proof.
have phB : phoare[ Bind(BB).main : (glob BB) = (glob BB){m} ==> res ]
           = Pr[ Bind(BB).main() @ &m : res ].
+ bypr=> &m0; split; first by rewrite Pr [mu_ge0].
  move=> Hg; byequiv (_: ={glob BB} ==> ={res}) => //; first by sim.
byphoare (_: (glob BB) = (glob BB){m} ==> _) => //; proc.
seq 1 : e (1%r / 2%r) 1%r (1%r / 2%r) (Pr[ Bind(BB).main() @ &m : res ])
          ((glob BB) = (glob BB){m}).
+ by auto.
+ by rnd; skip => />; rewrite dboolE.
+ call (: true); last by skip => /> /#.
  by call BB_ll; auto => />; rewrite Gen_ll.
+ by rnd; skip => />; rewrite dboolE.
+ by call phB; skip => /> /#.
smt().
qed.

local lemma H_le_E &m :
  Pr[ H(BB).main() @ &m : res ] <= Pr[ RealG(AB(BB)).main() @ &m : RealG.m = RealG.m' ].
proof.
byequiv => //; proc; inline *.
swap{1} 1 3.
seq 4 7 : (r{1} = AB.ok{2} /\ (!AB.ok{2} => (e{1} <=> RealG.m{2} = m1))).
+ rnd (fun e => if AB.ok{2} then (if e then AB.v0{2} else AB.v1{2})
                else (if e then m1 else m2))
      (fun m => if AB.ok{2} then m = AB.v0{2} else m = m1).
  wp; call (: true); auto => /> pk pk_in r.
  case (r.`2 <> r.`4 /\ Verify pk (r.`2, (r.`1, r.`3)) /\ Verify pk (r.`4, (r.`1, r.`5)))
    => h.
  + have neq : r.`2 <> r.`4 by smt().
    split; first by move=> m; rewrite supp_duniform /= => -[|] ->; smt().
    move=> _; split.
    + move=> m; rewrite supp_duniform /= => -[|] ->;
        rewrite duniform1E dbool1E /= neq /=; smt().
    by move=> _ e _; rewrite supp_duniform /=; smt().
  split; first by move=> m; rewrite supp_duniform /= => -[|] ->; smt(m1_neq_m2).
  move=> _; split.
  + move=> m; rewrite supp_duniform /= => -[|] ->;
      rewrite duniform1E dbool1E /= m1_neq_m2 /=; smt(m1_neq_m2).
  by move=> _ e _; rewrite supp_duniform /=; smt(m1_neq_m2).
seq 0 2 : (r{1} = AB.ok{2} /\ (!AB.ok{2} => (e{1} <=> RealG.m{2} = m1))).
+ by wp; rnd{2}; skip => />; smt(Com_ll).
if{2}.
+ by auto => /> /#.
by wp; rnd{2}; skip => />; smt(Com_ll).
qed.

local lemma E_imp :
  hoare[ RealG(AB(BB)).main : true ==>
           RealG.m = RealG.m' => res \/ RealG.c' = RealG.c ].
proof.
proc; inline *.
seq 9 : (pk \in Gen /\ AB.pk = pk /\ RealG.c = c /\ rel = (fun (n v : message) => n = v) /\
         (AB.ok => (RealG.m = AB.v0 \/ RealG.m = AB.v1) /\
                   Verify AB.pk (AB.v0, (AB.cb, AB.d0)) /\
                   Verify AB.pk (AB.v1, (AB.cb, AB.d1)))).
+ wp; rnd; rnd; wp; call (: true); auto => /> pk pk_in r m.
  move=> + cd _ h1 h2 h3; rewrite h1 h2 h3 /= supp_duniform /= /#.
if.
+ auto => /> &hr pk_in h ok.
  by move: (h ok) => [#] [] -> //; smt().
auto => /> &hr pk_in _ nok [c' df] cd_in /=.
by rewrite (S_correct pk{hr} m1 c' df) //=; smt().
qed.

local lemma E_le &m :
  Pr[ RealG(AB(BB)).main() @ &m : RealG.m = RealG.m' ]
  <= Pr[ RealG(AB(BB)).main() @ &m : res ]
   + Pr[ RealG(AB(BB)).main() @ &m : RealG.c' = RealG.c ].
proof.
have -> : Pr[ RealG(AB(BB)).main() @ &m : res ]
        + Pr[ RealG(AB(BB)).main() @ &m : RealG.c' = RealG.c ]
        = Pr[ RealG(AB(BB)).main() @ &m : res \/ RealG.c' = RealG.c ]
        + Pr[ RealG(AB(BB)).main() @ &m : res /\ RealG.c' = RealG.c ].
+ by rewrite Pr[mu_or]; ring.
have : Pr[ RealG(AB(BB)).main() @ &m : RealG.m = RealG.m' ]
    <= Pr[ RealG(AB(BB)).main() @ &m : res \/ RealG.c' = RealG.c ].
+ have h0 : Pr[ RealG(AB(BB)).main() @ &m :
                RealG.m = RealG.m' /\ !(res \/ RealG.c' = RealG.c) ] = 0%r.
  + by byphoare => //; hoare; conseq E_imp => /#.
  rewrite Pr[mu_split (res \/ RealG.c' = RealG.c)] h0 /=.
  by rewrite Pr[mu_sub] => /#.
smt(ge0_mu).
qed.

local lemma copy_le &m :
  Pr[ RealG(AB(BB)).main() @ &m : RealG.c' = RealG.c ] <= gamma.
proof.
byphoare => //; proc; inline *.
seq 7 : true 1%r gamma 0%r 0%r => //.
case (AB.ok).
+ rcondt 3; first by auto.
  wp; rnd (fun (cd : commitment * openingkey) => cd.`1 = AB.cb).
  by skip => /> &hr _; apply Com_coll.
+ by move=> _; apply gamma_ge0.
rcondf 3; first by auto.
seq 2 : true 1%r gamma 0%r 0%r => //.
wp; rnd (fun (cd : commitment * openingkey) => cd.`1 = RealG.c).
+ by skip => /> &hr; apply Com_coll.
by move=> _; apply gamma_ge0.
qed.

lemma cnm_ap_implies_binding &m :
  Pr[ Bind(BB).main() @ &m : res ]
  <= 2%r * ((Pr[ RealG(AB(BB)).main() @ &m : res ]
             - Pr[ Base(AB(BB)).main() @ &m : res ]) + gamma).
proof.
rewrite AB_base.
have := H_pr &m; have := H_le_E &m; have := E_le &m; have := copy_le &m.
smt().
qed.

end section.

end section Hypotheses.
