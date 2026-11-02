(* C5 implies binding:  Pr[ Bind(Bd) ] <= 2 * Adv_C5(AB(Bd)) + gamma.

   AB(Bd) runs the binding adversary in init, picks md = uniform {m0, m1},
   R = equality, commits to the double-openable commitment and opens it to
   whatever message it sees.  It never opens invalidly (V = 0), and by the
   symmetry n <-> swap(n) we get Real = 2 B.                               *)

pragma Goals:printall.

require import AllCore Distr DBool List StdRing StdOrder RealExp.
require import C5.
import RField RealOrder.

op gamma : real.

section Hypotheses.

declare axiom Com_coll pk m c :
  mu (Commit pk m) (fun (cd : commitment * openingkey) => cd.`1 = c) <= gamma.

lemma Com_coll_and pk m c (b : bool) :
  mu (Commit pk m) (fun (cd : commitment * openingkey) => b /\ cd.`1 = c) <= gamma.
proof.
apply (ler_trans (mu (Commit pk m) (fun (cd : commitment * openingkey) => cd.`1 = c))).
+ by apply mu_sub => /#.
by apply Com_coll.
qed.

module type AdvBind = {
  proc find(pk : pubkey) : commitment * message * openingkey * message * openingkey
}.

module Bind(Bd : AdvBind) = {
  proc main() : bool = {
    var pk, c, m0, d0, m1, d1;
    pk                   <$ Gen;
    (c, m0, d0, m1, d1)  <@ Bd.find(pk);
    return m0 <> m1 /\ Verify pk (m0, (c, d0)) /\ Verify pk (m1, (c, d1));
  }
}.

module AB(Bd : AdvBind) : AdvC5 = {
  var cs : commitment
  var m0, m1 : message
  var d0, d1 : openingkey
  var ok : bool

  proc init(pk : pubkey) : message distr = {
    (cs, m0, d0, m1, d1) <@ Bd.find(pk);
    ok <- m0 <> m1 /\ Verify pk (m0, (cs, d0)) /\ Verify pk (m1, (cs, d1));
    return duniform [m0; m1];
  }

  proc commit(c : commitment) : (commitment * relation) option = {
    return if ok then Some (cs, fun (n v : message) => n = v) else None;
  }

  proc decommit(m : message, d : openingkey) : (openingkey * message) option = {
    return Some (if m = m0 then (d0, m0) else (d1, m1));
  }
}.

section.

declare module Bd <: AdvBind {-AB, -G}.

declare axiom Bd_ll : islossless Bd.find.

lemma ab_v0 &m : Pr[ G(AB(Bd)).main() @ &m : G.opd /\ !G.v ] = 0%r.
proof.
byphoare => //; hoare; proc; inline *.
auto; call (: true); auto => /> pk _ [cs m0 d0 m1 d1] /= m.
rewrite supp_duniform /= => hm n _ [c d] _ /=.
case: (m0 <> m1 /\ Verify pk (m0, (cs, d0)) /\ Verify pk (m1, (cs, d1))) => //= [[_ [h0 h1]]] _.
by case: (m = m0) => /#.
qed.

lemma ab_sym &m :
    Pr[ G(AB(Bd)).main() @ &m : G.v /\ G.rel G.n G.m' ]
  = Pr[ G(AB(Bd)).main() @ &m : G.v /\ !G.rel G.n G.m' ].
proof.
byequiv => //; proc; inline *.
seq 6 6 : (={glob Bd, glob AB, G.m, G.md, pk} /\ G.md{1} = duniform [AB.m0{1}; AB.m1{1}]
           /\ G.m{1} \in G.md{1}
           /\ (AB.ok{1} => AB.m0{1} <> AB.m1{1})).
+ by rnd; wp; call (: true); auto => /> /#.
swap 1 9.
seq 9 9 : (={G.v, G.m', G.m, G.md, G.rel} /\ G.md{1} = duniform [AB.m0{1}; AB.m1{1}]
           /\ (G.m{1} = AB.m0{1} \/ G.m{1} = AB.m1{1})
           /\ (G.v{1} => AB.m0{1} <> AB.m1{1} /\ G.m'{1} = G.m{1}
                       /\ G.rel{1} = (fun (n v : message) => n = v))
           /\ AB.m0{1} = AB.m0{2} /\ AB.m1{1} = AB.m1{2}).
+ auto => /> &2 hm hok [c d] _.
  move: hm; rewrite supp_duniform /=; smt().
rnd (fun n => if n = AB.m0{1} then AB.m1{1} else AB.m0{1}); skip => /> &2 hm hv.
split.
+ move=> n; rewrite supp_duniform /= => -[|] ->; smt().
move=> _; split.
+ move=> n; rewrite supp_duniform /= => hn; rewrite !duniform1E /=; smt().
move=> _ n; rewrite supp_duniform /= => hn; split.
+ by rewrite supp_duniform /=; smt().
move=> _; smt().
qed.

lemma ab_real &m :
  Pr[ Bind(Bd).main() @ &m : res ] - gamma <= Pr[ G(AB(Bd)).main() @ &m : G.v /\ G.rel G.m G.m' ].
proof.
have h1 : Pr[ Bind(Bd).main() @ &m : res ]
       <= Pr[ G(AB(Bd)).main() @ &m : (G.v /\ G.rel G.m G.m') \/ (AB.ok /\ AB.cs = G.c) ].
+ byequiv => //; proc; inline *.
  wp; rnd{2}; rnd{2}; rnd{2}; wp; call (: true); auto => /> pk _ [cs m0 d0 m1 d1] /=.
  split; first by apply duniform_ll.
  move=> _ m; rewrite supp_duniform /= => hm n _; split; first by apply Com_ll.
  move=> _ [c d] _ /=; smt().
have h2 : Pr[ G(AB(Bd)).main() @ &m : AB.ok /\ AB.cs = G.c ] <= gamma.
+ byphoare => //; proc; inline *.
  seq 7 : true 1%r gamma 0%r 0%r => //.
  seq 1 : (AB.ok /\ AB.cs = G.c) gamma 1%r 1%r 0%r => //.
  + rnd (fun (cd : commitment * openingkey) => AB.ok /\ cd.`1 = AB.cs); auto => />.
    by move=> &hr; apply Com_coll_and.
  + by have := Com_coll witness witness witness; smt(ge0_mu).
  by hoare; auto.
have h3 : Pr[ G(AB(Bd)).main() @ &m : (G.v /\ G.rel G.m G.m') \/ (AB.ok /\ AB.cs = G.c) ]
       <= Pr[ G(AB(Bd)).main() @ &m : G.v /\ G.rel G.m G.m' ]
        + Pr[ G(AB(Bd)).main() @ &m : AB.ok /\ AB.cs = G.c ].
+ rewrite Pr[mu_or].
  have : 0%r <= Pr[ G(AB(Bd)).main() @ &m : (G.v /\ G.rel G.m G.m') /\ (AB.ok /\ AB.cs = G.c) ]
    by rewrite Pr[mu_ge0].
  smt().
smt().
qed.

lemma ab_real_split &m :
    Pr[ G(AB(Bd)).main() @ &m : G.v /\ G.rel G.m G.m' ]
  = Pr[ G(AB(Bd)).main() @ &m : G.v /\ G.rel G.n G.m' ]
  + Pr[ G(AB(Bd)).main() @ &m : G.v /\ !G.rel G.n G.m' ].
proof.
have -> : Pr[ G(AB(Bd)).main() @ &m : G.v /\ G.rel G.m G.m' ] = Pr[ G(AB(Bd)).main() @ &m : G.v ].
+ byequiv => //; proc; inline *.
  wp; rnd; rnd; rnd; wp; call (: true); auto => /> pk _ [cs m0 d0 m1 d1] /= m.
  rewrite supp_duniform /= => hm n _ [c d] _ /=; smt().
by rewrite Pr[mu_split (G.rel G.n G.m')]; congr; rewrite Pr[mu_eq] /#.
qed.

lemma c5_implies_binding &m :
  Pr[ Bind(Bd).main() @ &m : res ]
  <= 2%r * (Pr[ G(AB(Bd)).main() @ &m : G.v /\ G.rel G.m G.m' ]
          - Pr[ G(AB(Bd)).main() @ &m : G.v /\ G.rel G.n G.m' ]
          - sqrt (Pr[ G(AB(Bd)).main() @ &m : G.v /\ G.rel G.n G.m' ]
                * Pr[ G(AB(Bd)).main() @ &m : G.opd /\ !G.v ]))
     + gamma.
proof.
rewrite ab_v0 mulr0 sqrt0 /=.
have := ab_real &m; have := ab_real_split &m; have := ab_sym &m.
smt().
qed.

end section.

end section Hypotheses.
