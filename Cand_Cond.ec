(* Candidate C2: Laur-Nyberg GN1 conditioned on a valid opening,
     Adv = Pr[ RealG ] - Pr[ G1 : win ] / Pr[ G1 : valid ].
   It is unsatisfiable: the "dilution" adversary AD never mauls, yet
     Pr[ RealG ] >= 1/4 - gamma,  Pr[ G1 : win ] <= 1/8,  Pr[ G1 : valid ] >= 3/4
   against EVERY correct scheme, so Adv >= 1/12 - gamma.
   AD commits to m1 or to a losing value m3; it opens m1 only if it sees m1,
   and always opens m3.  Aborting reweights the conditioned baseline towards
   the losing value.                                                       *)

pragma Goals:printall.

require import AllCore Distr DBool List StdRing StdOrder.
require import CNM_AP.
import RField RealOrder.

op m1, m2, m3 : message.

section Hypotheses.

declare axiom m12 : m1 <> m2.
declare axiom m13 : m1 <> m3.
declare axiom m23 : m2 <> m3.

op gamma : real.

declare axiom Com_correct pk m c d :
  pk \in Gen => (c, d) \in Commit pk m => Verify pk (m, (c, d)).

declare axiom Com_coll pk m c :
  mu (Commit pk m) (fun (cd : commitment * openingkey) => cd.`1 = c) <= gamma.

lemma duni12_m1 : mu (duniform [m1; m2]) (pred1 m1) = 1%r / 2%r.
proof. rewrite duniform1E /=; smt(m12). qed.

lemma duni12_ll : is_lossless (duniform [m1; m2]).
proof. by apply duniform_ll. qed.

(* GN1 of Laur-Nyberg, returning (valid, win) *)
module G1(A : AdvCNM) = {
  var m, n : message

  proc main() : bool * bool = {
    var pk, md, rel, c, d, c', d', m', v;
    pk         <$ Gen;
    (md, rel)  <@ A.init(pk);
    m          <$ md;
    n          <$ md;
    (c, d)     <$ Commit pk m;
    c'         <@ A.commit(c);
    (d', m')   <@ A.decommit(m, d);
    v          <- Verify pk (m', (c', d'));
    return (v, v /\ rel n m' /\ c' <> c);
  }
}.

module AD : AdvCNM = {
  var pk : pubkey
  var b : bool
  var c' : commitment
  var d' : openingkey

  proc init(x : pubkey) : message distr * relation = {
    pk <- x;
    return (duniform [m1; m2], fun (n v : message) => n = v);
  }

  proc commit(y : commitment) : commitment = {
    b         <$ {0,1};
    (c', d')  <$ Commit pk (if b then m1 else m3);
    return c';
  }

  proc decommit(m : message, d : openingkey) : openingkey * message = {
    return if !b then (d', m3) else if m = m1 then (d', m1) else (d', m3);
  }
}.


(* ------------------------------------------------------------------ *)
(* the real game                                                       *)

module S2 = {
  proc main() : bool = {
    var m, b;
    m <$ duniform [m1; m2];
    b <$ {0,1};
    return b /\ m = m1;
  }
}.

lemma S2_pr &m : Pr[ S2.main() @ &m : res ] = 1%r / 4%r.
proof.
byphoare => //; proc.
seq 1 : (m = m1) (1%r / 2%r) (1%r / 2%r) (1%r / 2%r) 0%r => //.
+ by rnd (pred1 m1); skip => />; rewrite duni12_m1.
+ by rnd (pred1 true); skip => />; rewrite dbool1E /=; smt().
by hoare; rnd; skip => /#.
qed.

lemma real_bm &m : Pr[ RealG(AD).main() @ &m : AD.b /\ RealG.m = m1 ] = 1%r / 4%r.
proof.
rewrite -(S2_pr &m); byequiv => //; proc; inline *.
wp; rnd{1}; rnd; wp; rnd{1}; rnd; wp; rnd{1}; skip => />.
smt(Gen_ll Com_ll).
qed.

lemma real_copy &m : Pr[ RealG(AD).main() @ &m : AD.c' = RealG.c ] <= gamma.
proof.
byphoare => //; proc; inline *.
seq 8 : true 1%r gamma 0%r 0%r => //.
+ wp; rnd (fun (cd : commitment * openingkey) => cd.`1 = RealG.c).
  by skip => /> &hr; apply Com_coll.
by move=> _; have := Com_coll witness witness witness; smt(ge0_mu).
qed.

lemma real_lb &m : 1%r / 4%r - gamma <= Pr[ RealG(AD).main() @ &m : res ].
proof.
have h1 : Pr[ RealG(AD).main() @ &m : AD.b /\ RealG.m = m1 ]
       <= Pr[ RealG(AD).main() @ &m : res \/ AD.c' = RealG.c ].
+ byequiv (_: ={glob AD} ==> (AD.b /\ RealG.m = m1){1} => (res \/ AD.c' = RealG.c){2}) => //.
  proc; inline *; auto => /> pk pk_in m _ [c d] _ b _ [c' d'] cd_in.
  smt(Com_correct).
have h2 : Pr[ RealG(AD).main() @ &m : res \/ AD.c' = RealG.c ]
       <= Pr[ RealG(AD).main() @ &m : res ] + Pr[ RealG(AD).main() @ &m : AD.c' = RealG.c ].
+ rewrite Pr[mu_or].
  have : 0%r <= Pr[ RealG(AD).main() @ &m : res /\ AD.c' = RealG.c ] by rewrite Pr[mu_ge0].
  smt().
have := real_bm &m; have := real_copy &m.
smt().
qed.


(* ------------------------------------------------------------------ *)
(* GN1                                                                 *)

module S3 = {
  proc main() : bool = {
    var m, n, b;
    m <$ duniform [m1; m2];
    n <$ duniform [m1; m2];
    b <$ {0,1};
    return b /\ m = m1 /\ n = m1;
  }
}.

lemma S3_pr &m : Pr[ S3.main() @ &m : res ] = 1%r / 8%r.
proof.
byphoare => //; proc.
seq 2 : (m = m1 /\ n = m1) (1%r / 4%r) (1%r / 2%r) (3%r / 4%r) 0%r => //.
+ seq 1 : (m = m1) (1%r / 2%r) (1%r / 2%r) (1%r / 2%r) 0%r => //.
  + by rnd (pred1 m1); skip => />; rewrite duni12_m1.
  + by rnd (pred1 m1); skip => />; rewrite duni12_m1.
  by hoare; rnd; skip => /#.
+ by rnd (pred1 true); skip => />; rewrite dbool1E /=; smt().
by hoare; rnd; skip => /#.
qed.

lemma g1_win &m : Pr[ G1(AD).main() @ &m : res.`2 ] <= 1%r / 8%r.
proof.
rewrite -(S3_pr &m); byequiv => //; proc; inline *.
wp; rnd{1}; rnd; wp; rnd{1}; rnd; rnd; wp; rnd{1}; skip => />.
split; first by apply Gen_ll.
move=> _ pk _ m; rewrite supp_duniform /= => hm n; rewrite supp_duniform /= => hn.
split; first by apply Com_ll.
move=> _ cd _ b _; split; first by apply Com_ll.
move=> _ cd2 _; case: b => /= hb; smt(m13 m23).
qed.

module S4 = {
  proc main() : bool = {
    var m, b;
    m <$ duniform [m1; m2];
    b <$ {0,1};
    return !b \/ m = m1;
  }
}.

lemma S4_pr &m : Pr[ S4.main() @ &m : res ] = 3%r / 4%r.
proof.
byphoare => //; proc.
seq 1 : (m = m1) (1%r / 2%r) 1%r (1%r / 2%r) (1%r / 2%r) => //.
+ by rnd (pred1 m1); skip => />; rewrite duni12_m1.
+ by rnd predT; skip => />; rewrite dbool_ll.
+ by rnd (predC (pred1 m1)); skip => />; rewrite mu_not duni12_m1 duni12_ll; smt().
by rnd (pred1 false); skip => />; rewrite dbool1E /=; smt().
qed.

lemma g1_valid &m : 3%r / 4%r <= Pr[ G1(AD).main() @ &m : res.`1 ].
proof.
rewrite -(S4_pr &m); byequiv => //; proc; inline *.
wp; rnd{2}; rnd; wp; rnd{2}; rnd{2}; rnd; wp; rnd{2}; skip => />.
split; first by apply Gen_ll.
move=> _ pk pk_in m _; split; first by apply duni12_ll.
move=> _ n _; split; first by apply Com_ll.
move=> _ cd _ b _; split; first by apply Com_ll.
move=> _ cd2 cd2_in; case: b cd2_in => /= cd2_in.
+ by move=> -> /=; have := Com_correct pk m1 cd2.`1 cd2.`2 pk_in; rewrite -pairS; apply.
by have := Com_correct pk m3 cd2.`1 cd2.`2 pk_in; rewrite -pairS; apply.
qed.


(* ------------------------------------------------------------------ *)
(* the conditioned baseline is beaten by 1/12 - gamma                  *)

lemma cond_unsat &m :
  1%r / 12%r - gamma
  <= Pr[ RealG(AD).main() @ &m : res ]
   - Pr[ G1(AD).main() @ &m : res.`2 ] / Pr[ G1(AD).main() @ &m : res.`1 ].
proof.
have h1 := real_lb &m; have h2 := g1_win &m; have h3 := g1_valid &m.
have : Pr[ G1(AD).main() @ &m : res.`2 ] / Pr[ G1(AD).main() @ &m : res.`1 ] <= 1%r / 6%r.
+ rewrite ler_pdivr_mulr; first by smt().
  smt().
smt().
qed.

end section Hypotheses.
