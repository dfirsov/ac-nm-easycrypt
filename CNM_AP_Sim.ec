(* Satisfiability: simulation-based non-malleability (in the style of
   Di Crescenzo-Ishai-Ostrovsky) implies CNM-AP.  Hence every scheme
   that is simulation-based non-malleable satisfies the new definition.

   We also show that the second game of Laur-Nyberg (relation fixed at
   init) never exceeds the a-priori baseline.                            *)

pragma Goals:printall.

require import AllCore Distr DBool.
require import CNM_AP.
import Biased.

module type Sim = {
  proc out(pk : pubkey, md : message distr, rel : relation) : message
}.

(* the simulator sees pk, the message distribution and the relation, but
   nothing that depends on the committed message *)
module Ideal(A : AdvCNM, S : Sim) = {
  proc main() : bool = {
    var pk, md, rel, w, m;
    pk         <$ Gen;
    (md, rel)  <@ A.init(pk);
    w          <@ S.out(pk, md, rel);
    m          <$ md;
    return rel m w;
  }
}.

(* Laur-Nyberg's GN1 with the relation chosen at init *)
module LaurG1(A : AdvCNM) = {
  proc main() : bool = {
    var pk, md, rel, m, n, c, d, c', d', m';
    pk         <$ Gen;
    (md, rel)  <@ A.init(pk);
    m          <$ md;
    n          <$ md;
    (c, d)     <$ Commit pk m;
    c'         <@ A.commit(c);
    (d', m')   <@ A.decommit(m, d);
    return Verify pk (m', (c', d')) /\ rel n m' /\ c' <> c;
  }
}.

section.

(* the simulator may read (and write) the adversary's state *)
declare module S <: Sim.
declare module A <: AdvCNM {-S}.

declare axiom A_md_ll : hoare[ A.init : true ==> is_lossless res.`1 ].
declare axiom S_ll : islossless S.out.

local module PS : Oblivious = {
  proc run() : message distr * relation * message = {
    var pk, md, rel, w;
    pk         <$ Gen;
    (md, rel)  <@ A.init(pk);
    w          <@ S.out(pk, md, rel);
    return (md, rel, w);
  }
}.

lemma ideal_le_base &m :
  Pr[ Ideal(A, S).main() @ &m : res ] <= Pr[ Base(A).main() @ &m : res ].
proof.
have h1 : Pr[ Ideal(A, S).main() @ &m : res ] = Pr[ IdealO(PS).main() @ &m : res ].
+ by byequiv => //; proc; inline *; wp; rnd; wp; call (: true); call (: true); auto.
have h2 : Pr[ BaseO(PS).main() @ &m : res ] = Pr[ Base(A).main() @ &m : res ].
+ byequiv => //; proc; inline *; wp; rnd; wp.
  by call{1} S_ll; call (: true); auto.
have h3 := oblivious_le_base PS _ &m.
+ by proc; call (: true); call A_md_ll; auto.
by rewrite h1 -h2.
qed.

(* simulation-based NM for (A, S) with error eps implies CNM-AP for A *)
lemma sim_implies_ap &m (eps : real) :
  Pr[ RealG(A).main() @ &m : res ] <= Pr[ Ideal(A, S).main() @ &m : res ] + eps =>
  Pr[ RealG(A).main() @ &m : res ] - Pr[ Base(A).main() @ &m : res ] <= eps.
proof. by have := ideal_le_base &m; smt(). qed.

end section.

section.

declare module A <: AdvCNM.

declare axiom A_md_ll : hoare[ A.init : true ==> is_lossless res.`1 ].
declare axiom A_commit_ll : islossless A.commit.
declare axiom A_decommit_ll : islossless A.decommit.

local module PL : Oblivious = {
  proc run() : message distr * relation * message = {
    var pk, md, rel, m, c, d, c', d', m';
    pk         <$ Gen;
    (md, rel)  <@ A.init(pk);
    m          <$ md;
    (c, d)     <$ Commit pk m;
    c'         <@ A.commit(c);
    (d', m')   <@ A.decommit(m, d);
    return (md, rel, m');
  }
}.

lemma laur_le_base &m :
  Pr[ LaurG1(A).main() @ &m : res ] <= Pr[ Base(A).main() @ &m : res ].
proof.
have h1 : Pr[ LaurG1(A).main() @ &m : res ] <= Pr[ IdealO(PL).main() @ &m : res ].
+ byequiv => //; proc; inline *.
  swap{1} 4 3; wp; rnd; wp.
  call (: true); call (: true); auto; call (: true); auto => /> /#.
have h2 : Pr[ BaseO(PL).main() @ &m : res ] = Pr[ Base(A).main() @ &m : res ].
+ byequiv => //; proc; inline *; wp; rnd; wp.
  call{1} A_decommit_ll; call{1} A_commit_ll; wp; rnd{1}; rnd{1}.
  seq 2 2 : (md0{1} = md{2} /\ rel0{1} = rel{2} /\ is_lossless md0{1}).
  + conseq (: ={glob A} ==> md0{1} = md{2} /\ rel0{1} = rel{2})
           (: true ==> is_lossless md0) _ => //.
    + by call A_md_ll; auto.
    by call (: true); auto.
  by auto => />; smt(Com_ll).
have h3 := oblivious_le_base PL _ &m.
+ by proc; call (: true); call (: true); auto; call A_md_ll; auto.
by smt().
qed.

end section.
