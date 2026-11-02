(* C5 is about one FIXED, EFFICIENT, black-box simulator.

   The canonical simulator SA(A) runs A on a commitment to a fresh message
   mb <- md (opening it with mb), and outputs the relation A chose at
   commit time together with the message A opens to.
   Its success in the simulation-based ideal game is at least B:

     c5_bl_ideal     : B <= Pr[ Ideal(A, SA(A)) : rel m w ]
     c5_implies_sim  : Real - I - sqrt (I * V) <= Real - B - sqrt (B * V)
                       where I = Pr[ Ideal(A, SA(A)) : rel m w ].

   So C5 security implies simulation-based NM with the canonical simulator,
   up to the abort term sqrt (I * V).  For adversaries that never open
   invalidly (V = 0) it gives Real <= Pr[ Ideal(A, SA(A)) ] + negl: plain
   simulation-based NM with an efficient black-box simulator, with no
   quantifier over simulators.                                              *)

pragma Goals:printall.

require import AllCore Distr DBool StdRing StdOrder RealExp.
require import C5.
import RField RealOrder.

module type Sim = {
  proc out(pk : pubkey, md : message distr) : relation * message
}.

(* the simulator chooses the relation and its output without seeing m *)
module Ideal(A : AdvC5, S : Sim) = {
  var m, w : message
  var rel : relation

  proc main() : unit = {
    var pk, md;
    pk         <$ Gen;
    md         <@ A.init(pk);
    m          <$ md;
    (rel, w)   <@ S.out(pk, md);
  }
}.

(* the canonical simulator: A against a commitment to a fresh message *)
module SA(A : AdvC5) : Sim = {
  var ok : bool

  proc out(pk : pubkey, md : message distr) : relation * message = {
    var mb, c, d, r, c', rel, o, w;
    mb       <$ md;
    (c, d)   <$ Commit pk mb;
    r        <@ A.commit(c);
    c'       <- omap fst r;
    rel      <- (oget r).`2;
    w        <- witness;
    ok       <- false;
    if (c' <> None /\ oget c' <> c) {
      o      <@ A.decommit(mb, d);
      w      <- (oget o).`2;
      ok     <- o <> None /\ Verify pk (w, (oget c', (oget o).`1));
    }
    return (rel, w);
  }
}.

section.

declare module A <: AdvC5 {-G, -Ideal, -SA}.

lemma c5_bl_eq &m :
  Pr[ G(A).main() @ &m : G.v /\ G.rel G.n G.m' ]
  = Pr[ Ideal(A, SA(A)).main() @ &m : SA.ok /\ Ideal.rel Ideal.m Ideal.w ].
proof.
byequiv (_: ={glob A} ==> (G.v /\ G.rel G.n G.m'){1} <=> (SA.ok /\ Ideal.rel Ideal.m Ideal.w){2}) => //.
proc; inline *.
swap{1} 4 -1.
seq 2 2 : (={glob A, pk} /\ G.md{1} = md{2}); 1: by call (: true); auto.
seq 1 1 : (#pre /\ G.n{1} = Ideal.m{2}); 1: by auto.
seq 1 3 : (#pre /\ G.m{1} = mb{2} /\ pk{1} = pk0{2}); 1: by auto.
seq 2 2 : (#pre /\ G.c{1} = c{2} /\ d{1} = d{2} /\ r{1} = r{2}).
+ by call (: true); auto.
sp; if => //.
+ by wp; call (: true); auto.
by auto.
qed.

lemma c5_bl_ideal &m :
  Pr[ G(A).main() @ &m : G.v /\ G.rel G.n G.m' ]
  <= Pr[ Ideal(A, SA(A)).main() @ &m : Ideal.rel Ideal.m Ideal.w ].
proof. by rewrite c5_bl_eq; rewrite Pr[mu_sub] => /#. qed.

lemma c5_implies_sim &m :
     Pr[ G(A).main() @ &m : G.v /\ G.rel G.m G.m' ]
   - Pr[ Ideal(A, SA(A)).main() @ &m : Ideal.rel Ideal.m Ideal.w ]
   - sqrt (Pr[ Ideal(A, SA(A)).main() @ &m : Ideal.rel Ideal.m Ideal.w ]
           * Pr[ G(A).main() @ &m : G.opd /\ !G.v ])
  <= Pr[ G(A).main() @ &m : G.v /\ G.rel G.m G.m' ]
   - Pr[ G(A).main() @ &m : G.v /\ G.rel G.n G.m' ]
   - sqrt (Pr[ G(A).main() @ &m : G.v /\ G.rel G.n G.m' ]
           * Pr[ G(A).main() @ &m : G.opd /\ !G.v ]).
proof.
have hBI := c5_bl_ideal &m.
have ge0B : 0%r <= Pr[ G(A).main() @ &m : G.v /\ G.rel G.n G.m' ] by rewrite Pr[mu_ge0].
have ge0V : 0%r <= Pr[ G(A).main() @ &m : G.opd /\ !G.v ] by rewrite Pr[mu_ge0].
have hs : sqrt (Pr[ G(A).main() @ &m : G.v /\ G.rel G.n G.m' ]
                * Pr[ G(A).main() @ &m : G.opd /\ !G.v ])
       <= sqrt (Pr[ Ideal(A, SA(A)).main() @ &m : Ideal.rel Ideal.m Ideal.w ]
                * Pr[ G(A).main() @ &m : G.opd /\ !G.v ]).
+ rewrite sqrt_mono; [by apply mulr_ge0 | by apply mulr_ge0; smt() |].
  by apply ler_wpmul2r.
smt().
qed.

end section.
