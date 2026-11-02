(* Real-world satisfiability of C5.

   A commitment scheme with an equivocation trapdoor and simulation-sound
   extraction satisfies C5.  The trapdoor algorithms are
     TGen -> (pk, td),  FCom pk td -> (c*, st),  Eq pk td st m -> d,  Ext pk td c'
   and the two assumptions are
     (E1) equivocation: EqReal(D) ~ EqIdeal(D) for any distinguisher D that
          picks m, sees the commitment, and later sees the opening;
     (E2) simulation-sound extraction: in the fake world no adversary opens
          c' <> c* validly to m' <> Ext c' (game SSE).

   Theorem (c5_sat): for every lossless C5 adversary A,
     Real <= B + sqrt ((B + e1 + bad) * (V + e2)) + e0 + e1 + 2 * bad,
   where e_k is the equivocation advantage of the reduction Dk(A) and bad the
   SSE advantage of BA(A).

   Hybrids: H0 = G(A); H1 = fake key, fake commitment, equivocated opening;
   in H1 the events with m' replaced by w = Ext c' differ only on the SSE
   event, and are exactly the ideal-model game of C5_IdealMod, so c5_mod
   applies.                                                                *)

pragma Goals:printall.

require import AllCore Distr DBool StdRing StdOrder RealExp.
require import C5.
require C5_IdealMod.
import RField RealOrder.

type tdk, eqst.

op TGen : (pubkey * tdk) distr.
op FCom : pubkey -> tdk -> (commitment * eqst) distr.
op Eq   : pubkey -> tdk -> eqst -> message -> openingkey distr.
op Ext  : pubkey -> tdk -> commitment -> message.

section Hypotheses.

declare axiom Eq_ll pk td st m : is_lossless (Eq pk td st m).

(* ------------------------------------------------------------------ *)
(* assumptions                                                         *)

module type EqD = {
  proc init(pk : pubkey) : message
  proc mid(c : commitment) : unit
  proc fin(d : openingkey) : bool
}.

module EqReal(D : EqD) = {
  proc main() : bool = {
    var pk, m, c, d, b;
    pk     <$ Gen;
    m      <@ D.init(pk);
    (c, d) <$ Commit pk m;
    D.mid(c);
    b      <@ D.fin(d);
    return b;
  }
}.

module EqIdeal(D : EqD) = {
  proc main() : bool = {
    var pk, td, m, c, st, d, b;
    (pk, td) <$ TGen;
    m        <@ D.init(pk);
    (c, st)  <$ FCom pk td;
    D.mid(c);
    d        <$ Eq pk td st m;
    b        <@ D.fin(d);
    return b;
  }
}.

module type SSB = {
  proc init(pk : pubkey) : message
  proc commit(c : commitment) : commitment option
  proc open(d : openingkey) : (openingkey * message) option
}.

module SSE(B : SSB) = {
  proc main() : bool = {
    var pk, td, m, c, st, c', d, o, b;
    (pk, td) <$ TGen;
    m        <@ B.init(pk);
    (c, st)  <$ FCom pk td;
    c'       <@ B.commit(c);
    d        <$ Eq pk td st m;
    b        <- false;
    if (c' <> None /\ oget c' <> c) {
      o <@ B.open(d);
      b <- o <> None /\ Verify pk ((oget o).`2, (oget c', (oget o).`1))
           /\ (oget o).`2 <> Ext pk td (oget c');
    }
    return b;
  }
}.

(* ------------------------------------------------------------------ *)
(* the ideal-model instance                                            *)

type xst = pubkey * tdk * eqst * commitment * commitment option * message distr * relation.

op sdm (md : message distr) = if is_lossless md then md else dunit witness.

op haltS (x : xst) = !(x.`5 <> None /\ oget x.`5 <> x.`4).
op wS    (x : xst) = Ext x.`1 x.`2 (oget x.`5).
op relS  (x : xst) = x.`7.
op dmS   (x : xst) = sdm x.`6.

clone C5_IdealMod as CI with
  type xt    <- xst,
  type msg   <- message,
  type wt    <- message,
  op   dm    <- dmS,
  op   wx    <- wS,
  op   haltx <- haltS,
  op   relx  <- relS
proof *.
realize dm_ll.
by move=> x; rewrite /dmS /sdm; case: (is_lossless x.`6) => // _; apply dunit_ll.
qed.

(* ------------------------------------------------------------------ *)
(* hybrid H1: fake key, fake commitment, equivocated opening           *)

module H1(A : AdvC5) = {
  var rel : relation
  var m, n, m' : message
  var pk : pubkey
  var td : tdk
  var c : commitment
  var c' : commitment option
  var opd, v : bool

  proc main() : unit = {
    var md, st, d, r, o;
    (pk, td) <$ TGen;
    md       <@ A.init(pk);
    m        <$ md;
    n        <$ md;
    (c, st)  <$ FCom pk td;
    r        <@ A.commit(c);
    c'       <- omap fst r;
    rel      <- (oget r).`2;
    d        <$ Eq pk td st m;
    opd      <- false;
    v        <- false;
    m'       <- witness;
    if (c' <> None /\ oget c' <> c) {
      opd    <- true;
      o      <@ A.decommit(m, d);
      m'     <- (oget o).`2;
      v      <- o <> None /\ Verify pk (m', (oget c', (oget o).`1));
    }
  }
}.

(* reductions *)

module D(A : AdvC5) = {
  var pk : pubkey
  var rel : relation
  var m, n, m' : message
  var c : commitment
  var c' : commitment option
  var opd, v : bool

  proc init(x : pubkey) : message = {
    var md;
    pk <- x;
    md <@ A.init(pk);
    m  <$ md;
    n  <$ md;
    return m;
  }

  proc mid(y : commitment) : unit = {
    var r;
    c   <- y;
    r   <@ A.commit(c);
    c'  <- omap fst r;
    rel <- (oget r).`2;
  }

  proc fin(d : openingkey) : unit = {
    var o;
    opd <- false;
    v   <- false;
    m'  <- witness;
    if (c' <> None /\ oget c' <> c) {
      opd <- true;
      o   <@ A.decommit(m, d);
      m'  <- (oget o).`2;
      v   <- o <> None /\ Verify pk (m', (oget c', (oget o).`1));
    }
  }
}.

module D0(A : AdvC5) : EqD = {
  proc init = D(A).init
  proc mid  = D(A).mid
  proc fin(d : openingkey) : bool = { D(A).fin(d); return D.v /\ D.rel D.m D.m'; }
}.

module D1(A : AdvC5) : EqD = {
  proc init = D(A).init
  proc mid  = D(A).mid
  proc fin(d : openingkey) : bool = { D(A).fin(d); return D.v /\ D.rel D.n D.m'; }
}.

module D2(A : AdvC5) : EqD = {
  proc init = D(A).init
  proc mid  = D(A).mid
  proc fin(d : openingkey) : bool = { D(A).fin(d); return D.opd /\ !D.v; }
}.

module BA(A : AdvC5) : SSB = {
  var m : message

  proc init(pk : pubkey) : message = {
    var md, n;
    md <@ A.init(pk);
    m  <$ md;
    n  <$ md;
    return m;
  }

  proc commit(c : commitment) : commitment option = {
    var r;
    r <@ A.commit(c);
    return omap fst r;
  }

  proc open(d : openingkey) : (openingkey * message) option = {
    var r;
    r <@ A.decommit(m, d);
    return r;
  }
}.

(* the ideal-model adversary: commit phase in the fake world *)
module P(A : AdvC5) : CI.Av.Two = {
  proc ex1() : xst = {
    var pk, td, md, rel, c, st, c', r;
    (pk, td) <$ TGen;
    md       <@ A.init(pk);
    (c, st)  <$ FCom pk td;
    r        <@ A.commit(c);
    c'       <- omap fst r;
    rel      <- (oget r).`2;
    return (pk, td, st, c, c', md, rel);
  }

  proc ex2(x : xst, m : message) : bool = {
    var d, o, b;
    b <- false;
    if (!haltS x) {
      d <$ Eq x.`1 x.`2 x.`3 m;
      o <@ A.decommit(m, d);
      b <- o <> None /\ Verify x.`1 ((oget o).`2, (oget x.`5, (oget o).`1));
    }
    return b;
  }
}.

section.

declare module A <: AdvC5 {-G, -H1, -D, -BA}.

declare axiom A_md_ll : hoare[ A.init : true ==> is_lossless res ].
declare axiom A_dec_ll : islossless A.decommit.

(* H0 = EqReal(Dk(A)) *)
lemma h0_0 &m : Pr[ G(A).main() @ &m : G.v /\ G.rel G.m G.m' ] = Pr[ EqReal(D0(A)).main() @ &m : res ].
proof.
byequiv => //; proc; inline *.
seq 12 19 : (G.v{1} = D.v{2} /\ G.rel{1} = D.rel{2} /\ G.m{1} = D.m{2} /\ G.n{1} = D.n{2}
             /\ G.m'{1} = D.m'{2} /\ G.opd{1} = D.opd{2}); last by wp; skip => />.
seq 11 18 : (={glob A} /\ G.c{1} = D.c{2} /\ G.c'{1} = D.c'{2} /\ G.m{1} = D.m{2}
            /\ G.n{1} = D.n{2} /\ G.rel{1} = D.rel{2} /\ pk{1} = D.pk{2} /\ d{1} = d1{2}
            /\ G.opd{1} = D.opd{2} /\ G.v{1} = D.v{2} /\ G.m'{1} = D.m'{2}).
+ by wp; call (: true); wp; rnd; wp; rnd; rnd; call (: true); wp; rnd; auto.
by if => //; wp; call (: true); auto.
qed.

lemma h0_1 &m : Pr[ G(A).main() @ &m : G.v /\ G.rel G.n G.m' ] = Pr[ EqReal(D1(A)).main() @ &m : res ].
proof.
byequiv => //; proc; inline *.
seq 12 19 : (G.v{1} = D.v{2} /\ G.rel{1} = D.rel{2} /\ G.m{1} = D.m{2} /\ G.n{1} = D.n{2}
             /\ G.m'{1} = D.m'{2} /\ G.opd{1} = D.opd{2}); last by wp; skip => />.
seq 11 18 : (={glob A} /\ G.c{1} = D.c{2} /\ G.c'{1} = D.c'{2} /\ G.m{1} = D.m{2}
            /\ G.n{1} = D.n{2} /\ G.rel{1} = D.rel{2} /\ pk{1} = D.pk{2} /\ d{1} = d1{2}
            /\ G.opd{1} = D.opd{2} /\ G.v{1} = D.v{2} /\ G.m'{1} = D.m'{2}).
+ by wp; call (: true); wp; rnd; wp; rnd; rnd; call (: true); wp; rnd; auto.
by if => //; wp; call (: true); auto.
qed.

lemma h0_2 &m : Pr[ G(A).main() @ &m : G.opd /\ !G.v ] = Pr[ EqReal(D2(A)).main() @ &m : res ].
proof.
byequiv => //; proc; inline *.
seq 12 19 : (G.v{1} = D.v{2} /\ G.rel{1} = D.rel{2} /\ G.m{1} = D.m{2} /\ G.n{1} = D.n{2}
             /\ G.m'{1} = D.m'{2} /\ G.opd{1} = D.opd{2}); last by wp; skip => />.
seq 11 18 : (={glob A} /\ G.c{1} = D.c{2} /\ G.c'{1} = D.c'{2} /\ G.m{1} = D.m{2}
            /\ G.n{1} = D.n{2} /\ G.rel{1} = D.rel{2} /\ pk{1} = D.pk{2} /\ d{1} = d1{2}
            /\ G.opd{1} = D.opd{2} /\ G.v{1} = D.v{2} /\ G.m'{1} = D.m'{2}).
+ by wp; call (: true); wp; rnd; wp; rnd; rnd; call (: true); wp; rnd; auto.
by if => //; wp; call (: true); auto.
qed.

(* H1 = EqIdeal(Dk(A)) *)
lemma h1_0 &m : Pr[ H1(A).main() @ &m : H1.v /\ H1.rel H1.m H1.m' ] = Pr[ EqIdeal(D0(A)).main() @ &m : res ].
proof.
byequiv => //; proc; inline *.
seq 13 20 : (H1.v{1} = D.v{2} /\ H1.rel{1} = D.rel{2} /\ H1.m{1} = D.m{2} /\ H1.n{1} = D.n{2}
             /\ H1.m'{1} = D.m'{2} /\ H1.opd{1} = D.opd{2}); last by wp; skip => />.
seq 12 19 : (={glob A} /\ H1.c{1} = D.c{2} /\ H1.c'{1} = D.c'{2} /\ H1.m{1} = D.m{2}
             /\ H1.n{1} = D.n{2} /\ H1.rel{1} = D.rel{2} /\ H1.pk{1} = D.pk{2} /\ d{1} = d1{2}
             /\ H1.opd{1} = D.opd{2} /\ H1.v{1} = D.v{2} /\ H1.m'{1} = D.m'{2}).
+ by wp; rnd; wp; call (: true); wp; rnd; wp; rnd; rnd; call (: true); wp; rnd; auto.
by if => //; wp; call (: true); auto.
qed.

lemma h1_1 &m : Pr[ H1(A).main() @ &m : H1.v /\ H1.rel H1.n H1.m' ] = Pr[ EqIdeal(D1(A)).main() @ &m : res ].
proof.
byequiv => //; proc; inline *.
seq 13 20 : (H1.v{1} = D.v{2} /\ H1.rel{1} = D.rel{2} /\ H1.m{1} = D.m{2} /\ H1.n{1} = D.n{2}
             /\ H1.m'{1} = D.m'{2} /\ H1.opd{1} = D.opd{2}); last by wp; skip => />.
seq 12 19 : (={glob A} /\ H1.c{1} = D.c{2} /\ H1.c'{1} = D.c'{2} /\ H1.m{1} = D.m{2}
             /\ H1.n{1} = D.n{2} /\ H1.rel{1} = D.rel{2} /\ H1.pk{1} = D.pk{2} /\ d{1} = d1{2}
             /\ H1.opd{1} = D.opd{2} /\ H1.v{1} = D.v{2} /\ H1.m'{1} = D.m'{2}).
+ by wp; rnd; wp; call (: true); wp; rnd; wp; rnd; rnd; call (: true); wp; rnd; auto.
by if => //; wp; call (: true); auto.
qed.

lemma h1_2 &m : Pr[ H1(A).main() @ &m : H1.opd /\ !H1.v ] = Pr[ EqIdeal(D2(A)).main() @ &m : res ].
proof.
byequiv => //; proc; inline *.
seq 13 20 : (H1.v{1} = D.v{2} /\ H1.rel{1} = D.rel{2} /\ H1.m{1} = D.m{2} /\ H1.n{1} = D.n{2}
             /\ H1.m'{1} = D.m'{2} /\ H1.opd{1} = D.opd{2}); last by wp; skip => />.
seq 12 19 : (={glob A} /\ H1.c{1} = D.c{2} /\ H1.c'{1} = D.c'{2} /\ H1.m{1} = D.m{2}
             /\ H1.n{1} = D.n{2} /\ H1.rel{1} = D.rel{2} /\ H1.pk{1} = D.pk{2} /\ d{1} = d1{2}
             /\ H1.opd{1} = D.opd{2} /\ H1.v{1} = D.v{2} /\ H1.m'{1} = D.m'{2}).
+ by wp; rnd; wp; call (: true); wp; rnd; wp; rnd; rnd; call (: true); wp; rnd; auto.
by if => //; wp; call (: true); auto.
qed.

(* the extraction-bad event in H1 is the SSE game *)
lemma h1_bad &m :
    Pr[ H1(A).main() @ &m : H1.v /\ H1.m' <> Ext H1.pk H1.td (oget H1.c') ]
  = Pr[ SSE(BA(A)).main() @ &m : res ].
proof.
byequiv => //; proc; inline *.
seq 12 12 : (={glob A} /\ H1.c{1} = c{2} /\ H1.c'{1} = c'{2} /\ H1.m{1} = BA.m{2}
             /\ H1.pk{1} = pk{2} /\ H1.td{1} = td{2} /\ d{1} = d{2} /\ !H1.v{1} /\ !b{2}).
+ by wp; rnd; wp; call (: true); wp; rnd; wp; rnd; rnd; call (: true); wp; rnd; auto.
by if => //; wp; call (: true); auto => /> /#.
qed.

(* H1 is the ideal-model game of C5_IdealMod, with w = Ext c' *)
lemma h1_g0 : equiv[ H1(A).main ~ CI.Av.G0(P(A)).main : ={glob A} ==>
    H1.v{1} = res{2}.`3 /\ H1.opd{1} = !haltS res{2}.`1 /\ H1.rel{1} = relS res{2}.`1
    /\ H1.m{1} = res{2}.`2 /\ H1.n{1} = res{2}.`4
    /\ Ext H1.pk{1} H1.td{1} (oget H1.c'{1}) = wS res{2}.`1 /\ (H1.v{1} => H1.opd{1}) ].
proof.
proc; inline *.
swap{1} 3 5; swap{1} 3 10.
seq 2 3 : (={glob A} /\ H1.pk{1} = pk{2} /\ H1.td{1} = td{2} /\ md{1} = md{2}
           /\ is_lossless md{1}).
+ seq 1 2 : (={glob A} /\ H1.pk{1} = pk{2} /\ H1.td{1} = td{2}); first by wp; rnd; auto.
  conseq (: ={glob A} /\ H1.pk{1} = pk{2} /\ H1.td{1} = td{2} ==>
            ={glob A} /\ H1.pk{1} = pk{2} /\ H1.td{1} = td{2} /\ md{1} = md{2})
         (: true ==> is_lossless md) _ => //.
  + by call A_md_ll; auto.
  by call (: true); auto.
seq 4 4 : (={glob A} /\ H1.pk{1} = pk{2} /\ H1.td{1} = td{2} /\ md{1} = md{2}
           /\ H1.rel{1} = rel{2} /\ is_lossless md{1}
           /\ H1.c{1} = c{2} /\ H1.c'{1} = c'{2} /\ st{1} = st{2}).
+ by wp; call (: true); rnd; auto.
seq 1 3 : (={glob A} /\ H1.pk{1} = pk{2} /\ H1.td{1} = td{2} /\ md{1} = md{2}
           /\ H1.rel{1} = rel{2} /\ is_lossless md{1}
           /\ H1.c{1} = c{2} /\ H1.c'{1} = c'{2} /\ st{1} = st{2} /\ H1.m{1} = m{2}
           /\ x{2} = (pk, td, st, c, c', md, rel){2}).
+ by rnd; wp; skip => /> &2 hll; rewrite /dmS /sdm /= hll.
seq 5 7 : (={glob A} /\ H1.pk{1} = pk{2} /\ H1.td{1} = td{2} /\ md{1} = md{2}
           /\ H1.rel{1} = rel{2} /\ is_lossless md{1}
           /\ H1.c{1} = c{2} /\ H1.c'{1} = c'{2} /\ H1.m{1} = m{2}
           /\ x{2} = (pk, td, st, c, c', md, rel){2}
           /\ H1.v{1} = b{2} /\ H1.opd{1} = !haltS x{2} /\ (H1.v{1} => H1.opd{1})).
+ case (H1.c'{1} <> None /\ oget H1.c'{1} <> H1.c{1}).
  + rcondt{1} 5; first by auto.
    rcondt{2} 5; first by auto => /> /#.
    by wp; call (: true); wp; rnd; wp; skip => /> /#.
  rcondf{1} 5; first by auto.
  rcondf{2} 5; first by auto => /> /#.
  by wp; rnd{1}; wp; skip => />; smt(Eq_ll).
by rnd; skip => /> &1 hll _; rewrite /dmS /sdm /= hll.
qed.

lemma P_ex2_ll : islossless P(A).ex2.
proof.
proc; sp; if => //.
by wp; call A_dec_ll; rnd; skip => />; smt(Eq_ll).
qed.

lemma h1_ev0 &m :
    Pr[ H1(A).main() @ &m : H1.v /\ H1.rel H1.m (Ext H1.pk H1.td (oget H1.c')) ]
  = Pr[ CI.Av.G0(P(A)).main() @ &m : CI.ev0 res ].
proof. by byequiv h1_g0 => // &1 &2; rewrite /CI.ev0; smt(). qed.

lemma h1_ev1 &m :
    Pr[ H1(A).main() @ &m : H1.v /\ H1.rel H1.n (Ext H1.pk H1.td (oget H1.c')) ]
  = Pr[ CI.Av.G0(P(A)).main() @ &m : CI.ev1 res ].
proof. by byequiv h1_g0 => // &1 &2; rewrite /CI.ev1; smt(). qed.

lemma h1_ev2 &m :
    Pr[ H1(A).main() @ &m : H1.opd /\ !H1.v ] = Pr[ CI.Av.G0(P(A)).main() @ &m : CI.ev2 res ].
proof. by byequiv h1_g0 => // &1 &2; rewrite /CI.ev2; smt(). qed.

lemma c5_sat &m :
  let e0  = `| Pr[ EqReal(D0(A)).main() @ &m : res ] - Pr[ EqIdeal(D0(A)).main() @ &m : res ] | in
  let e1  = `| Pr[ EqReal(D1(A)).main() @ &m : res ] - Pr[ EqIdeal(D1(A)).main() @ &m : res ] | in
  let e2  = `| Pr[ EqReal(D2(A)).main() @ &m : res ] - Pr[ EqIdeal(D2(A)).main() @ &m : res ] | in
  let bad = Pr[ SSE(BA(A)).main() @ &m : res ] in
  let rl  = Pr[ G(A).main() @ &m : G.v /\ G.rel G.m G.m' ] in
  let bl  = Pr[ G(A).main() @ &m : G.v /\ G.rel G.n G.m' ] in
  let vl  = Pr[ G(A).main() @ &m : G.opd /\ !G.v ] in
  rl <= bl + sqrt ((bl + e1 + bad) * (vl + e2)) + e0 + e1 + 2%r * bad.
proof.
move=> e0 e1 e2 bad rl bl vl.
have hr := h0_0 &m; have hb := h0_1 &m; have hv := h0_2 &m.
have ir := h1_0 &m; have ib := h1_1 &m; have iv := h1_2 &m.
have hbad := h1_bad &m.
(* replacing m' by Ext c' in H1 costs the SSE event *)
have s0 : Pr[ H1(A).main() @ &m : H1.v /\ H1.rel H1.m H1.m' ] <= Pr[ H1(A).main() @ &m : H1.v /\ H1.rel H1.m (Ext H1.pk H1.td (oget H1.c')) ] + Pr[ H1(A).main() @ &m : H1.v /\ H1.m' <> Ext H1.pk H1.td (oget H1.c') ].
+ have h : Pr[ H1(A).main() @ &m : H1.v /\ H1.rel H1.m H1.m' ] <= Pr[ H1(A).main() @ &m : (H1.v /\ H1.rel H1.m (Ext H1.pk H1.td (oget H1.c'))) \/ (H1.v /\ H1.m' <> Ext H1.pk H1.td (oget H1.c')) ] by rewrite Pr[mu_sub] => // &h /#.
  have : Pr[ H1(A).main() @ &m : (H1.v /\ H1.rel H1.m (Ext H1.pk H1.td (oget H1.c'))) \/ (H1.v /\ H1.m' <> Ext H1.pk H1.td (oget H1.c')) ] = Pr[ H1(A).main() @ &m : H1.v /\ H1.rel H1.m (Ext H1.pk H1.td (oget H1.c')) ] + Pr[ H1(A).main() @ &m : H1.v /\ H1.m' <> Ext H1.pk H1.td (oget H1.c') ] - Pr[ H1(A).main() @ &m : (H1.v /\ H1.rel H1.m (Ext H1.pk H1.td (oget H1.c'))) /\ (H1.v /\ H1.m' <> Ext H1.pk H1.td (oget H1.c')) ] by rewrite Pr[mu_or].
  have : 0%r <= Pr[ H1(A).main() @ &m : (H1.v /\ H1.rel H1.m (Ext H1.pk H1.td (oget H1.c'))) /\ (H1.v /\ H1.m' <> Ext H1.pk H1.td (oget H1.c')) ] by rewrite Pr[mu_ge0].
  smt().
have s1 : Pr[ H1(A).main() @ &m : H1.v /\ H1.rel H1.n (Ext H1.pk H1.td (oget H1.c')) ] <= Pr[ H1(A).main() @ &m : H1.v /\ H1.rel H1.n H1.m' ] + Pr[ H1(A).main() @ &m : H1.v /\ H1.m' <> Ext H1.pk H1.td (oget H1.c') ].
+ have h : Pr[ H1(A).main() @ &m : H1.v /\ H1.rel H1.n (Ext H1.pk H1.td (oget H1.c')) ] <= Pr[ H1(A).main() @ &m : (H1.v /\ H1.rel H1.n H1.m') \/ (H1.v /\ H1.m' <> Ext H1.pk H1.td (oget H1.c')) ] by rewrite Pr[mu_sub] => // &h /#.
  have : Pr[ H1(A).main() @ &m : (H1.v /\ H1.rel H1.n H1.m') \/ (H1.v /\ H1.m' <> Ext H1.pk H1.td (oget H1.c')) ] = Pr[ H1(A).main() @ &m : H1.v /\ H1.rel H1.n H1.m' ] + Pr[ H1(A).main() @ &m : H1.v /\ H1.m' <> Ext H1.pk H1.td (oget H1.c') ] - Pr[ H1(A).main() @ &m : (H1.v /\ H1.rel H1.n H1.m') /\ (H1.v /\ H1.m' <> Ext H1.pk H1.td (oget H1.c')) ] by rewrite Pr[mu_or].
  have : 0%r <= Pr[ H1(A).main() @ &m : (H1.v /\ H1.rel H1.n H1.m') /\ (H1.v /\ H1.m' <> Ext H1.pk H1.td (oget H1.c')) ] by rewrite Pr[mu_ge0].
  smt().
(* the ideal-model theorem *)
have c5 := CI.c5_mod (P(A)) P_ex2_ll &m.
rewrite -(h1_ev0 &m) -(h1_ev1 &m) -(h1_ev2 &m) in c5.
have ge0B2 : 0%r <= Pr[ H1(A).main() @ &m : H1.v /\ H1.rel H1.n (Ext H1.pk H1.td (oget H1.c')) ] by rewrite Pr[mu_ge0].
have ge0V2 : 0%r <= Pr[ H1(A).main() @ &m : H1.opd /\ !H1.v ] by rewrite Pr[mu_ge0].
have hB2 : Pr[ H1(A).main() @ &m : H1.v /\ H1.rel H1.n (Ext H1.pk H1.td (oget H1.c')) ] <= bl + e1 + bad.
+ by rewrite /bl /e1 /bad; smt().
have hV2 : Pr[ H1(A).main() @ &m : H1.opd /\ !H1.v ] <= vl + e2.
+ by rewrite /vl /e2; smt().
have hsq : sqrt (Pr[ H1(A).main() @ &m : H1.v /\ H1.rel H1.n (Ext H1.pk H1.td (oget H1.c')) ]
                 * Pr[ H1(A).main() @ &m : H1.opd /\ !H1.v ])
        <= sqrt ((bl + e1 + bad) * (vl + e2)).
+ rewrite sqrt_mono; [by apply mulr_ge0 | smt(mulr_ge0) |].
  by apply ler_pmul.
by rewrite /rl /e0 /bad; smt().
qed.

end section.

end section Hypotheses.
