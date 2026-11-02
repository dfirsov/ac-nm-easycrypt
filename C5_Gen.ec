(* AC-NM (C5) for a generic shape of the adversary's output, and the
   filtering lemma for it.

   The challenge is a single commitment c to m <- md, as in C5.ec.  The
   adversary outputs a commitment of an abstract type ocom together with
   the relation, and later an opening (oopen) of an opened value (oval):
     fresh c c'                  -- the output is not a trivial copy of c,
     Vfy pk (m', (c', d'))       -- the opening is valid.
   For a single commitment (C5.ec): ocom = commitment, oval = message,
   fresh c c' = c' <> c, Vfy = Verify.  For a vector of commitments
   (C5_Vector.ec): lists, fresh = every component differs from c, and Vfy =
   every component verifies (all-or-nothing validity, as in Laur-Pasini).

   c5_filter is the proof of C5_Filter.ec, unchanged except for the types:
   it never inspects the shape of c' or m'.                               *)

pragma Goals:printall.

require import AllCore Distr DBool StdRing StdOrder RealExp.
import RField RealOrder.

type pubkey, message, commitment, openingkey.
type ocom, oopen, oval.

type relation = message -> oval -> bool.

op Gen : pubkey distr.
op Commit (pk : pubkey) (m : message) : (commitment * openingkey) distr.
op Vfy : pubkey -> oval * (ocom * oopen) -> bool.
op fresh : commitment -> ocom -> bool.

module type AdvG = {
  proc init(pk : pubkey) : message distr
  proc commit(c : commitment) : (ocom * relation) option
  proc decommit(m : message, d : openingkey) : (oopen * oval) option
}.

module G(A : AdvG) = {
  var md : message distr
  var rel : relation
  var m, n : message
  var m' : oval
  var c : commitment
  var c' : ocom option
  var opd, v : bool

  proc main() : unit = {
    var pk, d, r, o;
    pk     <$ Gen;
    md     <@ A.init(pk);
    m      <$ md;
    n      <$ md;
    (c, d) <$ Commit pk m;
    r      <@ A.commit(c);
    c'     <- omap fst r;
    rel    <- (oget r).`2;
    opd    <- false;
    v      <- false;
    m'     <- witness;
    if (c' <> None /\ fresh c (oget c')) {
      opd  <- true;
      o    <@ A.decommit(m, d);
      m'   <- (oget o).`2;
      v    <- o <> None /\ Vfy pk (m', (oget c', (oget o).`1));
    }
  }
}.


(* ------------------------------------------------------------------ *)
(* the arithmetic                                                      *)

lemma amgm2 (a b : real) : 0%r <= a => 0%r <= b => 2%r * sqrt (a * b) <= a + b.
proof.
move=> ge0a ge0b.
have h : sqrt (a * b) <= sqrt (((a + b) / 2%r) ^ 2).
+ rewrite sqrt_mono; first by smt().
  + by rewrite expr2; smt(ge0_sqr).
  have h0 := ge0_sqr (a - b); rewrite expr2 in h0.
  have he : (a + b) / 2%r * ((a + b) / 2%r) - a * b = (a - b) * (a - b) / 4%r by field.
  by rewrite expr2 /#.
by move: h; rewrite sqrtsq_ge0 /#.
qed.

lemma filter_arith (r b vv p q adv : real) :
  0%r <= q => q < 1%r => 0%r <= r => 0%r <= b => 0%r <= vv =>
  b <= q * r => vv <= p =>
  adv = r - b - sqrt (b * vv) =>
  r <= q * p / ((1%r - q) * (1%r - q)) + 2%r * adv / (1%r - q).
proof.
move=> ge0q lt1q ge0r ge0b ge0v hb hv ->.
have ge0p : 0%r <= p by smt().
have s1 : sqrt (b * vv) <= sqrt (q * r * p).
+ rewrite sqrt_mono; first 2 by smt().
  by apply ler_pmul => // /#.
have s2 : 2%r * sqrt ((q * p / (1%r - q)) * ((1%r - q) * r))
          <= q * p / (1%r - q) + (1%r - q) * r.
+ apply amgm2; last by smt().
  by apply divr_ge0 => /#.
have he : (q * p / (1%r - q)) * ((1%r - q) * r) = q * r * p.
+ by field; smt().
move: s2; rewrite he => s2.
(* r - adv <= q r + sqrt (q r p) <= q r + (q p / (1 - q) + (1 - q) r) / 2 *)
pose X := q * p / (1%r - q).
have s3 : sqrt (b * vv) <= X / 2%r + (1%r - q) * r / 2%r by smt().
have key : (1%r - q) * r / 2%r <= (r - b - sqrt (b * vv)) + X / 2%r by smt().
have pos : 0%r < 1%r - q by smt().
pose Z := r - b - sqrt (b * vv).
have k2 : (1%r - q) * r <= 2%r * Z + X by smt().
have k3 : r <= (2%r * Z + X) / (1%r - q) by rewrite ler_pdivl_mulr // mulrC.
have -> : q * p / ((1%r - q) * (1%r - q)) + 2%r * Z / (1%r - q) = (2%r * Z + X) / (1%r - q).
+ rewrite /X; field; last by smt().
  have := mulr_gt0 _ _ pos pos.
  by rewrite expr2 => /#.
done.
qed.


(* ------------------------------------------------------------------ *)
(* the filtered adversary                                              *)

module Filt(A : AdvG) = {
  var r : relation

  proc init(pk : pubkey) : message distr = {
    var md;
    md <@ A.init(pk);
    return md;
  }

  proc commit(c : commitment) : (ocom * relation) option = {
    var o;
    o <@ A.commit(c);
    r <- (oget o).`2;
    return o;
  }

  proc decommit(m : message, d : openingkey) : (oopen * oval) option = {
    var o;
    o <@ A.decommit(m, d);
    return (if o <> None /\ r m (oget o).`2 then o else None);
  }
}.

(* G with the (unused) sample n moved to the very end *)
module GN(A : AdvG) = {
  proc pre() : unit = {
    var pk, d, r, o;
    pk       <$ Gen;
    G.md     <@ A.init(pk);
    G.m      <$ G.md;
    (G.c, d) <$ Commit pk G.m;
    r        <@ A.commit(G.c);
    G.c'     <- omap fst r;
    G.rel    <- (oget r).`2;
    G.opd    <- false;
    G.v      <- false;
    G.m'     <- witness;
    if (G.c' <> None /\ fresh G.c (oget G.c')) {
      G.opd  <- true;
      o      <@ A.decommit(G.m, d);
      G.m'   <- (oget o).`2;
      G.v    <- o <> None /\ Vfy pk (G.m', (oget G.c', (oget o).`1));
    }
  }

  proc main() : unit = {
    pre();
    G.n <$ G.md;
  }
}.

op sparse (q : real) (md : message distr) (rel : relation) =
  forall y, mu md (fun x => rel x y) <= q.

section.

declare module A <: AdvG {-G, -Filt}.

declare axiom A_md_ll : hoare[ A.init : true ==> is_lossless res ].

local equiv e_filt : G(A).main ~ G(Filt(A)).main :
  ={glob A} ==>
  ={G.md, G.rel, G.opd, G.m} /\
  ((G.v /\ G.rel G.m G.m'){1} <=> G.v{2}) /\
  (G.v{2} => G.rel{2} G.m{2} G.m'{2} /\ G.opd{2}).
proof.
proc; inline Filt(A).init Filt(A).commit Filt(A).decommit.
seq 11 16 : (={glob A, pk, d, G.md, G.rel, G.m, G.c, G.c', G.opd, G.v} /\
             Filt.r{2} = G.rel{2} /\ !G.v{2} /\ !G.opd{2}).
+ by wp; call (: true); auto; call (: true); auto.
if => //.
+ by wp; call (: true); auto => /> /#.
qed.

local equiv e_gn : G(Filt(A)).main ~ GN(Filt(A)).main :
  ={glob A} ==> ={G.v, G.opd, G.md, G.rel, G.m, G.n, G.m'}.
proof.
proc; inline *.
swap{1} 6 11.
sim.
qed.

local lemma g_md_ll : hoare[ G(A).main : true ==> is_lossless G.md ].
proof.
proc; seq 2 : (is_lossless G.md); first by call A_md_ll; auto.
seq 9 : (is_lossless G.md); first by wp; call (: true); auto.
by if; [wp; call (: true); auto | auto].
qed.

local lemma gn_main_pre (q : real) &m :
  Pr[ GN(Filt(A)).main() @ &m : G.v /\ G.opd /\ sparse q G.md G.rel /\ is_lossless G.md ]
  = Pr[ GN(Filt(A)).pre() @ &m : G.v /\ G.opd /\ sparse q G.md G.rel /\ is_lossless G.md ].
proof.
byphoare (_ : (glob A) = (glob A){m} ==> G.v /\ G.opd /\ sparse q G.md G.rel /\ is_lossless G.md) => //.
proc.
seq 1 : (G.v /\ G.opd /\ sparse q G.md G.rel /\ is_lossless G.md)
        (Pr[ GN(Filt(A)).pre() @ &m : G.v /\ G.opd /\ sparse q G.md G.rel /\ is_lossless G.md ]) 1%r
        _ 0%r => //.
+ call (_ : (glob A) = (glob A){m} ==> G.v /\ G.opd /\ sparse q G.md G.rel /\ is_lossless G.md).
  + bypr => &m0; split; first by rewrite Pr[mu_ge0].
    move=> h; byequiv (_ : ={glob A} ==> ={G.v, G.opd, G.md, G.rel}) => //.
    by proc; inline *; sim.
  by auto.
+ by rnd; skip => /> &hr _ _ _ hll; apply hll.
by hoare; rnd; skip => />.
qed.

local lemma gn_bl (q : real) &m : 0%r <= q =>
  Pr[ GN(Filt(A)).main() @ &m : (G.v /\ G.opd /\ sparse q G.md G.rel /\ is_lossless G.md) /\ G.rel G.n G.m' ]
  <= q * Pr[ GN(Filt(A)).pre() @ &m : G.v /\ G.opd /\ sparse q G.md G.rel /\ is_lossless G.md ].
proof.
move=> ge0q.
byphoare (_ : (glob A) = (glob A){m} ==>
              (G.v /\ G.opd /\ sparse q G.md G.rel /\ is_lossless G.md) /\ G.rel G.n G.m') => //.
proc.
seq 1 : (G.v /\ G.opd /\ sparse q G.md G.rel /\ is_lossless G.md)
        (Pr[ GN(Filt(A)).pre() @ &m : G.v /\ G.opd /\ sparse q G.md G.rel /\ is_lossless G.md ]) q
        _ 0%r => //.
+ call (_ : (glob A) = (glob A){m} ==> G.v /\ G.opd /\ sparse q G.md G.rel /\ is_lossless G.md).
  + bypr => &m0; split; first by rewrite Pr[mu_ge0].
    move=> h; byequiv (_ : ={glob A} ==> ={G.v, G.opd, G.md, G.rel}) => //.
    by proc; inline *; sim.
  by auto.
+ by rnd; auto => /> &hr _ _ hs _; apply hs.
+ by hoare; rnd; skip => />.
by move=> &hr _; rewrite mulrC.
qed.

lemma c5_filter (q : real) &m :
  0%r <= q => q < 1%r =>
  hoare[ G(A).main : true ==> G.opd => sparse q G.md G.rel ] =>
  Pr[ G(A).main() @ &m : G.v /\ G.rel G.m G.m' ]
  <= q * Pr[ G(A).main() @ &m : G.opd ] / ((1%r - q) * (1%r - q))
   + 2%r * (Pr[ G(Filt(A)).main() @ &m : G.v /\ G.rel G.m G.m' ]
            - Pr[ G(Filt(A)).main() @ &m : G.v /\ G.rel G.n G.m' ]
            - sqrt (Pr[ G(Filt(A)).main() @ &m : G.v /\ G.rel G.n G.m' ]
                    * Pr[ G(Filt(A)).main() @ &m : G.opd /\ !G.v ])) / (1%r - q).
proof.
move=> ge0q lt1q hsp.
(* the bad event: a valid opening outside the sparse, lossless regime *)
have hz : Pr[ G(A).main() @ &m : G.opd /\ !(sparse q G.md G.rel /\ is_lossless G.md) ] = 0%r.
+ byphoare => //; hoare; conseq hsp g_md_ll => /#.
have hz1 : Pr[ G(Filt(A)).main() @ &m : G.v /\ !(G.opd /\ sparse q G.md G.rel /\ is_lossless G.md) ] = 0%r.
+ have : Pr[ G(Filt(A)).main() @ &m : G.v /\ !(G.opd /\ sparse q G.md G.rel /\ is_lossless G.md) ]
       <= Pr[ G(A).main() @ &m : G.opd /\ !(sparse q G.md G.rel /\ is_lossless G.md) ].
  + byequiv (_ : ={glob A} ==> (G.v{1} => G.opd{1}) /\ ={G.md, G.rel, G.opd}) => //; last by smt().
    by symmetry; conseq e_filt => /#.
  by rewrite hz; smt(ge0_mu).
have hz2 : Pr[ GN(Filt(A)).main() @ &m : G.v /\ !(G.opd /\ sparse q G.md G.rel /\ is_lossless G.md) ] = 0%r.
+ by rewrite -hz1 eq_sym; byequiv e_gn.
(* Real is unchanged by filtering, and every valid filtered opening is related *)
have hr1 : Pr[ G(Filt(A)).main() @ &m : G.v ] = Pr[ G(A).main() @ &m : G.v /\ G.rel G.m G.m' ].
+ by rewrite eq_sym; byequiv e_filt => /#.
have hr2 : Pr[ G(Filt(A)).main() @ &m : G.v /\ G.rel G.m G.m' ] = Pr[ G(A).main() @ &m : G.v /\ G.rel G.m G.m' ].
+ by rewrite eq_sym; byequiv e_filt => /#.
have hp : Pr[ G(Filt(A)).main() @ &m : G.opd ] = Pr[ G(A).main() @ &m : G.opd ].
+ by rewrite eq_sym; byequiv e_filt => /#.
have hv : Pr[ G(Filt(A)).main() @ &m : G.opd /\ !G.v ] <= Pr[ G(A).main() @ &m : G.opd ].
+ by rewrite -hp Pr[mu_sub] => /#.
(* B of the filtered adversary is at most q * Real *)
have hgv : Pr[ G(Filt(A)).main() @ &m : G.v ]
         = Pr[ GN(Filt(A)).pre() @ &m : G.v /\ G.opd /\ sparse q G.md G.rel /\ is_lossless G.md ].
+ rewrite -(gn_main_pre q &m).
  have -> : Pr[ G(Filt(A)).main() @ &m : G.v ] = Pr[ GN(Filt(A)).main() @ &m : G.v ] by byequiv e_gn.
  by rewrite Pr[mu_split (G.opd /\ sparse q G.md G.rel /\ is_lossless G.md)] hz2.
have hb : Pr[ G(Filt(A)).main() @ &m : G.v /\ G.rel G.n G.m' ] <= q * Pr[ G(Filt(A)).main() @ &m : G.v ].
+ rewrite hgv; apply (ler_trans _ _ _ _ (gn_bl q &m ge0q)).
  have -> : Pr[ G(Filt(A)).main() @ &m : G.v /\ G.rel G.n G.m' ]
          = Pr[ GN(Filt(A)).main() @ &m : G.v /\ G.rel G.n G.m' ] by byequiv e_gn.
  rewrite Pr[mu_split (G.opd /\ sparse q G.md G.rel /\ is_lossless G.md)].
  have : Pr[ GN(Filt(A)).main() @ &m : (G.v /\ G.rel G.n G.m') /\ !(G.opd /\ sparse q G.md G.rel /\ is_lossless G.md) ]
       <= Pr[ GN(Filt(A)).main() @ &m : G.v /\ !(G.opd /\ sparse q G.md G.rel /\ is_lossless G.md) ].
  + by rewrite Pr[mu_sub] => /#.
  rewrite hz2.
  have -> : Pr[ GN(Filt(A)).main() @ &m : (G.v /\ G.rel G.n G.m') /\ (G.opd /\ sparse q G.md G.rel /\ is_lossless G.md) ]
          = Pr[ GN(Filt(A)).main() @ &m : (G.v /\ G.opd /\ sparse q G.md G.rel /\ is_lossless G.md) /\ G.rel G.n G.m' ].
  + by rewrite Pr[mu_eq] => /#.
  smt().
apply (filter_arith Pr[ G(A).main() @ &m : G.v /\ G.rel G.m G.m' ]
                    Pr[ G(Filt(A)).main() @ &m : G.v /\ G.rel G.n G.m' ]
                    Pr[ G(Filt(A)).main() @ &m : G.opd /\ !G.v ]
                    Pr[ G(A).main() @ &m : G.opd ] q
                    (Pr[ G(Filt(A)).main() @ &m : G.v /\ G.rel G.m G.m' ]
                     - Pr[ G(Filt(A)).main() @ &m : G.v /\ G.rel G.n G.m' ]
                     - sqrt (Pr[ G(Filt(A)).main() @ &m : G.v /\ G.rel G.n G.m' ]
                             * Pr[ G(Filt(A)).main() @ &m : G.opd /\ !G.v ]))
                    ge0q lt1q _ _ _ _ hv _).
+ by rewrite Pr[mu_ge0].
+ by rewrite Pr[mu_ge0].
+ by rewrite Pr[mu_ge0].
+ by rewrite -hr1.
by rewrite hr2.
qed.

end section.
