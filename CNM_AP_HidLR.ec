(* CNM-AP implies left-or-right hiding, for a stateful distinguisher that
   chooses its two messages after seeing pk (and may choose equal ones):

     Pr[ HidLR(D) : res ] - 1/2 = Adv_CNM-AP(AHL(D))            (hidlr_eq)

   with no gamma term.  This is the hiding step used by the reduction from
   simulation-based NM to AC-NM (paper, Appendix A, Lemma "hid"),
   whose distinguisher picks (u_J, u_J') from a list, so the two messages
   may coincide.

   AHL(D) uses md = uniform{m0, m1} and the relation
     relH m0 m1 x y = m0 <> m1 /\ (y = m0 \/ y = m1) /\ x <> y,
   commits to m_{1-b'} and opens it.  The guard "y in {m0, m1}" keeps the
   a-priori baseline at 1/2 (without it every y outside {m0, m1} would win
   always, and the prior would be 1); the guard "m0 <> m1" makes runs with
   equal messages contribute 0 to both the success and the baseline.     *)

pragma Goals:printall.

require import AllCore Distr DBool List StdRing StdOrder RealFLub.
require import CNM_AP.
import Biased RField RealOrder.

(* the scheme is functional *)
section Hypotheses.

declare axiom S_correct pk m c d :
  pk \in Gen => (c, d) \in Commit pk m => Verify pk (m, (c, d)).

module type LRD = {
  proc choose(pk : pubkey) : message * message
  proc guess(c : commitment) : bool
}.

module HidLR(D : LRD) = {
  var m0, m1 : message

  proc main() : bool = {
    var pk, b, b', c, d;
    pk       <$ Gen;
    (m0, m1) <@ D.choose(pk);
    b        <$ {0,1};
    (c, d)   <$ Commit pk (if b then m1 else m0);
    b'       <@ D.guess(c);
    return b = b';
  }
}.

op relH (m0 m1 : message) : relation =
  fun (x y : message) => m0 <> m1 /\ (y = m0 \/ y = m1) /\ x <> y.

module AHL(D : LRD) : AdvCNM = {
  var pk : pubkey
  var m0, m1, y : message
  var d' : openingkey

  proc init(x : pubkey) : message distr * relation = {
    pk       <- x;
    (m0, m1) <@ D.choose(x);
    return (duniform [m0; m1], relH m0 m1);
  }

  proc commit(c : commitment) : commitment = {
    var b', c';
    b'       <@ D.guess(c);
    y        <- if b' then m0 else m1;      (* m_{1-b'} *)
    (c', d') <$ Commit pk y;
    return c';
  }

  proc decommit(m : message, d : openingkey) : openingkey * message = {
    return (d', y);
  }
}.

lemma prior_relH (m0 m1 : message) :
  prior (duniform [m0; m1]) (relH m0 m1) = if m0 <> m1 then 1%r / 2%r else 0%r.
proof.
case: (m0 = m1) => [<- | ne] /=.
+ have : prior (duniform [m0; m0]) (relH m0 m0) <= 0%r.
  + apply flub_le_ub => w /=; rewrite /relH /=.
    by rewrite (@mu_eq _ _ pred0) // mu0.
  smt(prior_ge0).
apply ler_anti; split.
+ apply flub_le_ub => w /=; rewrite /relH ne /= duniformE /=.
  smt().
have := prior_ub (duniform [m0; m1]) (relH m0 m1) m0.
by rewrite /relH ne /= duniformE /=; smt().
qed.

(* a coin after the choice phase *)
module G2(D : LRD) = {
  proc main() : bool = {
    var pk, b;
    pk                     <$ Gen;
    (HidLR.m0, HidLR.m1)   <@ D.choose(pk);
    b                      <$ {0,1};
    return b;
  }
}.

(* HidLR with the commitment to m0 and the bit sampled last *)
module G3(D : LRD) = {
  proc main() : bool = {
    var pk, b, b', c, d;
    pk                     <$ Gen;
    (HidLR.m0, HidLR.m1)   <@ D.choose(pk);
    (c, d)                 <$ Commit pk HidLR.m0;
    b'                     <@ D.guess(c);
    b                      <$ {0,1};
    return b = b';
  }
}.

section.

declare module D <: LRD {-AHL, -HidLR, -RealG}.

declare axiom guess_ll : islossless D.guess.
declare axiom choose_ll : islossless D.choose.

local lemma real_eq &m :
  Pr[ RealG(AHL(D)).main() @ &m : res ]
  = Pr[ HidLR(D).main() @ &m : res /\ HidLR.m0 <> HidLR.m1 ].
proof.
byequiv => //; proc; inline *.
seq 5 2 : (={glob D, pk} /\ AHL.pk{1} = pk{1} /\ pk{1} \in Gen /\
           AHL.m0{1} = HidLR.m0{2} /\ AHL.m1{1} = HidLR.m1{2} /\
           md{1} = duniform [AHL.m0{1}; AHL.m1{1}] /\ rel{1} = relH AHL.m0{1} AHL.m1{1}).
+ by wp; call (: true); wp; rnd; skip => />.
case (AHL.m0{1} = AHL.m1{1}).
+ wp; rnd{1}; wp; call (: true); wp; rnd; rnd{2}; rnd{1}; skip => />.
  move=> &2 pk_in; split; first by apply duniform_ll.
  move=> _ m; rewrite supp_duniform /= => hm b _.
  have -> : m = HidLR.m1{2} by smt().
  by split => // _ cd cd_in; split => // _; apply Com_ll.
wp; rnd{1}; wp; call (: true); wp; rnd.
rnd (fun (m : message) => m = AHL.m1{1}) (fun (b : bool) => if b then AHL.m1{1} else AHL.m0{1}).
skip => /> &2 pk_in ne.
split; first by move=> b _; case: b => /=; smt().
move=> _; split.
+ move=> b _; rewrite dbool1E; case: b => /=; rewrite duniform1E /=; smt().
move=> _ m; rewrite supp_duniform /= => hm.
have em : (if m = HidLR.m1{2} then HidLR.m1{2} else HidLR.m0{2}) = m by smt().
rewrite em /=; move=> cd cd_in; split => // _ r.
split; first by apply Com_ll.
move=> _ cd' cd'_in.
have hv : Verify pk{2} ((if r then HidLR.m0{2} else HidLR.m1{2}), (cd'.`1, cd'.`2)).
+ by apply (S_correct pk{2} _ cd'.`1 cd'.`2 pk_in); rewrite -pairS.
split; first smt().
by smt().
qed.

local lemma base_g2 &m :
  Pr[ Base(AHL(D)).main() @ &m : res ]
  = Pr[ G2(D).main() @ &m : res /\ HidLR.m0 <> HidLR.m1 ].
proof.
byequiv => //; proc; inline *.
seq 5 2 : (={glob D} /\ AHL.m0{1} = HidLR.m0{2} /\ AHL.m1{1} = HidLR.m1{2} /\
           md{1} = duniform [AHL.m0{1}; AHL.m1{1}] /\ rel{1} = relH AHL.m0{1} AHL.m1{1}).
+ by wp; call (: true); wp; rnd; skip => />.
case (AHL.m0{1} = AHL.m1{1}).
+ rnd{1}; rnd{2}; skip => /> &2 b _; split; first by apply dbiased_ll.
  by move=> _ b1; rewrite prior_relH /= supportP dbiased1E clamp_id //; case: b1.
rnd; skip => /> &2 ne b _.
by rewrite prior_relH ne /= dbiased1E dbool1E; case: b; rewrite clamp_id; smt().
qed.

local lemma g2_half &m :
  Pr[ G2(D).main() @ &m : res /\ HidLR.m0 <> HidLR.m1 ]
  = Pr[ G2(D).main() @ &m : HidLR.m0 <> HidLR.m1 ] / 2%r.
proof.
have flip : Pr[ G2(D).main() @ &m : res /\ HidLR.m0 <> HidLR.m1 ]
          = Pr[ G2(D).main() @ &m : !res /\ HidLR.m0 <> HidLR.m1 ].
+ by byequiv => //; proc; rnd (fun b => !b); call (: true); rnd; skip => /> /#.
have : Pr[ G2(D).main() @ &m : HidLR.m0 <> HidLR.m1 ]
     = Pr[ G2(D).main() @ &m : res /\ HidLR.m0 <> HidLR.m1 ]
     + Pr[ G2(D).main() @ &m : !res /\ HidLR.m0 <> HidLR.m1 ].
+ by rewrite Pr[mu_split res]; congr; rewrite Pr[mu_eq] /#.
smt().
qed.

local lemma g2_hid &m :
  Pr[ G2(D).main() @ &m : HidLR.m0 <> HidLR.m1 ]
  = Pr[ HidLR(D).main() @ &m : HidLR.m0 <> HidLR.m1 ].
proof.
byequiv => //; proc.
call{2} guess_ll; rnd{2}; rnd; call (: true); rnd; skip => />.
smt(Com_ll).
qed.

local lemma hid_g3 &m :
  Pr[ HidLR(D).main() @ &m : res /\ HidLR.m0 = HidLR.m1 ]
  = Pr[ G3(D).main() @ &m : res /\ HidLR.m0 = HidLR.m1 ].
proof.
byequiv (_ : ={glob D} ==>
  (res /\ HidLR.m0 = HidLR.m1){1} = (res /\ HidLR.m0 = HidLR.m1){2}) => [| // | /#].
proc.
seq 2 2 : (={glob D, pk, HidLR.m0, HidLR.m1}).
+ by call (: true); rnd; skip.
case (HidLR.m0{1} = HidLR.m1{1}).
+ swap{2} 3 -2; call (: true); rnd; rnd; skip => /> &2 eq b _; split; smt().
rnd{2}; call{1} guess_ll; call{2} guess_ll; rnd{2}; rnd{1}; rnd{1}; skip => />.
smt(Com_ll dbool_ll).
qed.

local lemma g3_half &m :
  Pr[ G3(D).main() @ &m : res /\ HidLR.m0 = HidLR.m1 ]
  = Pr[ G3(D).main() @ &m : HidLR.m0 = HidLR.m1 ] / 2%r.
proof.
have flip : Pr[ G3(D).main() @ &m : res /\ HidLR.m0 = HidLR.m1 ]
          = Pr[ G3(D).main() @ &m : !res /\ HidLR.m0 = HidLR.m1 ].
+ byequiv => //; proc; rnd (fun b => !b); call (: true); rnd; call (: true); rnd.
  by skip => /> /#.
have : Pr[ G3(D).main() @ &m : HidLR.m0 = HidLR.m1 ]
     = Pr[ G3(D).main() @ &m : res /\ HidLR.m0 = HidLR.m1 ]
     + Pr[ G3(D).main() @ &m : !res /\ HidLR.m0 = HidLR.m1 ].
+ by rewrite Pr[mu_split res]; congr; rewrite Pr[mu_eq] /#.
smt().
qed.

local lemma g3_hid &m :
  Pr[ G3(D).main() @ &m : HidLR.m0 = HidLR.m1 ]
  = Pr[ HidLR(D).main() @ &m : HidLR.m0 = HidLR.m1 ].
proof.
byequiv => //; proc.
rnd{1}; call{1} guess_ll; call{2} guess_ll; rnd{1}; rnd{2}; rnd{2}.
call (: true); rnd; skip => />; smt(Com_ll dbool_ll).
qed.

local lemma hid_ll &m :
  Pr[ HidLR(D).main() @ &m : HidLR.m0 <> HidLR.m1 ]
  + Pr[ HidLR(D).main() @ &m : HidLR.m0 = HidLR.m1 ] = 1%r.
proof.
have -> : Pr[ HidLR(D).main() @ &m : HidLR.m0 <> HidLR.m1 ]
        + Pr[ HidLR(D).main() @ &m : HidLR.m0 = HidLR.m1 ]
        = Pr[ HidLR(D).main() @ &m : true ].
+ by rewrite eq_sym Pr[mu_split HidLR.m0 <> HidLR.m1] /=.
byphoare => //; proc; call guess_ll; rnd; rnd; call choose_ll; rnd; skip => />.
have -> : (fun (x : pubkey) => forall (result : message * message),
             mu {0,1} (fun (x0 : bool) =>
               weight (Commit x (if x0 then result.`2 else result.`1)) = 1%r) = 1%r)
         = predT.
+ apply fun_ext => pk; rewrite /predT eqT => r.
  have -> : (fun (x0 : bool) => weight (Commit pk (if x0 then r.`2 else r.`1)) = 1%r)
          = predT by apply fun_ext => b; rewrite /predT Com_ll.
  by apply dbool_ll.
by apply Gen_ll.
qed.

lemma hidlr_eq &m :
  Pr[ HidLR(D).main() @ &m : res ] - 1%r / 2%r
  = Pr[ RealG(AHL(D)).main() @ &m : res ] - Pr[ Base(AHL(D)).main() @ &m : res ].
proof.
rewrite real_eq base_g2 g2_half g2_hid.
have : Pr[ HidLR(D).main() @ &m : res ]
     = Pr[ HidLR(D).main() @ &m : res /\ HidLR.m0 <> HidLR.m1 ]
     + Pr[ HidLR(D).main() @ &m : res /\ HidLR.m0 = HidLR.m1 ].
+ by rewrite Pr[mu_split HidLR.m0 <> HidLR.m1]; congr; rewrite Pr[mu_eq] /#.
have := hid_g3 &m; have := g3_half &m; have := g3_hid &m; have := hid_ll &m.
smt().
qed.

end section.

end section Hypotheses.
