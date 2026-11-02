(* Simulation-based NM implies AC-NM-init: the game level of the reduction
   (paper, Appendix A, Lemmas "test" and "mix").  Sim_C5_Ideal.ec is the
   distribution level; this file connects it to the games.

   The adversary A is an arbitrary lossless AC-NM-init adversary (an
   abstract module), whose message distribution is lossless.  The games:
     GI(A)           the AC-NM-init experiment (C5.G with the relation fixed
                     at initialisation), with the events Real, B and V
     A2(A)           A''_t, the CNM-AP adversary of the mixed first-hit
                     partition test (k ~ k w_k / Z on [1, K], u ~ md^k,
                     md' = a uniform entry of u, R'(x, y) = [x = u_{j*(y)}],
                     fallback commitment to ystar after a halt)
     D2(A)           D''_t, the left-or-right distinguisher of the halting
                     part, turned into a CNM-AP adversary by
                     CNM_AP_HidLR.AHL
     GF(A), GC(A)    Pr[challenge = ystar] and Pr[two samples collide]

   Proved here (no admits):
     compose (Compose)  a game "initialise; sample; run A once; decide" has
                        the probability of the reflected distributions of
                        the initialisation and of one run (Reflection.eca)
     gi_cg, gf_cg, gc_cg, a2_real, a2_base, hid_ch
                        the games are composed games (a2_real: A''_t wins at
                        least when the partition test does; the fallback
                        opens validly by correctness)
     real_E, bl_E, vl_E, gf_E, gc_E, a2r_E, a2b_E, hid_E
                        their values as expectations over the reflected
                        initialisation, in the terms of Sim_C5_Ideal (test_E:
                        the uniform challenge index gives the sum over the
                        worlds; hid_k: the hiding game is 1/2 + (haltp -
                        hsum k)/(2k) for each k)
     mix_point          sim_c5_ideal at every state reached after init
     mix_game           integrated over the initialisation
     mix_cnmap          with the hiding term as a CNM-AP advantage
                        (CNM_AP_HidLR.hidlr_eq)
     gf_gc              Pr[GF]^2 <= Pr[GC] (Jensen)
     mix_sqrt           THE THEOREM (Lemma "mix"):
       2t Real <= t (2 + t) B + V + Z Adv_CNM-AP(A''_t)
                  + 2 Z Adv_CNM-AP(A_H(D''_t)) + Z sqrt(cp) + (1 + t)^4 cp
                  + (1 - rho)^K (K + 1 + 1/rho)
     with Z = sum_k k w_k <= (1 + t)^2 (Sim_C5_Core.sum_bounds) and
     cp = Pr[GC] the collision probability of md averaged over the
     initialisation.

   t and K are the theory parameters tmix and Kmix (0 < t, 1 <= K are
   hypotheses).  Not covered: the choice of t and the k = 2 test of
   Theorem 9 (Sim_C5_Core.choose_t is the analytic part of the former), the
   estimate of the truncation term for K = ceil(lambda (1 + t)^2), and the
   running times of the reductions. *)

pragma Goals:printall.

require import AllCore List Distr DBool DList DInterval RealSeries StdBigop StdOrder StdRing RealFLub.
require import CNM_AP RealExp.
require CNM_AP_HidLR.
require Sim_C5_Core Sim_C5_Ideal Reflection.
import Biased RField RealOrder StdBigop.Bigreal BRA.

clone Sim_C5_Ideal as SI with type msg <- message.

lemma mu_dlet_E ['a 'b] (d : 'a distr) (F : 'a -> 'b distr) (P : 'b -> bool) :
  mu (dlet d F) P = E d (fun x => mu (F x) P).
proof. by rewrite dletE /E; apply eq_sum => x /=; ring. qed.

(* -------------------------------------------------------------------- *)
(* AC-NM-init: the relation is fixed at initialisation                  *)

module type AdvACI = {
  proc init(pk : pubkey) : message distr * relation
  proc commit(c : commitment) : commitment option
  proc decommit(m : message, d : openingkey) : (openingkey * message) option
}.

(* the initialisation, and one run of the adversary on challenge m, with its
   outcome: halt (including copying c), refusal or invalid opening, or a
   valid opening of y *)
module Pre(A : AdvACI) = {
  proc p(u : unit) : pubkey * (message distr * relation) = {
    var pk, mr;
    pk <$ Gen;
    mr <@ A.init(pk);
    return (pk, mr);
  }
}.

module Run(A : AdvACI) = {
  proc p(x : pubkey * message) : SI.outc = {
    var c, d, r, o, out;
    (c, d) <$ Commit x.`1 x.`2;
    r      <@ A.commit(c);
    out    <- SI.Halt;
    if (r <> None /\ oget r <> c) {
      o    <@ A.decommit(x.`2, d);
      out  <- if o <> None /\ Verify x.`1 ((oget o).`2, (oget r, (oget o).`1))
              then SI.Opn (oget o).`2 else SI.Ref;
    }
    return out;
  }
}.

clone Reflection as RPre with
  type Proc.a <- unit,
  type Proc.r <- pubkey * (message distr * relation).

clone Reflection as RRun with
  type Proc.a <- pubkey * message,
  type Proc.r <- SI.outc.

(* -------------------------------------------------------------------- *)
(* composition: a game that initialises, samples, runs the adversary     *)
(* once and decides, has the probability of the reflected distributions *)

abstract theory Compose.

type s1, s2.

type st = pubkey * (message distr * relation).

module G(A : AdvACI) = {
  proc main(S1 : st -> s1 distr, S2 : st -> s1 -> s2 distr,
            mof : st -> s1 -> s2 -> message,
            fin : st -> s1 -> s2 -> SI.outc -> bool) : bool = {
    var x, a, b, o;
    x <@ Pre(A).p();
    a <$ S1 x;
    b <$ S2 x a;
    o <@ Run(A).p((x.`1, mof x a b));
    return fin x a b o;
  }
}.

section.

declare module A <: AdvACI.

local module SP = {
  proc s(d : (st * glob A) distr) : st * glob A = {
    var r;
    r <$ d;
    return r;
  }
}.

local module SR = {
  proc s(d : SI.outc distr) : SI.outc = {
    var r;
    r <$ d;
    return r;
  }
}.

local module IG = {
  proc main(dp : (st * glob A) distr, dr : glob A -> pubkey * message -> SI.outc distr,
            S1 : st -> s1 distr, S2 : st -> s1 -> s2 distr,
            mof : st -> s1 -> s2 -> message,
            fin : st -> s1 -> s2 -> SI.outc -> bool) : bool = {
    var y, a, b, o;
    y <@ SP.s(dp);
    a <$ S1 y.`1;
    b <$ S2 y.`1 a;
    o <@ SR.s(dr y.`2 (y.`1.`1, mof y.`1 a b));
    return fin y.`1 a b o;
  }
}.

lemma compose (DP : glob A -> unit -> (st * glob A) distr)
              (DR : glob A -> pubkey * message -> SI.outc distr) &m S1 S2 mof fin :
  (forall &m0 po, mu (DP (glob A){m0} tt) po = Pr[Pre(A).p() @ &m0 : po (res, glob A)]) =>
  (forall &m0 po x, mu (DR (glob A){m0} x) po = Pr[Run(A).p(x) @ &m0 : po res]) =>
  Pr[G(A).main(S1, S2, mof, fin) @ &m : res]
  = E (DP (glob A){m} tt) (fun (y : st * glob A) =>
      E (S1 y.`1) (fun a => E (S2 y.`1 a) (fun b =>
        mu (DR y.`2 (y.`1.`1, mof y.`1 a b)) (fin y.`1 a b)))).
proof.
move=> hDP hDR.
have ePre : equiv[Pre(A).p ~ SP.s : d{2} = DP (glob A){1} tt ==> res{1} = res{2}.`1 /\ (glob A){1} = res{2}.`2].
+ bypr (res, glob A){1} (res){2} => // &1 &2 a hd.
  have -> : Pr[SP.s(d{2}) @ &2 : res = a] = mu1 (DP (glob A){1} tt) a.
  + by byphoare (_ : d = DP (glob A){1} tt ==> _) => //; proc; rnd; skip.
  rewrite hDP; byequiv (_ : ={arg, glob A} ==> ={res, glob A}) => //; by sim.
have eRun : equiv[Run(A).p ~ SR.s : d{2} = DR (glob A){1} x{1} ==> ={res}].
+ bypr (res){1} (res){2} => // &1 &2 a hd.
  have -> : Pr[SR.s(d{2}) @ &2 : res = a] = mu1 (DR (glob A){1} x{1}) a.
  + by byphoare (_ : d = DR (glob A){1} x{1} ==> _) => //; proc; rnd; skip.
  by rewrite hDR.
have -> : Pr[G(A).main(S1, S2, mof, fin) @ &m : res]
        = Pr[IG.main(DP (glob A){m} tt, DR, S1, S2, mof, fin) @ &m : res].
+ byequiv (_ : ={glob A} /\ arg{1} = (S1, S2, mof, fin)
                /\ arg{2} = (DP (glob A){m} tt, DR, S1, S2, mof, fin)
                /\ (glob A){1} = (glob A){m} ==> ={res}) => //.
  proc.
  call eRun; rnd; rnd; call ePre; skip => />.
byphoare (_ : arg = (DP (glob A){m} tt, DR, S1, S2, mof, fin) ==> _) => //.
proc; inline *; wp.
rndsem* 0; rnd (fun (x : (st * glob A) * s1 * s2 * SI.outc) => fin x.`1.`1 x.`2 x.`3 x.`4).
skip => />.
rewrite mu_dlet_E; apply eq_exp => y _ /=; rewrite mu_dlet_E; apply eq_exp => a _ /=.
rewrite mu_dlet_E; apply eq_exp => b _ /=; rewrite dmapE /(\o) /=.
by apply mu_eq.
qed.

end section.

end Compose.

clone Compose as CG with type s1 <- message, type s2 <- message.

(* -------------------------------------------------------------------- *)
(* the AC-NM-init experiment (C5.G with the relation fixed at init)     *)

module GI(A : AdvACI) = {
  var md : message distr
  var rel : relation
  var m, n, m' : message
  var opd, v : bool

  proc main() : unit = {
    var pk, c, d, r, o;
    pk        <$ Gen;
    (md, rel) <@ A.init(pk);
    m         <$ md;
    n         <$ md;
    (c, d)    <$ Commit pk m;
    r         <@ A.commit(c);
    opd       <- false;
    v         <- false;
    m'        <- witness;
    if (r <> None /\ oget r <> c) {
      opd     <- true;
      o       <@ A.decommit(m, d);
      m'      <- (oget o).`2;
      v       <- o <> None /\ Verify pk (m', (oget r, (oget o).`1));
    }
  }
}.

(* the AC-NM quantities of one run, as events on the outcome *)
op finR (x : CG.st) (a b : message) (o : SI.outc) : bool =
  match o with SI.Halt => false | SI.Ref => false | SI.Opn y => x.`2.`2 a y end.
op finB (x : CG.st) (a b : message) (o : SI.outc) : bool =
  match o with SI.Halt => false | SI.Ref => false | SI.Opn y => x.`2.`2 b y end.
op finV (x : CG.st) (a b : message) (o : SI.outc) : bool = o = SI.Ref.

op FRl (R : relation) (a b : message) (o : SI.outc) : bool =
  match o with SI.Halt => false | SI.Ref => false | SI.Opn y => R a y end.
op FBl (R : relation) (a b : message) (o : SI.outc) : bool =
  match o with SI.Halt => false | SI.Ref => false | SI.Opn y => R b y end.
op FVl (R : relation) (a b : message) (o : SI.outc) : bool = o = SI.Ref.

op S1m (x : CG.st) : message distr = x.`2.`1.
op S2m (x : CG.st) (a : message) : message distr = x.`2.`1.
op mofm (x : CG.st) (a b : message) : message = a.

(* -------------------------------------------------------------------- *)
(* the parameters of the reduction and its sampling distributions        *)

op tmix : real.      (* the parameter t of the mixture *)
op Kmix : int.       (* the truncation K *)
op ystar : message.  (* the fallback value *)

op wk (k : int) : real = Sim_C5_Core.w tmix k.
op Zk : real = bigi predT (fun k => k%r * wk k) 1 (Kmix + 1).

(* k is sampled with probability k w_k / Z, 1 <= k <= K *)
op pK (k : int) : real = if 1 <= k <= Kmix then k%r * wk k / Zk else 0%r.
op dK : int distr = mk pK.

(* the partition test with k points: a uniform entry of u, and the cell
   relation of the first hit *)
op SAd (md : message distr) : (int * message list) distr =
  dlet dK (fun k => dmap (dlist md k) (fun u => (k, u))).
op mdA (u : message list) : message distr = dmap (drange 0 (size u)) (nth witness u).
op relA (R : relation) (u : message list) : relation =
  fun (a y : message) => a = nth witness u (SI.jst R u y).

(* the hiding distinguisher samples k, u and two indices *)
op SHd (md : message distr) : (int * message list * int * int) distr =
  dlet dK (fun k => dlet (dlist md k) (fun u =>
    dmap (drange 0 k `*` drange 0 k) (fun (jj : int * int) => (k, u, jj.`1, jj.`2)))).

(* A''_t: the CNM-AP adversary of the mixed partition test *)
module A2(A : AdvACI) : AdvCNM = {
  var pk : pubkey
  var u : message list
  var rel : relation
  var halted : bool
  var dst : openingkey

  proc init(x : pubkey) : message distr * relation = {
    var md, s;
    pk        <- x;
    (md, rel) <@ A.init(x);
    s         <$ SAd md;
    u         <- s.`2;
    return (mdA u, relA rel u);
  }

  proc commit(c : commitment) : commitment = {
    var r, c';
    r      <@ A.commit(c);
    halted <- !(r <> None /\ oget r <> c);
    c'     <- oget r;
    if (halted) {
      (c', dst) <$ Commit pk ystar;
    }
    return c';
  }

  proc decommit(m : message, d : openingkey) : openingkey * message = {
    var o, rs;
    if (halted) {
      rs <- (dst, ystar);
    } else {
      o  <@ A.decommit(m, d);
      rs <- oget o;
    }
    return rs;
  }
}.

(* D''_t: the left-or-right distinguisher for the halting part *)
module D2(A : AdvACI) = {
  var u : message list
  var rel : relation
  var j : int

  proc choose(pk : pubkey) : message * message = {
    var md, s;
    (md, rel) <@ A.init(pk);
    s         <$ SHd md;
    u         <- s.`2;
    j         <- s.`3;
    return (nth witness u j, nth witness u s.`4);
  }

  proc guess(c : commitment) : bool = {
    var r;
    r <@ A.commit(c);
    return !(r <> None /\ oget r <> c) /\ j = SI.jst rel u ystar;
  }
}.

(* the challenge equals the fallback value; two samples collide *)
module GF(A : AdvACI) = {
  proc main() : bool = {
    var pk, md, rel, m, n;
    pk         <$ Gen;
    (md, rel)  <@ A.init(pk);
    m          <$ md;
    n          <$ md;
    return m = ystar;
  }
}.

module GC(A : AdvACI) = {
  proc main() : bool = {
    var pk, md, rel, m, n;
    pk         <$ Gen;
    (md, rel)  <@ A.init(pk);
    m          <$ md;
    n          <$ md;
    return m = n;
  }
}.

clone Compose as CA with type s1 <- int * message list, type s2 <- message.
clone Compose as CB with type s1 <- int * message list, type s2 <- bool.
clone Compose as CH with type s1 <- int * message list * int * int, type s2 <- bool.

(* the decision of each composed game *)
op winm (R : relation) (u : message list) (m : message) (o : SI.outc) : bool =
  match o with
  | SI.Halt  => m = nth witness u (SI.jst R u ystar) /\ m <> ystar
  | SI.Ref   => false
  | SI.Opn y => m = nth witness u (SI.jst R u y)
  end.

op S1A (x : CG.st) : (int * message list) distr = SAd x.`2.`1.
op S2A (x : CG.st) (a : int * message list) : message distr = mdA a.`2.
op mofA (x : CG.st) (a : int * message list) (b : message) : message = b.
op finA (x : CG.st) (a : int * message list) (b : message) (o : SI.outc) : bool =
  winm x.`2.`2 a.`2 b o.

op S2B (x : CG.st) (a : int * message list) : bool distr =
  dbiased (SI.priork x.`2.`2 a.`2).
op mofB (x : CG.st) (a : int * message list) (b : bool) : message = witness.
op finB' (x : CG.st) (a : int * message list) (b : bool) (o : SI.outc) : bool = b.

op S1H (x : CG.st) : (int * message list * int * int) distr = SHd x.`2.`1.
op S2H (x : CG.st) (a : int * message list * int * int) : bool distr = {0,1}.
op mofH (x : CG.st) (a : int * message list * int * int) (b : bool) : message =
  if b then nth witness a.`2 a.`4 else nth witness a.`2 a.`3.
op finH (x : CG.st) (a : int * message list * int * int) (b : bool) (o : SI.outc) : bool =
  b = (o = SI.Halt /\ a.`3 = SI.jst x.`2.`2 a.`2 ystar).

(* -------------------------------------------------------------------- *)
(* expectations of bounded functions                                    *)

lemma hasE_bnd ['a] (d : 'a distr) (f : 'a -> real) (c : real) :
  (forall x, `|f x| <= c) => hasE d f.
proof. by move=> h; apply (hasE_le _ _ (fun _ => c)); [apply hasEC | smt()]. qed.

lemma exp_dlet_b ['a 'b] (d : 'a distr) (df : 'a -> 'b distr) (f : 'b -> real) (c : real) :
  (forall x, `|f x| <= c) => E (dlet d df) f = E d (fun x => E (df x) f).
proof. by move=> h; rewrite exp_dlet //; apply (hasE_bnd _ _ c). qed.

lemma exp_dmap_b ['a 'b] (d : 'a distr) (g : 'a -> 'b) (f : 'b -> real) (c : real) :
  (forall x, `|f x| <= c) => E (dmap d g) f = E d (fun x => f (g x)).
proof. by move=> h; rewrite exp_dmap //; apply (hasE_bnd _ _ c). qed.

lemma exp_b2r ['a] (d : 'a distr) (P : 'a -> bool) :
  E d (fun x => b2r (P x)) = mu d P.
proof. by rewrite /E muE; apply eq_sum => x /=; case: (P x). qed.

lemma exp_drange (k : int) (f : int -> real) : 0 < k =>
  E (drange 0 k) f = 1%r / k%r * bigi predT f 0 k.
proof.
move=> gt0k; rewrite /drange exp_duniform undup_id 1:range_uniq size_range.
by rewrite (_ : max 0 (k - 0) = k) 1:/#.
qed.

lemma exp_dbool (f : bool -> real) : E {0,1} f = (f true + f false) / 2%r.
proof.
rewrite /E (sumE_fin _ [true; false]) //=; first smt().
by rewrite big_cons big_cons big_nil /predT /= !dbool1E; ring.
qed.

lemma mu_dprod_E ['a 'b] (da : 'a distr) (db : 'b distr) (P : 'a -> 'b -> bool) :
  mu (da `*` db) (fun (p : 'a * 'b) => P p.`1 p.`2) = E da (fun a => mu db (P a)).
proof.
rewrite dprod_dlet mu_dlet_E; apply eq_exp => a _ /=.
rewrite mu_dlet_E (eq_exp _ _ (fun b => b2r (P a b))) => [b _ /=|].
+ by rewrite dunitE.
by rewrite exp_b2r.
qed.

lemma fubini_mu ['a 'b] (da : 'a distr) (db : 'b distr) (P : 'a -> 'b -> bool) :
  E da (fun a => mu db (P a)) = E db (fun b => mu da (fun a => P a b)).
proof.
rewrite -mu_dprod_E dprodC dmapE /(\o) /= -(mu_dprod_E db da (fun b a => P a b)) /=.
by apply mu_eq.
qed.

(* the k-th entry of a list of independent samples is a sample *)
lemma exp_nth (md : message distr) (k J : int) (f : message -> real) (c : real) :
  is_lossless md => 0 <= J < k => (forall x, `|f x| <= c) =>
  E (dlist md k) (fun u => f (nth witness u J)) = E md f.
proof.
move=> mdll [ge0J ltJk] hf.
have dl : dlist md k = dmap (md `*` dlist md (k - 1)) (fun (x : message * message list) => insert x.`1 x.`2 J).
+ have := dlist_insert witness J (k - 1) md _ _; 1,2: smt().
  by rewrite (_ : k - 1 + 1 = k) 1:/#.
rewrite dl (exp_dmap_b _ _ _ c) /=; first by smt().
rewrite (eq_exp _ _ (fun (x : message * message list) => f x.`1)).
+ move=> -[m r]; rewrite supp_dprod supp_dlist 1:/# /= => -[_ [szr _]].
  by rewrite nth_insert 1:/#.
have -> := SI.exp_dprod (dunit witness) (fun _ => dunit SI.Halt) _ _ md (dlist md (k - 1))
                         (fun (x : message * message list) => f x.`1) c _.
+ by apply dunit_ll.
+ by move=> ?; apply dunit_ll.
+ by move=> x /=; smt().
apply eq_exp => m _ /=.
by rewrite expC (dlist_ll md (k - 1) mdll).
qed.

lemma e01 ['a] (d : 'a distr) (F : 'a -> real) :
  (forall x, 0%r <= F x <= 1%r) => 0%r <= E d F <= 1%r.
proof.
move=> h; apply (SI.exp01 (dunit witness) (fun _ => dunit SI.Halt)) => //.
+ by apply dunit_ll.
by move=> ?; apply dunit_ll.
qed.

lemma sum_E ['a] (d : 'a distr) (f : int -> 'a -> real) (m n : int) (c : real) :
  m <= n => (forall J x, m <= J < n => 0%r <= f J x <= c) =>
  bigi predT (fun J => E d (f J)) m n = E d (fun x => bigi predT (fun J => f J x) m n).
proof.
move=> lemn h; apply (SI.sum_exp_range (dunit witness) (fun _ => dunit SI.Halt) _ _ d f m n c) => //.
+ by apply dunit_ll.
by move=> ?; apply dunit_ll.
qed.

lemma mu01 ['a] (d : 'a distr) (P : 'a -> bool) : 0%r <= mu d P <= 1%r.
proof. by smt(ge0_mu le1_mu). qed.

lemma exp_aff ['a] (d : 'a distr) (a b : real) (f : 'a -> real) (c : real) :
  is_lossless d => (forall x, `|f x| <= c) =>
  E d (fun x => a + b * f x) = a + b * E d f.
proof.
move=> ll hf; rewrite expD; first by apply hasEC.
+ by apply hasEZ; apply (hasE_bnd _ _ c).
by rewrite expC ll expZ.
qed.

lemma exp_lin2 ['a] (d : 'a distr) (a b : real) (f g : 'a -> real) (c : real) :
  (forall x, `|f x| <= c) => (forall x, `|g x| <= c) =>
  E d (fun x => a * f x - b * g x) = a * E d f - b * E d g.
proof.
move=> hf hg; rewrite expB; first 2 by apply hasEZ; apply (hasE_bnd _ _ c).
by rewrite !expZ.
qed.

(* one coin of the left-or-right game, for fixed u, J, J' *)
lemma hid_coin (run : message -> SI.outc distr) (R : relation) (u : message list) (J J' : int) :
  is_lossless (run (nth witness u J)) =>
  E {0,1} (fun b => mu (run (if b then nth witness u J' else nth witness u J))
                       (fun o => b = (o = SI.Halt /\ J = SI.jst R u ystar)))
  = 1%r / 2%r + 1%r / 2%r * b2r (J = SI.jst R u ystar)
      * (mu (run (nth witness u J')) (pred1 SI.Halt) - mu (run (nth witness u J)) (pred1 SI.Halt)).
proof.
move=> ll; rewrite exp_dbool /=.
case: (J = SI.jst R u ystar) => hj /=.
+ rewrite (mu_eq _ _ (pred1 SI.Halt)) 1:/#.
  rewrite (mu_eq _ (fun (o : SI.outc) => false = (o = SI.Halt)) (predC (pred1 SI.Halt))) 1:/#.
  by rewrite mu_not ll; ring.
rewrite (mu_eq _ (fun (o : SI.outc) => false = false) predT) // ll.
by rewrite (mu_eq _ _ pred0) // mu0.
qed.

lemma hid_k (md : message distr) (R : relation) (run : message -> SI.outc distr) (k : int) :
  is_lossless md => (forall m, is_lossless (run m)) => 1 <= k =>
  E (dlist md k) (fun u => E (drange 0 k `*` drange 0 k) (fun (jj : int * int) =>
     E {0,1} (fun b => mu (run (if b then nth witness u jj.`2 else nth witness u jj.`1))
                          (fun o => b = (o = SI.Halt /\ jj.`1 = SI.jst R u ystar)))))
  = 1%r / 2%r + (SI.haltp md run - SI.hsum md R run ystar k) / (2%r * k%r).
proof.
move=> mdll runll ge1k.
pose h := fun m => mu (run m) (pred1 SI.Halt).
pose c := fun (u : message list) (J : int) => b2r (J = SI.jst R u ystar).
have h01 : forall m, 0%r <= h m <= 1%r by move=> m; apply mu01.
have c01 : forall u J, 0%r <= c u J <= 1%r by move=> u J; rewrite /c; case: (J = SI.jst R u ystar).
have dr_ll : is_lossless (drange 0 k) by apply drange_ll; smt().
(* per u, the two indices *)
have hu : forall u, size u = k =>
    E (drange 0 k `*` drange 0 k) (fun (jj : int * int) =>
      E {0,1} (fun b => mu (run (if b then nth witness u jj.`2 else nth witness u jj.`1))
                         (fun o => b = (o = SI.Halt /\ jj.`1 = SI.jst R u ystar))))
  = 1%r / 2%r + 1%r / 2%r * (1%r / k%r * E (drange 0 k) (fun J' => h (nth witness u J'))
                             - 1%r / k%r * bigi predT (fun J => c u J * h (nth witness u J)) 0 k).
+ move=> u szu.
  rewrite (eq_exp _ _ (fun (jj : int * int) => 1%r / 2%r + 1%r / 2%r * c u jj.`1
                         * (h (nth witness u jj.`2) - h (nth witness u jj.`1)))).
  + by move=> jj _ /=; rewrite hid_coin 1:runll /c /h.
  rewrite (SI.exp_dprod (dunit witness) (fun _ => dunit SI.Halt) _ _ _ _ _ 2%r).
  + by apply dunit_ll.
  + by move=> ?; apply dunit_ll.
  + by move=> jj /=; smt().
  pose EH := E (drange 0 k) (fun J' => h (nth witness u J')).
  have [eh0 eh1] : 0%r <= EH <= 1%r by apply e01.
  rewrite /= (eq_exp _ _ (fun J => 1%r / 2%r + 1%r / 2%r
                 * (EH * c u J - 1%r * (c u J * h (nth witness u J))))).
  + move=> J _ /=.
    rewrite (eq_exp _ _ (fun J' => (1%r / 2%r - 1%r / 2%r * c u J * h (nth witness u J))
                                 + (1%r / 2%r * c u J) * h (nth witness u J'))) => [J' _ /=|].
    + by ring.
    by rewrite (exp_aff _ _ _ _ 1%r) //; [smt() | rewrite -/EH; ring].
  rewrite (exp_aff _ _ _ _ 2%r) //; first by move=> J /=; smt().
  rewrite (exp_lin2 _ _ _ (fun J => c u J) (fun J => c u J * h (nth witness u J)) 1%r).
  + by move=> J /=; smt().
  + by move=> J /=; smt().
  have -> : E (drange 0 k) (fun J => c u J) = 1%r / k%r.
  + rewrite /c exp_b2r (mu_eq _ _ (pred1 (SI.jst R u ystar))) // drange1E.
    have := SI.jst_range (dunit witness) R (fun _ => dunit SI.Halt) _ _ u ystar _.
    + by apply dunit_ll.
    + by move=> ?; apply dunit_ll.
    + smt().
    by rewrite szu => -> /=.
  by rewrite exp_drange 1:/#; ring.
pose EHu := fun u => E (drange 0 k) (fun J' => h (nth witness u J')).
pose Su := fun u => bigi predT (fun J => c u J * h (nth witness u J)) 0 k.
have bS : forall u, `|Su u| <= k%r.
+ move=> u; rewrite /Su; have : 0%r <= bigi predT (fun J => c u J * h (nth witness u J)) 0 k <= k%r.
  + split; first by apply sumr_ge0_seq => J _ _ /=; smt().
    move=> _; apply (ler_trans (bigi predT (fun _ => 1%r) 0 k)).
    + by apply ler_sum_seq => J _ _ /=; smt().
    by rewrite sumri_const 1:/# intmulr; smt().
  smt().
have bH : forall u, `|EHu u| <= k%r.
+ move=> u; rewrite /EHu; have := e01 (drange 0 k) (fun J' => h (nth witness u J')) _; [by move=> J'; apply h01 | smt()].
rewrite (eq_exp _ _ (fun u => 1%r / 2%r + 1%r / 2%r * (1%r / k%r * EHu u - 1%r / k%r * Su u))).
+ by move=> u; rewrite supp_dlist 1:/# => -[szu _] /=; rewrite hu.
rewrite (exp_aff _ _ _ _ 2%r) //; first by apply dlist_ll.
+ move=> u /=; have h1 := bS u; have h2 := bH u.
  have : `|1%r / k%r * EHu u| <= 1%r.
  + rewrite normrM ger0_norm 1:/# /EHu; have := e01 (drange 0 k) (fun J' => h (nth witness u J')) _.
    + by move=> J'; apply h01.
    move=> [e0 e1]; rewrite ger0_norm //; smt().
  have : `|1%r / k%r * Su u| <= 1%r.
  + rewrite normrM (ger0_norm (1%r / k%r)) 1:/#.
    apply (ler_trans (1%r / k%r * k%r)); first by apply ler_wpmul2l; [smt() | apply h1].
    by have -> : 1%r / k%r * k%r = 1%r by field; smt().
  smt().
rewrite (exp_lin2 _ _ _ EHu Su k%r) //.
have -> : E (dlist md k) EHu = SI.haltp md run.
+ rewrite /EHu (eq_exp _ _ (fun u => 1%r / k%r * bigi predT (fun J' => h (nth witness u J')) 0 k)).
  + by move=> u _ /=; rewrite exp_drange 1:/#.
  rewrite expZ -(sum_E _ _ 0 k 1%r) 1:/#; first by move=> J u _ /=; apply h01.
  rewrite (eq_big_seq _ (fun _ => SI.haltp md run)).
  + move=> J /mem_range hJ /=; rewrite (exp_nth md k J h 1%r) //; smt().
  by rewrite sumri_const 1:/# intmulr; field; smt().
have -> : E (dlist md k) Su = SI.hsum md R run ystar k.
+ rewrite /Su -(sum_E _ _ 0 k 1%r) 1:/#; first by move=> J u _ /=; smt().
  rewrite /SI.hsum; apply eq_big_seq => J _ /=.
  rewrite /SI.dtest mu_dlet_E; apply eq_exp => u _ /=.
  rewrite dmapE /(\o) /= /c /h; case: (J = SI.jst R u ystar) => hj /=.
  + by apply mu_eq => o; rewrite /pred1.
  by rewrite (mu_eq _ _ pred0) // mu0.
by field; smt().
qed.

lemma hasED ['a] (d : 'a distr) (f g : 'a -> real) :
  hasE d f => hasE d g => hasE d (fun x => f x + g x).
proof.
rewrite /hasE => hf hg; have := summableD _ _ hf hg.
by apply eq_summable => x /=; ring.
qed.

lemma hasE_s ['a] (d : 'a distr) (f : 'a -> real) (c : real) :
  (forall x, x \in d => `|f x| <= c) => hasE d f.
proof.
move=> h; apply (SI.hasE_supp (dunit witness) (fun _ => dunit SI.Halt) _ _ d f c) => //.
+ by apply dunit_ll.
by move=> ?; apply dunit_ll.
qed.

(* a weighted mixture of values bounded by k c is bounded by c *)
lemma mix_bound (X : int -> real) (c : real) :
  0%r < Zk => (forall k, 0%r <= wk k) => (forall k, 1 <= k <= Kmix => `|X k| <= k%r * c) =>
  `|1%r / Zk * bigi predT (fun k => wk k * X k) 1 (Kmix + 1)| <= c.
proof.
move=> gt0Z hw hX.
rewrite normrM ger0_norm 1:/#.
apply (ler_trans (1%r / Zk * (Zk * c))); last by have -> : 1%r / Zk * (Zk * c) = c by field; smt().
apply ler_wpmul2l; first smt().
apply (ler_trans _ _ _ (big_normr _ _ _)).
rewrite /Zk mulr_suml; apply ler_sum_seq => k /mem_range hk _ /=.
rewrite normrM ger0_norm 1:hw.
have -> : k%r * wk k * c = wk k * (k%r * c) by ring.
by apply ler_wpmul2l; [apply hw | apply hX; smt()].
qed.

lemma exp_sum7 ['a] (d : 'a distr) (f1 f2 f3 f4 f5 f6 f7 : 'a -> real) :
  hasE d f1 => hasE d f2 => hasE d f3 => hasE d f4 => hasE d f5 => hasE d f6 => hasE d f7 =>
  E d (fun x => f1 x + f2 x + f3 x + f4 x + f5 x + f6 x + f7 x)
  = E d f1 + E d f2 + E d f3 + E d f4 + E d f5 + E d f6 + E d f7.
proof.
move=> h1 h2 h3 h4 h5 h6 h7.
rewrite expD 2:h7; first by do 5! (apply hasED => //).
rewrite expD 2:h6; first by do 4! (apply hasED => //).
rewrite expD 2:h5; first by do 3! (apply hasED => //).
rewrite expD 2:h4; first by do 2! (apply hasED => //).
rewrite expD 2:h3; first by apply hasED.
by rewrite expD.
qed.

lemma sumk01 (F : int -> real) (k : int) : 0 <= k => (forall J, 0%r <= F J <= 1%r) =>
  0%r <= bigi predT F 0 k <= k%r.
proof.
move=> ge0k hF; split; first by apply sumr_ge0_seq => J _ _; smt().
move=> _; apply (ler_trans (bigi predT (fun _ => 1%r) 0 k)).
+ by apply ler_sum_seq => J _ _ /=; smt().
by rewrite sumri_const // intmulr.
qed.

lemma T_bound (md : message distr) (R : relation) (run : message -> SI.outc distr) (k : int) :
  0 <= k => `|bigi predT (fun J => mu (SI.dtest md run k J) (SI.win R ystar J)) 0 k| <= k%r * 1%r.
proof.
move=> ge0k; have := sumk01 (fun J => mu (SI.dtest md run k J) (SI.win R ystar J)) k ge0k _.
+ by move=> J; apply mu01.
smt().
qed.

lemma P_bound (md : message distr) (R : relation) (k : int) :
  0 <= k => `|k%r * E (dlist md k) (SI.priork R)| <= k%r * 1%r.
proof.
move=> ge0k; have := e01 (dlist md k) (SI.priork R) _.
+ move=> u; apply (SI.priork_01 (dunit witness) R (fun _ => dunit SI.Halt)).
  + by apply dunit_ll.
  by move=> ?; apply dunit_ll.
move=> [e0 e1]; rewrite normrM ger0_norm 1:/# ger0_norm //.
by apply ler_wpmul2l; smt().
qed.

lemma H_bound (md : message distr) (R : relation) (run : message -> SI.outc distr) (k : int) :
  1 <= k => `|SI.haltp md run - SI.hsum md R run ystar k| <= k%r * 1%r.
proof.
move=> ge1k.
have hh : 0%r <= SI.haltp md run <= 1%r.
+ by rewrite /SI.haltp; apply e01 => m; apply mu01.
have hs : 0%r <= SI.hsum md R run ystar k <= k%r.
+ by rewrite /SI.hsum; apply sumk01; [smt() | move=> J; apply mu01].
smt().
qed.

(* the per-state values of the reduction's games (Sim_C5_Game: a2r_E,
   a2b_E, hid_E) *)
op fT (md : message distr) (R : relation) (run : message -> SI.outc distr) : real =
  1%r / Zk * bigi predT (fun k => wk k *
    bigi predT (fun J => mu (SI.dtest md run k J) (SI.win R ystar J)) 0 k) 1 (Kmix + 1).
op fP (md : message distr) (R : relation) : real =
  1%r / Zk * bigi predT (fun k => wk k * (k%r * E (dlist md k) (SI.priork R))) 1 (Kmix + 1).
op fH (md : message distr) (R : relation) (run : message -> SI.outc distr) : real =
  1%r / 2%r + 1%r / (2%r * Zk) * bigi predT (fun k => wk k *
    (SI.haltp md run - SI.hsum md R run ystar k)) 1 (Kmix + 1).

op tail : real =
  (1%r - Sim_C5_Core.rho tmix) ^ Kmix * (Kmix%r + 1%r + 1%r / Sim_C5_Core.rho tmix).

section Main.

declare axiom S_correct pk m c d :
  pk \in Gen => (c, d) \in Commit pk m => Verify pk (m, (c, d)).
declare axiom tmix_gt0 : 0%r < tmix.
declare axiom Kmix_ge1 : 1 <= Kmix.

declare module A <: AdvACI {-GI, -A2, -D2, -RealG, -CNM_AP_HidLR.HidLR, -CNM_AP_HidLR.AHL}.

declare axiom init_ll : islossless A.init.
declare axiom commit_ll : islossless A.commit.
declare axiom decommit_ll : islossless A.decommit.
declare axiom init_md : hoare [A.init : true ==> is_lossless res.`1].

(* -------------------------------------------------------------------- *)
(* the distribution of k                                                *)

lemma wk_gt0 k : 0%r < wk k.
proof.
have [r0 r1] := Sim_C5_Core.rho_bounds tmix tmix_gt0.
by rewrite /wk /Sim_C5_Core.w; apply mulr_gt0 => //; apply expr_gt0; smt().
qed.

lemma Zk_gt0 : 0%r < Zk.
proof.
rewrite /Zk big_ltn; first smt(Kmix_ge1).
rewrite /=.
have : 0%r <= bigi predT (fun k => k%r * wk k) 2 (Kmix + 1).
+ by apply sumr_ge0_seq => k /mem_range hk _ /=; apply mulr_ge0; smt(wk_gt0).
smt(wk_gt0).
qed.

lemma sum_pK : bigi predT pK 1 (Kmix + 1) = 1%r.
proof.
rewrite (eq_big_seq _ (fun k => (k%r * wk k) * inv Zk)).
+ by move=> k /mem_range hk; rewrite /pK; smt().
rewrite -(mulr_suml predT (fun k => k%r * wk k)) -/Zk.
by rewrite divrr; smt(Zk_gt0).
qed.

lemma isdistr_pK : isdistr pK.
proof.
rewrite (isdistr_finP (range 1 (Kmix + 1))) ?range_uniq.
+ by move=> k; rewrite /pK mem_range; smt().
+ by move=> k; rewrite /pK; smt(wk_gt0 Zk_gt0 divr_ge0 mulr_ge0).
by rewrite sum_pK.
qed.

lemma dK1E k : mu1 dK k = pK k.
proof. by rewrite /dK (muK pK k isdistr_pK). qed.

lemma supp_dK k : k \in dK => 1 <= k <= Kmix.
proof. by rewrite supportP dK1E /pK; smt(). qed.

lemma exp_dK (f : int -> real) : E dK f = bigi predT (fun k => pK k * f k) 1 (Kmix + 1).
proof.
rewrite /E (sumE_fin _ (range 1 (Kmix + 1))) ?range_uniq.
+ by move=> k /=; rewrite dK1E /pK mem_range; smt().
by apply eq_big_seq => k _ /=; rewrite dK1E; ring.
qed.

lemma dK_ll : is_lossless dK.
proof.
rewrite /is_lossless -(exp_b2r dK predT) exp_dK /predT /= -sum_pK.
by apply eq_big_seq => k _ /=.
qed.

op finF (F : relation -> message -> message -> SI.outc -> bool) (x : CG.st) (a b : message) (o : SI.outc) : bool =
  F x.`2.`2 a b o.

op oc (opd v : bool) (m' : message) : SI.outc =
  if v then SI.Opn m' else if opd then SI.Ref else SI.Halt.

lemma gi_cg (F : relation -> message -> message -> SI.outc -> bool) &m :
  Pr[GI(A).main() @ &m : F GI.rel GI.m GI.n (oc GI.opd GI.v GI.m')]
  = Pr[CG.G(A).main(S1m, S2m, mofm, finF F) @ &m : res].
proof.
byequiv (_ : ={glob A} /\ arg{2} = (S1m, S2m, mofm, finF F)
             ==> _) => //; proc; inline *; wp.
seq 9 10 : (={glob A, r, c, d} /\ pk{1} = x0{2}.`1 /\ GI.m{1} = x0{2}.`2 /\
            GI.m{1} = a{2} /\ GI.n{1} = b{2} /\ GI.rel{1} = x{2}.`2.`2 /\
            fin{2} = finF F /\ !GI.opd{1} /\ !GI.v{1} /\ out{2} = SI.Halt).
+ wp; call (: true); rnd; wp; rnd; rnd; wp; call (: true); rnd; wp; skip => /> &2 pk _ [md rel] /=; rewrite /S1m /S2m /mofm.
if => //.
+ by sp; wp; call (: true); skip => /> &1 &2 *; rewrite /finF /oc /=; smt().
by skip => /> &1 &2 *; rewrite /finF /oc /=.
qed.

lemma Run_ll : islossless Run(A).p.
proof.
proc; seq 2 : true => //.
+ by call commit_ll; rnd; skip => />; smt(Com_ll).
by sp; if; [wp; call decommit_ll | ]; skip.
qed.

lemma gf_cg &m :
  Pr[GF(A).main() @ &m : res]
  = Pr[CG.G(A).main(S1m, S2m, mofm, finF (fun _ (a _ : message) _ => a = ystar)) @ &m : res].
proof.
byequiv (_ : ={glob A} /\ arg{2} = (S1m, S2m, mofm, finF (fun _ (a _ : message) _ => a = ystar))
             ==> _) => //; proc; inline Pre(A).p.
call{2} Run_ll; wp; rnd; rnd; wp; call (: true); rnd; wp; skip => /> &2 pk _ [md rel] /=; rewrite /S1m /S2m /mofm /finF.
qed.

lemma gc_cg &m :
  Pr[GC(A).main() @ &m : res]
  = Pr[CG.G(A).main(S1m, S2m, mofm, finF (fun _ (a b : message) _ => a = b)) @ &m : res].
proof.
byequiv (_ : ={glob A} /\ arg{2} = (S1m, S2m, mofm, finF (fun _ (a b : message) _ => a = b))
             ==> _) => //; proc; inline Pre(A).p.
call{2} Run_ll; wp; rnd; rnd; wp; call (: true); rnd; wp; skip => /> &2 pk _ [md rel] /=; rewrite /S1m /S2m /mofm /finF.
qed.

lemma a2_real &m :
  Pr[CA.G(A).main(S1A, S2A, mofA, finA) @ &m : res]
  <= Pr[RealG(A2(A)).main() @ &m : res].
proof.
byequiv (_ : ={glob A} /\ arg{1} = (S1A, S2A, mofA, finA) ==> res{1} => res{2}) => //.
proc; inline *.
seq 10 11 : (={glob A, r, c, d} /\ x0{1}.`1 = pk{2} /\ pk{2} \in Gen /\ A2.pk{2} = pk{2} /\
            x0{1}.`2 = RealG.m{2} /\ c{2} = RealG.c{2} /\ a{1}.`2 = A2.u{2} /\
            x{1}.`2.`2 = A2.rel{2} /\ fin{1} = finA /\ b{1} = RealG.m{2} /\
            rel{2} = relA A2.rel{2} A2.u{2} /\ out{1} = SI.Halt).
+ wp; call (: true); wp; rnd; wp; rnd; wp; rnd; wp; call (: true); wp; rnd; wp; skip => />.
case (r{1} <> None /\ oget r{1} <> c{1}).
+ rcondt{1} 1; first by auto.
  rcondf{2} 3; first by auto.
  rcondf{2} 6; first by auto.
  wp; call (: true); wp; skip => /> &1 &2 *.
  rewrite /finA /winm /relA /=; smt().
rcondf{1} 1; first by auto.
rcondt{2} 3; first by auto.
rcondt{2} 7; first by auto.
wp; rnd{2}; wp; skip => /> &1 &2 pk_in _.
split; first by apply Com_ll.
move=> _ cd cd_in; rewrite /finA /winm /relA /= => _ ne.
split; last by smt().
by apply S_correct; [ | rewrite -pairS].
qed.

lemma prior_A (R : relation) (u : message list) :
  prior (mdA u) (relA R u) = SI.priork R u.
proof. by rewrite /prior /SI.priork /mdA /relA /pred1. qed.

lemma a2_base &m :
  Pr[Base(A2(A)).main() @ &m : res]
  = Pr[CB.G(A).main(S1A, S2B, mofB, finB') @ &m : res].
proof.
byequiv (_ : ={glob A} /\ arg{2} = (S1A, S2B, mofB, finB') ==> _) => //.
proc; inline Pre(A).p A2(A).init.
call{2} Run_ll; wp; rnd; wp; rnd; wp; call (: true); wp; rnd; wp; skip => />; smt(prior_A).
qed.

lemma hid_ch &m :
  Pr[CNM_AP_HidLR.HidLR(D2(A)).main() @ &m : res]
  = Pr[CH.G(A).main(S1H, S2H, mofH, finH) @ &m : res].
proof.
byequiv (_ : ={glob A} /\ arg{2} = (S1H, S2H, mofH, finH) ==> _) => //.
proc; inline *.
seq 11 10 : (={glob A, r, b} /\ c0{1} = c{2} /\ D2.u{1} = a{2}.`2 /\ D2.j{1} = a{2}.`3 /\
             D2.rel{1} = x{2}.`2.`2 /\ fin{2} = finH /\ out{2} = SI.Halt).
+ wp; call (: true); wp; rnd; wp; rnd; wp; rnd; wp; call (: true); wp; rnd; wp; skip => />.
wp; if{2}.
+ wp; call{2} decommit_ll; skip => /> &1 &2 h; rewrite /finH /=; smt().
by skip => /> &1 &2 h; rewrite /finH /=; smt().
qed.

lemma real_ev &m :
  Pr[GI(A).main() @ &m : GI.v /\ GI.rel GI.m GI.m']
  = Pr[GI(A).main() @ &m : FRl GI.rel GI.m GI.n (oc GI.opd GI.v GI.m')].
proof.
byequiv (_ : ={glob A} ==> ={GI.v, GI.opd, GI.rel, GI.m, GI.n, GI.m'}) => //; first by sim.
by move=> &1 &2 />; rewrite /oc /FRl; case: (GI.v{2}) => //=; case: (GI.opd{2}).
qed.

lemma bl_ev &m :
  Pr[GI(A).main() @ &m : GI.v /\ GI.rel GI.n GI.m']
  = Pr[GI(A).main() @ &m : FBl GI.rel GI.m GI.n (oc GI.opd GI.v GI.m')].
proof.
byequiv (_ : ={glob A} ==> ={GI.v, GI.opd, GI.rel, GI.m, GI.n, GI.m'}) => //; first by sim.
by move=> &1 &2 />; rewrite /oc /FBl; case: (GI.v{2}) => //=; case: (GI.opd{2}).
qed.

lemma vl_ev &m :
  Pr[GI(A).main() @ &m : GI.opd /\ !GI.v]
  = Pr[GI(A).main() @ &m : FVl GI.rel GI.m GI.n (oc GI.opd GI.v GI.m')].
proof.
byequiv (_ : ={glob A} ==> ={GI.v, GI.opd, GI.rel, GI.m, GI.n, GI.m'}) => //; first by sim.
by move=> &1 &2 />; rewrite /oc /FVl; case: (GI.v{2}) => //=; case: (GI.opd{2}).
qed.

(* sim_c5_ideal in terms of the per-state values of the games *)
lemma mix_point (md : message distr) (R : relation) (run : message -> SI.outc distr) :
  is_lossless md => (forall m, is_lossless (run m)) =>
  2%r * tmix * SI.RealS md R run
  <= tmix * (2%r + tmix) * SI.Bl md R run + SI.Vl md run
   + Zk * (fT md R run - fP md R) + 2%r * Zk * (fH md R run - 1%r / 2%r)
   + Zk * mu1 md ystar + (1%r + tmix) ^ 4 * SI.cp md + tail.
proof.
move=> mdll runll.
have h := SI.sim_c5_ideal md R run ystar mdll runll tmix Kmix tmix_gt0 Kmix_ge1.
have e1 : bigi predT (fun k => Sim_C5_Core.w tmix k *
            (bigi predT (fun J => mu (SI.dtest md run k J) (SI.win R ystar J)) 0 k
             - k%r * E (dlist md k) (SI.priork R))) 1 (Kmix + 1)
        = Zk * (fT md R run - fP md R).
+ rewrite /fT /fP -/wk.
  rewrite (eq_big_seq _ (fun k => wk k * bigi predT (fun J => mu (SI.dtest md run k J) (SI.win R ystar J)) 0 k
                                 - wk k * (k%r * E (dlist md k) (SI.priork R)))).
  + by move=> k _ /=; rewrite /wk; ring.
  rewrite -sumrB; pose X := bigi _ _ _ _; pose Y := bigi _ _ _ _.
  by field; smt(Zk_gt0).
have e2 : bigi predT (fun k => Sim_C5_Core.w tmix k *
            (SI.haltp md run - SI.hsum md R run ystar k)) 1 (Kmix + 1)
        = 2%r * Zk * (fH md R run - 1%r / 2%r).
+ rewrite /fH /wk; pose X := bigi _ _ _ _.
  by field; smt(Zk_gt0).
have e3 : bigi predT (fun k => k%r * Sim_C5_Core.w tmix k) 1 (Kmix + 1) = Zk by rewrite /Zk /wk.
move: h; rewrite e1 e2 e3 /tail.
pose a := Zk * (fT md R run - fP md R); pose b := 2%r * Zk * (fH md R run - 1%r / 2%r).
smt().
qed.

(* -------------------------------------------------------------------- *)
(* the distribution level: DP and DR are the reflected distributions of  *)
(* the initialisation and of one run (Reflection.eca); they are declared *)
(* here and supplied by reflection at the end of the section            *)

section Refl.

declare op DP : (glob A) -> unit -> (CG.st * (glob A)) distr.
declare op DR : (glob A) -> pubkey * message -> SI.outc distr.

declare axiom hDP &m0 (po : CG.st * (glob A) -> bool) :
  mu (DP (glob A){m0} tt) po = Pr[Pre(A).p() @ &m0 : po (res, glob A)].
declare axiom hDR &m0 (po : SI.outc -> bool) x :
  mu (DR (glob A){m0} x) po = Pr[Run(A).p(x) @ &m0 : po res].

(* DR is normalised to be lossless everywhere (it is, on memories) *)
declare axiom DR_ll g x : is_lossless (DR g x).

lemma DP_ll &m : is_lossless (DP (glob A){m} tt).
proof.
rewrite /is_lossless hDP; byphoare => //; conseq (: true ==> true) => //.
by proc; call init_ll; rnd; skip; smt(Gen_ll).
qed.

lemma DP_supp &m y : y \in DP (glob A){m} tt => is_lossless y.`1.`2.`1.
proof.
move=> hy.
have h0 : mu (DP (glob A){m} tt) (fun (y : CG.st * (glob A)) => !is_lossless y.`1.`2.`1) = 0%r.
+ rewrite hDP; byphoare => //; hoare.
  by proc; call init_md; rnd; skip.
case: (is_lossless y.`1.`2.`1) => // hn.
have := mu_sub (DP (glob A){m} tt) (pred1 y)
  (fun (y : CG.st * (glob A)) => !is_lossless y.`1.`2.`1) _.
+ by move=> z ->.
rewrite h0 => h1.
have h2 : 0%r < mu1 (DP (glob A){m} tt) y.
+ move: hy; rewrite supportP.
  by have := ge0_mu (DP (glob A){m} tt) (pred1 y); smt().
by move: (ltr_le_trans _ _ _ h2 h1); rewrite ltrr.
qed.

lemma mu_const ['a] (d : 'a distr) (b : bool) : is_lossless d =>
  mu d (fun _ => b) = b2r b.
proof. by move=> ll; case: b => _; [rewrite (_ : (fun _ => true) = predT) // ll | rewrite mu0]. qed.

lemma gi_E (F : relation -> message -> message -> SI.outc -> bool) &m :
  Pr[GI(A).main() @ &m : F GI.rel GI.m GI.n (oc GI.opd GI.v GI.m')]
  = E (DP (glob A){m} tt) (fun (y : CG.st * (glob A)) =>
      E y.`1.`2.`1 (fun a => E y.`1.`2.`1 (fun b =>
        mu (DR y.`2 (y.`1.`1, a)) (F y.`1.`2.`2 a b)))).
proof.
rewrite gi_cg (CG.compose A DP DR &m _ _ _ _ hDP hDR).
by rewrite /S1m /S2m /mofm /finF.
qed.

lemma real_E &m :
  Pr[GI(A).main() @ &m : GI.v /\ GI.rel GI.m GI.m']
  = E (DP (glob A){m} tt) (fun (y : CG.st * (glob A)) =>
      SI.RealS y.`1.`2.`1 y.`1.`2.`2 (fun a => DR y.`2 (y.`1.`1, a))).
proof.
rewrite real_ev (gi_E FRl &m); apply eq_exp => y hy /=.
have mdll := DP_supp &m y hy.
rewrite /SI.RealS; apply eq_exp => a _ /=.
rewrite /FRl /= expC mdll /= -exp_b2r; apply eq_exp => o _ /=.
by rewrite /SI.realf; case: o.
qed.

lemma bl_E &m :
  Pr[GI(A).main() @ &m : GI.v /\ GI.rel GI.n GI.m']
  = E (DP (glob A){m} tt) (fun (y : CG.st * (glob A)) =>
      SI.Bl y.`1.`2.`1 y.`1.`2.`2 (fun a => DR y.`2 (y.`1.`1, a))).
proof.
rewrite bl_ev (gi_E FBl &m); apply eq_exp => y hy /=.
rewrite /SI.Bl; apply eq_exp => a _ /=.
rewrite fubini_mu; apply eq_exp => o _ /=.
rewrite /FBl /SI.bf /SI.q; case: o => [| | z] /=; last by done.
+ by rewrite mu0.
by rewrite mu0.
qed.

lemma vl_E &m :
  Pr[GI(A).main() @ &m : GI.opd /\ !GI.v]
  = E (DP (glob A){m} tt) (fun (y : CG.st * (glob A)) =>
      SI.Vl y.`1.`2.`1 (fun a => DR y.`2 (y.`1.`1, a))).
proof.
rewrite vl_ev (gi_E FVl &m); apply eq_exp => y hy /=.
have mdll := DP_supp &m y hy.
rewrite /SI.Vl; apply eq_exp => a _ /=.
rewrite /FVl /= expC mdll /= -exp_b2r; apply eq_exp => o _ /=.
by rewrite /SI.vf; case: o.
qed.

lemma gf_E &m :
  Pr[GF(A).main() @ &m : res]
  = E (DP (glob A){m} tt) (fun (y : CG.st * (glob A)) => mu1 y.`1.`2.`1 ystar).
proof.
rewrite gf_cg (CG.compose A DP DR &m _ _ _ _ hDP hDR).
apply eq_exp => y hy /=.
have mdll := DP_supp &m y hy.
rewrite /S1m /S2m /mofm /finF /= -exp_b2r; apply eq_exp => a _ /=.
by rewrite (mu_const _ _ (DR_ll _ _)) expC mdll.
qed.

lemma gc_E &m :
  Pr[GC(A).main() @ &m : res]
  = E (DP (glob A){m} tt) (fun (y : CG.st * (glob A)) => SI.cp y.`1.`2.`1).
proof.
rewrite gc_cg (CG.compose A DP DR &m _ _ _ _ hDP hDR).
apply eq_exp => y hy /=.
rewrite /S1m /S2m /mofm /finF /SI.cp mu_dprod_E /=; apply eq_exp => a _ /=.
rewrite -exp_b2r; apply eq_exp => b _ /=.
by rewrite (mu_const _ _ (DR_ll _ _)).
qed.

(* the k-test, averaged over the challenge index, is the sum over worlds *)
lemma test_E (md : message distr) (R : relation) (run : message -> SI.outc distr) (k : int) :
  1 <= k =>
  E (dlist md k) (fun u => E (mdA u) (fun b => mu (run b) (winm R u b)))
  = 1%r / k%r * bigi predT (fun J => mu (SI.dtest md run k J) (SI.win R ystar J)) 0 k.
proof.
move=> ge1k.
rewrite (eq_exp _ _ (fun u => 1%r / k%r *
           bigi predT (fun J => mu (run (nth witness u J)) (winm R u (nth witness u J))) 0 k)).
+ move=> u; rewrite supp_dlist 1:/# => -[szu _].
  rewrite /= /mdA (exp_dmap_b _ _ _ 1%r) /=; first by move=> b; smt(mu01).
  by rewrite szu exp_drange 1:/#.
rewrite expZ -(sum_E _ _ 0 k 1%r) 1:/#; first by move=> J u _ /=; apply mu01.
congr; apply eq_big_seq => J _ /=.
rewrite /SI.dtest mu_dlet_E; apply eq_exp => u _ /=.
rewrite dmapE /(\o) /=; apply mu_eq => o.
by rewrite /SI.win /winm /=; case: o.
qed.

lemma a2r_E &m :
  Pr[CA.G(A).main(S1A, S2A, mofA, finA) @ &m : res]
  = E (DP (glob A){m} tt) (fun (y : CG.st * (glob A)) =>
      1%r / Zk * bigi predT (fun k => wk k *
        bigi predT (fun J => mu (SI.dtest y.`1.`2.`1 (fun a => DR y.`2 (y.`1.`1, a)) k J)
                                (SI.win y.`1.`2.`2 ystar J)) 0 k) 1 (Kmix + 1)).
proof.
rewrite (CA.compose A DP DR &m _ _ _ _ hDP hDR); apply eq_exp => y hy /=.
rewrite /S1A /S2A /mofA /finA /SAd (exp_dlet_b _ _ _ 1%r).
+ by move=> a /=; have := e01 (mdA a.`2) (fun b => mu (DR y.`2 (y.`1.`1, b)) (winm y.`1.`2.`2 a.`2 b)) _; [move=> b; apply mu01 | smt()].
rewrite exp_dK /= mulr_suml; apply eq_big_seq => k /mem_range hk /=.
rewrite (exp_dmap_b _ _ _ 1%r) /=.
+ by move=> a; have := e01 (mdA a.`2) (fun b => mu (DR y.`2 (y.`1.`1, b)) (winm y.`1.`2.`2 a.`2 b)) _; [move=> b; apply mu01 | smt()].
rewrite test_E 1:/# /pK.
have -> : (1 <= k <= Kmix) = true by smt().
rewrite /=; pose T := bigi predT _ 0 k.
by field; smt(Zk_gt0).
qed.

lemma a2b_E &m :
  Pr[CB.G(A).main(S1A, S2B, mofB, finB') @ &m : res]
  = E (DP (glob A){m} tt) (fun (y : CG.st * (glob A)) =>
      1%r / Zk * bigi predT (fun k => wk k *
        (k%r * E (dlist y.`1.`2.`1 k) (SI.priork y.`1.`2.`2))) 1 (Kmix + 1)).
proof.
rewrite (CB.compose A DP DR &m _ _ _ _ hDP hDR); apply eq_exp => y hy /=.
rewrite /S1A /S2B /mofB /finB' /SAd.
rewrite (eq_exp _ _ (fun (a : int * message list) => SI.priork y.`1.`2.`2 a.`2)).
+ move=> a _ /=.
  rewrite (eq_exp _ _ (fun b => b2r b)) => [b _ /=|]; first by apply mu_const; apply DR_ll.
  rewrite exp_b2r dbiasedE /=.
  have := SI.priork_01 (dunit witness) y.`1.`2.`2 (fun _ => dunit SI.Halt) _ _ a.`2.
  + by apply dunit_ll.
  + by move=> ?; apply dunit_ll.
  by move=> h01; rewrite clamp_id.
rewrite (exp_dlet_b _ _ _ 1%r).
+ move=> a; have := SI.priork_01 (dunit witness) y.`1.`2.`2 (fun _ => dunit SI.Halt) _ _ a.`2.
  + by apply dunit_ll.
  + by move=> ?; apply dunit_ll.
  smt().
rewrite exp_dK /= mulr_suml; apply eq_big_seq => k /mem_range hk /=.
rewrite (exp_dmap_b _ _ _ 1%r) /=.
+ move=> a; have := SI.priork_01 (dunit witness) y.`1.`2.`2 (fun _ => dunit SI.Halt) _ _ a.`2.
  + by apply dunit_ll.
  + by move=> ?; apply dunit_ll.
  smt().
rewrite /pK; have -> : (1 <= k <= Kmix) = true by smt().
rewrite /=; pose T := E _ _.
by field; smt(Zk_gt0).
qed.

lemma hid_E &m :
  Pr[CH.G(A).main(S1H, S2H, mofH, finH) @ &m : res]
  = E (DP (glob A){m} tt) (fun (y : CG.st * (glob A)) =>
      1%r / 2%r + 1%r / (2%r * Zk) * bigi predT (fun k => wk k *
        (SI.haltp y.`1.`2.`1 (fun a => DR y.`2 (y.`1.`1, a))
         - SI.hsum y.`1.`2.`1 y.`1.`2.`2 (fun a => DR y.`2 (y.`1.`1, a)) ystar k)) 1 (Kmix + 1)).
proof.
rewrite (CH.compose A DP DR &m _ _ _ _ hDP hDR); apply eq_exp => y hy /=.
have mdll := DP_supp &m y hy.
have b1 : forall (a : int * message list * int * int),
  `|E {0,1} (fun b => mu (DR y.`2 (y.`1.`1, if b then nth witness a.`2 a.`4 else nth witness a.`2 a.`3))
       (fun o => b = (o = SI.Halt /\ a.`3 = SI.jst y.`1.`2.`2 a.`2 ystar)))| <= 1%r.
+ move=> a; have := e01 {0,1} (fun b => mu (DR y.`2 (y.`1.`1, if b then nth witness a.`2 a.`4 else nth witness a.`2 a.`3))
       (fun o => b = (o = SI.Halt /\ a.`3 = SI.jst y.`1.`2.`2 a.`2 ystar))) _; first by move=> b; apply mu01.
  by move=> [h0 h1]; rewrite ger0_norm.
rewrite /S1H /S2H /mofH /finH /SHd (exp_dlet_b _ _ _ 1%r).
+ by move=> a; apply b1.
rewrite exp_dK.
rewrite (eq_big_seq _ (fun k => pK k / 2%r + 1%r / (2%r * Zk) * (wk k *
           (SI.haltp y.`1.`2.`1 (fun a => DR y.`2 (y.`1.`1, a))
            - SI.hsum y.`1.`2.`1 y.`1.`2.`2 (fun a => DR y.`2 (y.`1.`1, a)) ystar k)))).
+ move=> k /mem_range hk /=.
  rewrite (exp_dlet_b _ _ _ 1%r) //.
  rewrite (eq_exp _ _ (fun u => E (drange 0 k `*` drange 0 k) (fun (jj : int * int) =>
     E {0,1} (fun b => mu (DR y.`2 (y.`1.`1, if b then nth witness u jj.`2 else nth witness u jj.`1))
        (fun o => b = (o = SI.Halt /\ jj.`1 = SI.jst y.`1.`2.`2 u ystar)))))).
  + by move=> u _ /=; rewrite (exp_dmap_b _ _ _ 1%r).
  rewrite (hid_k y.`1.`2.`1 y.`1.`2.`2 (fun a => DR y.`2 (y.`1.`1, a)) k mdll _ _).
  + by move=> ?; apply DR_ll.
  + smt().
  rewrite /pK; have -> : (1 <= k <= Kmix) = true by smt().
  rewrite /=; pose H := SI.haltp _ _; pose S := SI.hsum _ _ _ _ _.
  by field; smt(Zk_gt0).
rewrite big_split -(mulr_suml _ pK) sum_pK -(mulr_sumr _ _ _ (1%r / (2%r * Zk))).
by ring.
qed.

(* Lemma "mix" of Appendix A at game level *)
lemma mix_game_r &m :
  2%r * tmix * Pr[GI(A).main() @ &m : GI.v /\ GI.rel GI.m GI.m']
  <= tmix * (2%r + tmix) * Pr[GI(A).main() @ &m : GI.v /\ GI.rel GI.n GI.m']
   + Pr[GI(A).main() @ &m : GI.opd /\ !GI.v]
   + Zk * (Pr[RealG(A2(A)).main() @ &m : res] - Pr[Base(A2(A)).main() @ &m : res])
   + 2%r * Zk * (Pr[CNM_AP_HidLR.HidLR(D2(A)).main() @ &m : res] - 1%r / 2%r)
   + Zk * Pr[GF(A).main() @ &m : res]
   + (1%r + tmix) ^ 4 * Pr[GC(A).main() @ &m : res]
   + tail.
proof.
pose d := DP (glob A){m} tt.
pose gR := fun (y : CG.st * (glob A)) => SI.RealS y.`1.`2.`1 y.`1.`2.`2 (fun a => DR y.`2 (y.`1.`1, a)).
pose gB := fun (y : CG.st * (glob A)) => SI.Bl y.`1.`2.`1 y.`1.`2.`2 (fun a => DR y.`2 (y.`1.`1, a)).
pose gV := fun (y : CG.st * (glob A)) => SI.Vl y.`1.`2.`1 (fun a => DR y.`2 (y.`1.`1, a)).
pose gT := fun (y : CG.st * (glob A)) => fT y.`1.`2.`1 y.`1.`2.`2 (fun a => DR y.`2 (y.`1.`1, a)).
pose gP := fun (y : CG.st * (glob A)) => fP y.`1.`2.`1 y.`1.`2.`2.
pose gH := fun (y : CG.st * (glob A)) => fH y.`1.`2.`1 y.`1.`2.`2 (fun a => DR y.`2 (y.`1.`1, a)).
pose gF := fun (y : CG.st * (glob A)) => mu1 y.`1.`2.`1 ystar.
pose gC := fun (y : CG.st * (glob A)) => SI.cp y.`1.`2.`1.
have hA : E d gT <= Pr[RealG(A2(A)).main() @ &m : res].
+ by rewrite /d /gT /fT -(a2r_E &m); apply a2_real.
have hB : Pr[Base(A2(A)).main() @ &m : res] = E d gP.
+ by rewrite (a2_base &m) (a2b_E &m).
have hH : Pr[CNM_AP_HidLR.HidLR(D2(A)).main() @ &m : res] = E d gH.
+ by rewrite (hid_ch &m) (hid_E &m).
rewrite (real_E &m) (bl_E &m) (vl_E &m) (gf_E &m) (gc_E &m) hB hH -/d -/gR -/gB -/gV -/gF -/gC.
have hw : forall k, 0%r <= wk k by move=> k; have := wk_gt0 k; smt().
have hR : hasE d gR.
+ apply (hasE_s _ _ 1%r) => y _; rewrite /gR /SI.RealS.
  have := e01 y.`1.`2.`1 (fun m => E (DR y.`2 (y.`1.`1, m)) (SI.realf y.`1.`2.`2 m)) _; last smt().
  by move=> m /=; apply e01 => o; rewrite /SI.realf; case: o => //= z; case: (y.`1.`2.`2 m z).
have hB' : hasE d gB.
+ apply (hasE_s _ _ 1%r) => y _; rewrite /gB /SI.Bl.
  have := e01 y.`1.`2.`1 (fun m => E (DR y.`2 (y.`1.`1, m)) (SI.bf y.`1.`2.`1 y.`1.`2.`2)) _; last smt().
  by move=> m /=; apply e01 => o; rewrite /SI.bf; case: o => //= z; rewrite /SI.q; apply mu01.
have hV : hasE d gV.
+ apply (hasE_s _ _ 1%r) => y _; rewrite /gV /SI.Vl.
  have := e01 y.`1.`2.`1 (fun m => E (DR y.`2 (y.`1.`1, m)) SI.vf) _; last smt().
  by move=> m /=; apply e01 => o; rewrite /SI.vf; case: o.
have hT : hasE d gT.
+ apply (hasE_s _ _ 1%r) => y _; rewrite /gT /fT.
  apply (mix_bound _ 1%r Zk_gt0 hw) => k hk; apply T_bound; smt().
have hP : hasE d gP.
+ apply (hasE_s _ _ 1%r) => y _; rewrite /gP /fP.
  apply (mix_bound _ 1%r Zk_gt0 hw) => k hk; apply P_bound; smt().
have hH' : hasE d gH.
+ apply (hasE_s _ _ 1%r) => y _; rewrite /gH /fH.
  have := mix_bound (fun k => SI.haltp y.`1.`2.`1 (fun a => DR y.`2 (y.`1.`1, a))
             - SI.hsum y.`1.`2.`1 y.`1.`2.`2 (fun a => DR y.`2 (y.`1.`1, a)) ystar k) 1%r Zk_gt0 hw _.
  + by move=> k hk /=; apply H_bound; smt().
  pose S := bigi _ _ _ _.
  have -> : 1%r / (2%r * Zk) * S = 1%r / 2%r * (1%r / Zk * S) by field; smt(Zk_gt0).
  pose x := 1%r / Zk * S; smt().
have hF : hasE d gF by apply (hasE_s _ _ 1%r) => y _; rewrite /gF; smt(mu01).
have hC : hasE d gC by apply (hasE_s _ _ 1%r) => y _; rewrite /gC /SI.cp; smt(mu01).
have pt : forall y, y \in d =>
  2%r * tmix * gR y
  <= tmix * (2%r + tmix) * gB y + gV y + Zk * (gT y - gP y) + 2%r * Zk * (gH y - 1%r / 2%r)
   + Zk * gF y + (1%r + tmix) ^ 4 * gC y + tail.
+ move=> y hy; rewrite /gR /gB /gV /gT /gP /gH /gF /gC /=.
  by apply mix_point; [apply (DP_supp &m y hy) | move=> a; apply DR_ll].
pose f1 := fun y => tmix * (2%r + tmix) * gB y.
pose f3 := fun y => Zk * (gT y - gP y).
pose f4 := fun y => 2%r * Zk * (gH y - 1%r / 2%r).
pose f5 := fun y => Zk * gF y.
pose f6 := fun y => (1%r + tmix) ^ 4 * gC y.
pose f7 := fun (_ : CG.st * (glob A)) => tail.
have h1 : hasE d f1 by apply hasEZ.
have h3 : hasE d f3 by apply hasEZ; apply hasED => //; apply/hasEN.
have h4 : hasE d f4 by apply hasEZ; apply hasED => //; apply hasEC.
have h5 : hasE d f5 by apply hasEZ.
have h6 : hasE d f6 by apply hasEZ.
have h7 : hasE d f7 by apply hasEC.
have := in_ler_exp d (fun y => 2%r * tmix * gR y)
  (fun y => f1 y + gV y + f3 y + f4 y + f5 y + f6 y + f7 y) _ _ pt.
+ by apply hasEZ.
+ by do 6! (apply hasED => //).
have e1 : E d f1 = tmix * (2%r + tmix) * E d gB by rewrite /f1 expZ.
have e3 : E d f3 = Zk * (E d gT - E d gP) by rewrite /f3 expZ expB.
have e4 : E d f4 = 2%r * Zk * (E d gH - 1%r / 2%r).
+ by rewrite /f4 expZ expB //; [apply hasEC | rewrite expC (DP_ll &m)].
have e5 : E d f5 = Zk * E d gF by rewrite /f5 expZ.
have e6 : E d f6 = (1%r + tmix) ^ 4 * E d gC by rewrite /f6 expZ.
have e7 : E d f7 = tail by rewrite /f7 expC (DP_ll &m).
rewrite expZ exp_sum7 // e1 e3 e4 e5 e6 e7.
have : 0%r <= Zk by smt(Zk_gt0).
move: hA; pose PR := Pr[RealG(A2(A)).main() @ &m : res].
pose ET := E d gT; pose EP := E d gP; pose Z := Zk.
move=> hA hZ; have : Z * ET <= Z * PR by apply ler_wpmul2l.
smt().
qed.

(* the fallback term: Pr[challenge = ystar]^2 <= Pr[two samples collide] *)
lemma gf_gc_r &m :
  Pr[GF(A).main() @ &m : res] ^ 2 <= Pr[GC(A).main() @ &m : res].
proof.
rewrite (gf_E &m) (gc_E &m).
pose d := DP (glob A){m} tt.
pose f := fun (y : CG.st * (glob A)) => mu1 y.`1.`2.`1 ystar.
pose g := fun (y : CG.st * (glob A)) => SI.cp y.`1.`2.`1.
have f01 : forall y, 0%r <= f y <= 1%r by move=> y; rewrite /f; apply mu01.
have pt : forall y, y \in d => f y ^ 2 <= g y.
+ move=> y hy; have mdll := DP_supp &m y hy.
  rewrite /f /g /SI.cp mu_dprod_E /=.
  rewrite (eq_exp _ _ (fun a => mu1 y.`1.`2.`1 a)) => [a _ /=|]; first by apply mu_eq => b; rewrite /pred1 /#.
  apply (ler_trans (E y.`1.`2.`1 (fun a => if a = ystar then mu1 y.`1.`2.`1 ystar else 0%r))).
  + by rewrite expC_cond; rewrite expr2.
  apply in_ler_exp.
  + by apply (hasE_s _ _ 1%r) => a _ /=; smt(mu01).
  + by apply (hasE_s _ _ 1%r) => a _ /=; smt(mu01).
  by move=> a _ /=; case: (a = ystar) => [-> | _] //; apply ge0_mu.
have hf : hasE d f by apply (hasE_s _ _ 1%r) => y _; smt().
have hf2 : hasE d (fun y => f y ^ 2) by apply (hasE_s _ _ 1%r) => y _ /=; smt(expr2).
pose a := E d f.
have jen : a ^ 2 <= E d (fun y => f y ^ 2).
+ have h0 : 0%r <= E d (fun y => (f y - a) ^ 2).
  + by apply exp_ge0 => y _ /=; apply ge0_sqr.
  have e : E d (fun y => (f y - a) ^ 2) = E d (fun y => f y ^ 2) - a ^ 2.
  + rewrite (eq_exp _ _ (fun y => f y ^ 2 + ((-2%r * a) * f y + a ^ 2))) => [y _ /=|].
    + by ring.
    rewrite expD //; first by apply hasED; [apply hasEZ | apply hasEC].
    rewrite expD; [by apply hasEZ | by apply hasEC |].
    by rewrite expZ expC (DP_ll &m) -/a; ring.
  smt().
apply (ler_trans _ _ _ jen); apply in_ler_exp => //.
+ by apply (hasE_s _ _ 1%r) => y _; rewrite /g /SI.cp; smt(mu01).
qed.

end section Refl.

(* the reflected distributions exist (Reflection.eca) *)
lemma mix_game &m :
  2%r * tmix * Pr[GI(A).main() @ &m : GI.v /\ GI.rel GI.m GI.m']
  <= tmix * (2%r + tmix) * Pr[GI(A).main() @ &m : GI.v /\ GI.rel GI.n GI.m']
   + Pr[GI(A).main() @ &m : GI.opd /\ !GI.v]
   + Zk * (Pr[RealG(A2(A)).main() @ &m : res] - Pr[Base(A2(A)).main() @ &m : res])
   + 2%r * Zk * (Pr[CNM_AP_HidLR.HidLR(D2(A)).main() @ &m : res] - 1%r / 2%r)
   + Zk * Pr[GF(A).main() @ &m : res]
   + (1%r + tmix) ^ 4 * Pr[GC(A).main() @ &m : res]
   + tail.
proof.
elim (RPre.reflection (Pre(A))) => DP0 hDP0.
elim (RRun.reflection_res (Run(A))) => DR0 hDR0.
have ll0 : forall &hr x, is_lossless (DR0 (glob A){hr} x).
+ by move=> &hr x; rewrite /is_lossless hDR0; byphoare => //; conseq Run_ll.
pose DRn := fun g x => if is_lossless (DR0 g x) then DR0 g x else dunit SI.Halt.
apply (mix_game_r DP0 DRn _ _ _ &m).
+ by move=> &m0 po; rewrite hDP0.
+ by move=> &m0 po x; rewrite /DRn ll0 /= hDR0.
by move=> g x; rewrite /DRn; case: (is_lossless (DR0 g x)) => // _; apply dunit_ll.
qed.

lemma gf_gc &m : Pr[GF(A).main() @ &m : res] ^ 2 <= Pr[GC(A).main() @ &m : res].
proof.
elim (RPre.reflection (Pre(A))) => DP0 hDP0.
elim (RRun.reflection_res (Run(A))) => DR0 hDR0.
have ll0 : forall &hr x, is_lossless (DR0 (glob A){hr} x).
+ by move=> &hr x; rewrite /is_lossless hDR0; byphoare => //; conseq Run_ll.
pose DRn := fun g x => if is_lossless (DR0 g x) then DR0 g x else dunit SI.Halt.
apply (gf_gc_r DP0 DRn _ _ _ &m).
+ by move=> &m0 po; rewrite hDP0.
+ by move=> &m0 po x; rewrite /DRn ll0 /= hDR0.
by move=> g x; rewrite /DRn; case: (is_lossless (DR0 g x)) => // _; apply dunit_ll.
qed.

lemma D2_guess_ll : islossless D2(A).guess.
proof. by proc; call commit_ll; skip. qed.

lemma SHd_ll (md : message distr) : is_lossless md => is_lossless (SHd md).
proof.
move=> mdll; apply dlet_ll; first by apply dK_ll.
move=> k /supp_dK hk; apply dlet_ll; first by apply dlist_ll.
move=> u _; apply dmap_ll; apply/dprod_ll; split; apply drange_ll; smt().
qed.

lemma D2_choose_ll : islossless D2(A).choose.
proof.
proc; wp; rnd; call (: true ==> is_lossless res.`1).
+ by conseq init_ll init_md.
by skip => /> mr mdll; apply SHd_ll.
qed.

(* the same bound, with the hiding term as a CNM-AP advantage
   (CNM_AP_HidLR.hidlr_eq): every term is a CNM-AP advantage of an
   adversary built from A, or a property of A's message distribution *)
lemma mix_cnmap &m :
  2%r * tmix * Pr[GI(A).main() @ &m : GI.v /\ GI.rel GI.m GI.m']
  <= tmix * (2%r + tmix) * Pr[GI(A).main() @ &m : GI.v /\ GI.rel GI.n GI.m']
   + Pr[GI(A).main() @ &m : GI.opd /\ !GI.v]
   + Zk * (Pr[RealG(A2(A)).main() @ &m : res] - Pr[Base(A2(A)).main() @ &m : res])
   + 2%r * Zk * (Pr[RealG(CNM_AP_HidLR.AHL(D2(A))).main() @ &m : res]
                 - Pr[Base(CNM_AP_HidLR.AHL(D2(A))).main() @ &m : res])
   + Zk * Pr[GF(A).main() @ &m : res]
   + (1%r + tmix) ^ 4 * Pr[GC(A).main() @ &m : res]
   + tail.
proof.
rewrite -(CNM_AP_HidLR.hidlr_eq S_correct (D2(A)) D2_guess_ll D2_choose_ll &m).
by apply mix_game.
qed.

(* Lemma "mix" of Appendix A: the fallback term is at most sqrt(cp) *)
lemma mix_sqrt &m :
  2%r * tmix * Pr[GI(A).main() @ &m : GI.v /\ GI.rel GI.m GI.m']
  <= tmix * (2%r + tmix) * Pr[GI(A).main() @ &m : GI.v /\ GI.rel GI.n GI.m']
   + Pr[GI(A).main() @ &m : GI.opd /\ !GI.v]
   + Zk * (Pr[RealG(A2(A)).main() @ &m : res] - Pr[Base(A2(A)).main() @ &m : res])
   + 2%r * Zk * (Pr[RealG(CNM_AP_HidLR.AHL(D2(A))).main() @ &m : res]
                 - Pr[Base(CNM_AP_HidLR.AHL(D2(A))).main() @ &m : res])
   + Zk * sqrt Pr[GC(A).main() @ &m : res]
   + (1%r + tmix) ^ 4 * Pr[GC(A).main() @ &m : res]
   + tail.
proof.
have h := mix_cnmap &m.
have hf : Pr[GF(A).main() @ &m : res] <= sqrt Pr[GC(A).main() @ &m : res].
+ have ge0f : 0%r <= Pr[GF(A).main() @ &m : res] by smt(mu_bounded).
  have ge0c : 0%r <= Pr[GC(A).main() @ &m : res] by smt(mu_bounded).
  rewrite -(sqrtsq_ge0 Pr[GF(A).main() @ &m : res]) //.
  by rewrite sqrt_mono; [apply ge0_sqr | done | apply gf_gc].
have : Zk * Pr[GF(A).main() @ &m : res] <= Zk * sqrt Pr[GC(A).main() @ &m : res].
+ by apply ler_wpmul2l; smt(Zk_gt0).
smt().
qed.

end section Main.
