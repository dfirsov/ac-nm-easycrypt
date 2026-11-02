(* Averaging over the intermediate state of an abstract two-phase adversary.

   P.ex1 is run, then m <$ dm x, then P.ex2(x, m), then n <$ dm x.  Using the
   standard library's reflection (Firsov-Unruh, CPP'22) for each phase we get
   distributions D1 (result and state after ex1) and D2 (result of ex2 from a
   given state), and

     Pr[ G0(P) : ev res ] = E (D1 g0) (fun xg => E (dm xg.`1) (fun m =>
                              E (D2 xg.`2 (xg.`1, m)) (fun b =>
                                mu (dm xg.`1) (fun n => ev (xg.`1, m, b, n))))).

   Only the adversary's phases are reflected; m and n stay syntactic, so the
   per-state structure needed by C5 (independence of m and n) is free.      *)

pragma Goals:printall.

require import AllCore Distr DBool RealSeries StdRing StdOrder.
require Reflection.
import RField RealOrder.

type xt, msg.

op dm : xt -> msg distr.   (* the message distribution may depend on the first phase *)

module type Two = {
  proc ex1() : xt
  proc ex2(x : xt, m : msg) : bool
}.

module W1(P : Two) = {
  proc p(u : unit) : xt = { var x; x <@ P.ex1(); return x; }
}.

module W2(P : Two) = {
  proc p(a : xt * msg) : bool = { var b; b <@ P.ex2(a.`1, a.`2); return b; }
}.

module G0(P : Two) = {
  proc main() : xt * msg * bool * msg = {
    var x, m, b, n;
    x <@ W1(P).p();
    m <$ dm x;
    b <@ W2(P).p(x, m);
    n <$ dm x;
    return (x, m, b, n);
  }
}.

clone Reflection as R1 with type Proc.a <- unit, type Proc.r <- xt.
clone Reflection as R2 with type Proc.a <- xt * msg, type Proc.r <- bool.

(* expectation form of a dlet *)
lemma mu_dlet_exp ['a 'b] (d : 'a distr) (F : 'a -> 'b distr) (P : 'b -> bool) :
  mu (dlet d F) P = E d (fun a => mu (F a) P).
proof. by rewrite dletE /E; apply eq_sum => a /=; rewrite mulrC. qed.

section.

declare module P <: Two.

local module S = {
  proc s1(d : (xt * glob P) distr) : xt * glob P = { var xg; xg <$ d; return xg; }
  proc s2(d : bool distr) : bool = { var b; b <$ d; return b; }

  proc main(d1 : (xt * glob P) distr, d2 : glob P -> xt * msg -> bool distr) = {
    var xg, m, b, n;
    xg <@ s1(d1);
    m  <$ dm xg.`1;
    b  <@ s2(d2 xg.`2 (xg.`1, m));
    n  <$ dm xg.`1;
    return (xg.`1, m, b, n);
  }

  proc main2(d1 : (xt * glob P) distr, d2 : glob P -> xt * msg -> bool distr) = {
    var xg, m, b, n;
    xg <$ d1;
    m  <$ dm xg.`1;
    b  <$ d2 xg.`2 (xg.`1, m);
    n  <$ dm xg.`1;
    return (xg.`1, m, b, n);
  }

  proc one(d : ((xt * glob P) * msg * bool * msg) distr) = {
    var r;
    r <$ d;
    return (r.`1.`1, r.`2, r.`3, r.`4);
  }
}.

lemma averaging :
  exists (D1 : glob P -> (xt * glob P) distr) (D2 : glob P -> xt * msg -> bool distr),
  (forall &m M, mu (D1 (glob P){m}) M = Pr[ W1(P).p() @ &m : M (res, glob P) ]) /\
  (forall &m M a, mu (D2 (glob P){m} a) M = Pr[ W2(P).p(a) @ &m : M res ]) /\
  forall &m (ev : xt * msg * bool * msg -> bool),
    Pr[ G0(P).main() @ &m : ev res ]
    = E (D1 (glob P){m}) (fun (xg : xt * glob P) => E (dm xg.`1) (fun m =>
        E (D2 xg.`2 (xg.`1, m)) (fun b =>
          mu (dm xg.`1) (fun n => ev (xg.`1, m, b, n))))).
proof.
elim (R1.reflection (W1(P))) => D1 hD1.
elim (R2.reflection_res (W2(P))) => D2 hD2.
exists (fun g => D1 g ()) D2; split.
+ by move=> &m M /=; rewrite (hD1 &m M tt).
split; first by move=> &m M a; apply (hD2 &m M a).
move=> &m ev.
(* phase 1: the call to ex1 is a sample from D1 *)
have eq1 : equiv[ W1(P).p ~ S.s1 : d{2} = D1 (glob P){1} () ==> (res, glob P){1} = res{2} ].
+ bypr ((res, glob P){1}) (res{2}) => // &1 &2 a hd.
  have h1 := hD1 &1 (pred1 a) arg{1}.
  have -> : Pr[ S.s1(arg{2}) @ &2 : res = a ] = mu1 arg{2} a.
  + by byphoare (: arg = arg{2} ==> _) => //; proc; rnd; skip.
  have eu : arg{1} = tt by smt().
  by rewrite hd -eu h1.
(* phase 2: the call to ex2 is a sample from D2 *)
have eq2 : equiv[ W2(P).p ~ S.s2 : d{2} = D2 (glob P){1} a{1} ==> ={res} ].
+ bypr (res{1}) (res{2}) => // &1 &2 a hd.
  have h2 := hD2 &1 (pred1 a) arg{1}.
  have -> : Pr[ S.s2(arg{2}) @ &2 : res = a ] = mu1 arg{2} a.
  + by byphoare (: arg = arg{2} ==> _) => //; proc; rnd; skip.
  by rewrite hd h2.
have -> : Pr[ G0(P).main() @ &m : ev res ] = Pr[ S.main(D1 (glob P){m} tt, D2) @ &m : ev res ].
+ byequiv => //; proc.
  rnd; call eq2; rnd; call eq1; skip => /> /#.
pose d1 := D1 (glob P){m} tt.
pose dd := dlet d1 (fun (xg : xt * glob P) => dlet (dm xg.`1) (fun m =>
             dlet (D2 xg.`2 (xg.`1, m)) (fun b => dmap (dm xg.`1) (fun n => (xg, m, b, n))))).
have -> : Pr[ S.main(d1, D2) @ &m : ev res ] = Pr[ S.one(dd) @ &m : ev res ].
+ have -> : Pr[ S.main(d1, D2) @ &m : ev res ] = Pr[ S.main2(d1, D2) @ &m : ev res ].
  + by byequiv => //; proc; inline *; auto.
  byequiv => //; proc.
  by wp; rnd : 0 0; skip => />; rewrite /dd dmap_id.
have -> : Pr[ S.one(dd) @ &m : ev res ]
        = mu dd (fun (r : (xt * glob P) * msg * bool * msg) => ev (r.`1.`1, r.`2, r.`3, r.`4)).
+ by byphoare (: arg = dd ==> _) => //; proc; rnd; skip.
rewrite mu_dlet_exp /d1 /=; apply eq_exp => xg _ /=.
rewrite mu_dlet_exp; apply eq_exp => m _ /=.
rewrite mu_dlet_exp; apply eq_exp => b _ /=.
by rewrite dmapE.
qed.

end section.
