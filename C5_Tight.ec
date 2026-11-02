(* Tightness of C5.  The generalised ICTAC'22 adversary AT commits honestly to
   a fixed w0 and opens only when the honest message is w0.  Against EVERY
   correct scheme with collision bound gamma, writing p = mu1 md0 w0,
     Real >= p - gamma,   B <= p^2,   V <= 1 - p.
   Hence for every kappa,
     Real - B - kappa * sqrt (B * V) >= p - p^2 - gamma - kappa * p * sqrt (1 - p),
   which is positive for kappa < 1 and p small (with gamma << p).  So no
   definition  Real <= B + kappa * sqrt (B * V) + negl  with kappa < 1 can be
   satisfied: the square-root correction in C5 is optimal.               *)

pragma Goals:printall.

require import AllCore Distr DBool StdRing StdOrder RealExp.
require import C5.
import RField RealOrder.

op md0 : message distr.
op w0, wbad : message.

section Hypotheses.

declare axiom md0_ll : is_lossless md0.
declare axiom wbad_w0 : wbad <> w0.

op p = mu1 md0 w0.

op gamma : real.

declare axiom Com_correct pk m c d :
  pk \in Gen => (c, d) \in Commit pk m => Verify pk (m, (c, d)).

declare axiom Com_coll pk m c :
  mu (Commit pk m) (fun (cd : commitment * openingkey) => cd.`1 = c) <= gamma.

module AT : AdvC5 = {
  var pk : pubkey
  var c' : commitment
  var d' : openingkey

  proc init(x : pubkey) : message distr = {
    pk <- x;
    return md0;
  }

  proc commit(y : commitment) : (commitment * relation) option = {
    (c', d') <$ Commit pk w0;
    return Some (c', fun (n v : message) => n = w0 /\ v = w0);
  }

  proc decommit(m : message, d : openingkey) : (openingkey * message) option = {
    return Some (if m = w0 then (d', w0) else (d', wbad));
  }
}.

module S1 = {
  proc main() : bool = {
    var m;
    m <$ md0;
    return m = w0;
  }
}.

module S2 = {
  proc main() : bool = {
    var m, n;
    m <$ md0;
    n <$ md0;
    return m = w0 /\ n = w0;
  }
}.

lemma S1_pr &m : Pr[ S1.main() @ &m : res ] = p.
proof. by byphoare => //; proc; rnd (pred1 w0); skip. qed.

lemma S2_pr &m : Pr[ S2.main() @ &m : res ] = p * p.
proof.
byphoare => //; proc.
seq 1 : (m = w0) p p (1%r - p) 0%r => //.
+ by rnd (pred1 w0); skip.
+ by rnd (pred1 w0); skip => />.
by hoare; rnd; skip => /#.
qed.

(* ------------------------------------------------------------------ *)

lemma G_mw0 &m : Pr[ G(AT).main() @ &m : G.m = w0 ] = p.
proof.
rewrite -(S1_pr &m); byequiv => //; proc; inline *.
wp; rnd{1}; wp; rnd{1}; rnd{1}; rnd; wp; rnd{1}; skip => />.
smt(Gen_ll Com_ll md0_ll).
qed.

lemma G_copy &m : Pr[ G(AT).main() @ &m : AT.c' = G.c ] <= gamma.
proof.
byphoare => //; proc; inline *.
seq 8 : true 1%r gamma 0%r 0%r => //.
+ wp; rnd (fun (cd : commitment * openingkey) => cd.`1 = G.c).
  by skip => /> &hr; apply Com_coll.
by move=> _; have := Com_coll witness witness witness; smt(ge0_mu).
qed.

lemma real_lb &m :
  p - gamma <= Pr[ G(AT).main() @ &m : G.v /\ G.rel G.m G.m' ].
proof.
have h1 : Pr[ G(AT).main() @ &m : G.m = w0 ]
       <= Pr[ G(AT).main() @ &m : (G.v /\ G.rel G.m G.m') \/ AT.c' = G.c ].
+ byequiv (_: ={glob AT} ==> G.m{1} = w0 => ((G.v /\ G.rel G.m G.m') \/ AT.c' = G.c){2}) => //.
  proc; inline *; auto => /> pk pk_in m _ n _ [c d] _ [c' d'] cd_in.
  by move=> /= _ _; apply (Com_correct pk w0 c' d' pk_in cd_in).
have h2 : Pr[ G(AT).main() @ &m : (G.v /\ G.rel G.m G.m') \/ AT.c' = G.c ]
       <= Pr[ G(AT).main() @ &m : G.v /\ G.rel G.m G.m' ] + Pr[ G(AT).main() @ &m : AT.c' = G.c ].
+ rewrite Pr[mu_or].
  have : 0%r <= Pr[ G(AT).main() @ &m : (G.v /\ G.rel G.m G.m') /\ AT.c' = G.c ] by rewrite Pr[mu_ge0].
  smt().
have := G_mw0 &m; have := G_copy &m; smt().
qed.

lemma bl_ub &m : Pr[ G(AT).main() @ &m : G.v /\ G.rel G.n G.m' ] <= p * p.
proof.
rewrite -(S2_pr &m); byequiv => //; proc; inline *.
wp; rnd{1}; wp; rnd{1}; rnd; rnd; wp; rnd{1}; skip => />.
smt(Gen_ll Com_ll wbad_w0).
qed.

lemma vl_ub &m : Pr[ G(AT).main() @ &m : G.opd /\ !G.v ] <= 1%r - p.
proof.
have -> : 1%r - p = Pr[ S1.main() @ &m : !res ].
+ byphoare => //; proc; rnd (predC (pred1 w0)); skip => />.
  by rewrite mu_not md0_ll.
byequiv => //; proc; inline *.
wp; rnd{1}; wp; rnd{1}; rnd{1}; rnd; wp; rnd{1}; skip => />.
split; first by apply Gen_ll.
move=> _ pk pk_in m _; split; first by apply md0_ll.
move=> _ n _; split; first by apply Com_ll.
move=> _ cd _; split; first by apply Com_ll.
move=> _ cd2 cd2_in _; case: (m = w0) => //= ->> /=.
by have := Com_correct pk w0 cd2.`1 cd2.`2 pk_in; rewrite -pairS => /(_ cd2_in) ->.
qed.

lemma c5_tight &m (kappa : real) : 0%r <= kappa =>
     p - p * p - gamma - kappa * (p * sqrt (1%r - p))
  <= Pr[ G(AT).main() @ &m : G.v /\ G.rel G.m G.m' ]
   - Pr[ G(AT).main() @ &m : G.v /\ G.rel G.n G.m' ]
   - kappa * sqrt (Pr[ G(AT).main() @ &m : G.v /\ G.rel G.n G.m' ]
                 * Pr[ G(AT).main() @ &m : G.opd /\ !G.v ]).
proof.
move=> ge0k.
have h1 := real_lb &m; have h2 := bl_ub &m; have h3 := vl_ub &m.
have ge0B : 0%r <= Pr[ G(AT).main() @ &m : G.v /\ G.rel G.n G.m' ] by rewrite Pr[mu_ge0].
have ge0V : 0%r <= Pr[ G(AT).main() @ &m : G.opd /\ !G.v ] by rewrite Pr[mu_ge0].
have ge0p : 0%r <= p by rewrite /p ge0_mu.
have le1p : p <= 1%r by rewrite /p le1_mu.
have hBV : Pr[ G(AT).main() @ &m : G.v /\ G.rel G.n G.m' ] * Pr[ G(AT).main() @ &m : G.opd /\ !G.v ]
        <= (p * p) * (1%r - p) by apply ler_pmul.
have hs : sqrt (Pr[ G(AT).main() @ &m : G.v /\ G.rel G.n G.m' ] * Pr[ G(AT).main() @ &m : G.opd /\ !G.v ])
       <= p * sqrt (1%r - p).
+ have -> : p * sqrt (1%r - p) = sqrt ((p * p) * (1%r - p)).
  + by rewrite sqrtM 1:mulr_ge0 // 1:/# -expr2 sqrtsq_ge0.
  by rewrite sqrt_mono 1:mulr_ge0 // mulr_ge0 1:mulr_ge0 //#.
have : kappa * sqrt (Pr[ G(AT).main() @ &m : G.v /\ G.rel G.n G.m' ] * Pr[ G(AT).main() @ &m : G.opd /\ !G.v ])
    <= kappa * (p * sqrt (1%r - p)) by apply ler_wpmul2l.
smt().
qed.

end section Hypotheses.
