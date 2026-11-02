(* Sanity check 2: the definition rejects malleable schemes.

   Assume the scheme admits a mauling transformation: from a commitment
   c to m with opening d one can compute a commitment mc c to f m with
   opening md d (e.g. Pedersen with f m = m + 1, or the "constant"
   scheme of Firsov-Laur-Zhuchko with mc = id, md = f).  Then there is
   an adversary with advantage >= 1/2.                                  *)

pragma Goals:printall.

require import AllCore Distr DBool List StdRing StdOrder RealFLub.
require import CNM_AP.
import Biased RField RealOrder.

op m1, m2 : message.

section Hypotheses.

declare axiom m1_neq_m2 : m1 <> m2.

op f : message -> message.
op mc : pubkey -> commitment -> commitment.
op md : pubkey -> openingkey -> openingkey.

declare axiom maul pk m c d :
  pk \in Gen => (c, d) \in Commit pk m => Verify pk (f m, (mc pk c, md pk d)).

(* f moves the challenge messages and keeps them apart *)
declare axiom f_m1 : f m1 <> m1.
declare axiom f_m2 : f m2 <> m2.
declare axiom f_12 : f m1 <> f m2.

module AM : AdvCNM = {
  var pk : pubkey

  proc init(x : pubkey) : message distr * relation = {
    pk <- x;
    return (duniform [m1; m2], fun (n v : message) => v = f n);
  }

  proc commit(c : commitment) : commitment = {
    return mc pk c;
  }

  proc decommit(m : message, d : openingkey) : openingkey * message = {
    return (md pk d, f m);
  }
}.

lemma AM_real &m : Pr[ RealG(AM).main() @ &m : res ] = 1%r.
proof.
byphoare => //; proc; inline *; auto => />.
rewrite Gen_ll /= => pk pk_in.
split; first by rewrite duniform_ll.
move=> _ m; rewrite supp_duniform /= => m_in.
rewrite Com_ll /= => -[c d] cd_in /=.
by rewrite (maul pk m c d) //=; smt(f_m1 f_m2).
qed.

lemma prior_AM :
  prior (duniform [m1; m2]) (fun (n v : message) => v = f n) <= 1%r / 2%r.
proof.
apply flub_le_ub => w /=.
rewrite duniformE /= m1_neq_m2 /=.
smt(f_12).
qed.

lemma AM_base &m : Pr[ Base(AM).main() @ &m : res ] <= 1%r / 2%r.
proof.
have -> : Pr[ Base(AM).main() @ &m : res ]
        = prior (duniform [m1; m2]) (fun (n v : message) => v = f n).
+ byphoare => //; proc; inline *; rnd; wp; rnd; skip => /> *.
  rewrite Gen_ll /= dbiasedE /= clamp_id //.
  by rewrite prior_ge0 prior_le1.
exact prior_AM.
qed.

lemma AM_adv &m :
  1%r / 2%r <= Pr[ RealG(AM).main() @ &m : res ] - Pr[ Base(AM).main() @ &m : res ].
proof. by rewrite AM_real; have := AM_base &m; smt(). qed.

end section Hypotheses.
