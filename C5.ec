(* C5: abort-corrected comparison-based non-malleability.

   One experiment G; the adversary's view never depends on n.
     Real = Pr[ G : G.v /\ G.rel G.m G.m' ]      (opening of m seen, R on m)
     B    = Pr[ G : G.v /\ G.rel G.n G.m' ]      (same run, R on independent n)
     V    = Pr[ G : G.opd /\ !G.v ]               (opened after seeing d, invalidly)

   As in Laur-Nyberg, the message distribution is chosen first (init) and the
   target relation is chosen together with the adversary's commitment
   (Laur-Nyberg's A4 receives the state sigma2 of A2).  The relation must be
   efficiently computable: it is evaluated by reductions.

   The adversary may halt before the opening (commit returns None; copying the
   challenge commitment counts as halting) and may refuse to open after seeing
   d (decommit returns None).  A refusal counts as an invalid opening.

   A scheme is C5-secure if for every efficient (in particular lossless) A
     Adv(A) = Real - B - sqrt (B * V)
   is negligible.  For adversaries that never open invalidly this is exactly
   the Laur-Nyberg condition Real - B <= negl.
   Losslessness matters: an adversary that diverges instead of opening
   invalidly would hide its aborts from V.                                 *)

pragma Goals:printall.

require import AllCore Distr DBool StdRing StdOrder RealExp.
import RField RealOrder.

type pubkey, message, commitment, openingkey.

type relation = message -> message -> bool.

op Gen : pubkey distr.
op Commit (pk : pubkey) (m : message) : (commitment * openingkey) distr.
op Verify : pubkey -> message * (commitment * openingkey) -> bool.

axiom Gen_ll : is_lossless Gen.
axiom Com_ll pk m : is_lossless (Commit pk m).

module type AdvC5 = {
  proc init(pk : pubkey) : message distr
  proc commit(c : commitment) : (commitment * relation) option
  proc decommit(m : message, d : openingkey) : (openingkey * message) option
}.

module G(A : AdvC5) = {
  var md : message distr
  var rel : relation
  var m, n, m' : message
  var c : commitment
  var c' : commitment option
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
    if (c' <> None /\ oget c' <> c) {
      opd  <- true;
      o    <@ A.decommit(m, d);
      m'   <- (oget o).`2;
      v    <- o <> None /\ Verify pk (m', (oget c', (oget o).`1));
    }
  }
}.
