(* Vector AC-NM (C5): the adversary outputs a vector of commitments, all
   different from the challenge c, and later opens all of them; the opening
   is valid only if every component verifies (all-or-nothing, as in
   Laur-Pasini PKC'08: "a game is ended with bot if any operation leads to
   bot").  The relation takes the challenge message and the vector of
   opened messages.

     Real = Pr[ G : G.v /\ G.rel G.m G.m' ],  B = Pr[ G : G.v /\ G.rel G.n G.m' ],
     V    = Pr[ G : G.opd /\ !G.v ],          Adv = Real - B - sqrt (B * V).

   Results for the vector form, obtained by instantiation:
   - the filtering lemma: V.c5_filter (from C5_Gen.ec);
   - soundness for ideal commitments: C5_IdealMod.c5_mod is generic in the
     type wt of the opened value, so it applies with wt = message list.   *)

pragma Goals:printall.

require import AllCore List Distr.
require C5_Gen.

type pubkey, message, commitment, openingkey.

op Gen : pubkey distr.
op Commit (pk : pubkey) (m : message) : (commitment * openingkey) distr.
op Verify : pubkey -> message * (commitment * openingkey) -> bool.

(* every output commitment differs from the challenge *)
op vfresh (c : commitment) (cs : commitment list) : bool =
  all (fun c' => c' <> c) cs.

(* every component opens validly *)
op vverify (pk : pubkey) (x : message list * (commitment list * openingkey list)) : bool =
  size x.`1 = size x.`2.`1 /\ size x.`2.`2 = size x.`2.`1 /\
  all (Verify pk) (zip x.`1 (zip x.`2.`1 x.`2.`2)).

clone import C5_Gen as V with
  type pubkey     <- pubkey,
  type message    <- message,
  type commitment <- commitment,
  type openingkey <- openingkey,
  type ocom       <- commitment list,
  type oopen      <- openingkey list,
  type oval       <- message list,
  op   Gen        <- Gen,
  op   Commit     <- Commit,
  op   Vfy        <- vverify,
  op   fresh      <- vfresh.

(* the vector filtering lemma, as instantiated *)
print V.c5_filter.
