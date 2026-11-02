(* The remaining global axioms of the development are the interface of the
   abstract commitment scheme in the base theories C5.ec, CNM_AP.ec and
   CNM_C.ec:
   Gen_ll and Com_ll (key generation and commitment terminate).  All other
   assumptions are section hypotheses (they appear as premises of the
   exported lemmas), or theory parameters that are realised where the
   theory is used (C5_IdealMod.dm_ll in C5_Sat.ec).

   This file instantiates the base theories with a concrete (transparent,
   correct) scheme and realises their axioms, so the interface is
   consistent.                                                            *)

require import AllCore Distr.
require C5 CNM_AP CNM_C.

op tgen : unit distr = dunit tt.
op tcom (pk : unit) (m : bool) : (bool * unit) distr = dunit (m, tt).
op tver (pk : unit) (x : bool * (bool * unit)) : bool = x.`2.`1 = x.`1.

clone C5 as C5_Transparent with
  type pubkey     <- unit,
  type message    <- bool,
  type commitment <- bool,
  type openingkey <- unit,
  op   Gen        <- tgen,
  op   Commit     <- tcom,
  op   Verify     <- tver
proof *.
realize Gen_ll by apply dunit_ll.
realize Com_ll by move=> pk m; apply dunit_ll.

clone CNM_AP as CNM_AP_Transparent with
  type pubkey     <- unit,
  type message    <- bool,
  type commitment <- bool,
  type openingkey <- unit,
  op   Gen        <- tgen,
  op   Commit     <- tcom,
  op   Verify     <- tver
proof *.
realize Gen_ll by apply dunit_ll.
realize Com_ll by move=> pk m; apply dunit_ll.

clone CNM_C as CNM_C_Transparent with
  type pubkey     <- unit,
  type xkey       <- unit,
  type message    <- bool,
  type commitment <- bool,
  type openingkey <- unit,
  op   Gen        <- dunit (tt, tt),
  op   Commit     <- tcom,
  op   Verify     <- tver,
  op   ext        <- fun (_ : unit) (c : bool) => Some c
proof *.
realize Gen_ll by apply dunit_ll.
realize Com_ll by move=> pk m; apply dunit_ll.

(* the instance is correct: honest openings verify *)
lemma transparent_correct pk m c d :
  pk \in tgen => (c, d) \in tcom pk m => tver pk (m, (c, d)).
proof. move=> _; rewrite /tcom /tver supp_dunit /=; smt(). qed.
