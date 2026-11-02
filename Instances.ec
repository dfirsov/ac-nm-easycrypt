(* The remaining global axioms of the development are the interface of the
   abstract commitment scheme in the base theories C5.ec and CNM_AP.ec:
   Gen_ll and Com_ll (key generation and commitment terminate).  All other
   assumptions are section hypotheses (they appear as premises of the
   exported lemmas), or theory parameters that are realised where the
   theory is used (C5_IdealMod.dm_ll in C5_Sat.ec, CNM_C's axioms in
   CNM_C_PKE.ec).

   This file instantiates both base theories with a concrete (transparent,
   correct) scheme and realises their axioms, so the interface is
   consistent.                                                            *)

require import AllCore Distr.
require C5 CNM_AP.

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

(* the instance is correct: honest openings verify *)
lemma transparent_correct pk m c d :
  pk \in tgen => (c, d) \in tcom pk m => tver pk (m, (c, d)).
proof. move=> _; rewrite /tcom /tver supp_dunit /=; smt(). qed.
