(* Negative test: must be REJECTED by check_all.sh. *)
require import AllCore.
lemma bad (x : real) : x * x < 0%r.
proof. smt(). qed.
