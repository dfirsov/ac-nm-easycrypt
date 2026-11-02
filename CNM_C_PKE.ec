(* Satisfiability of CNM-C: every perfectly correct public-key encryption
   scheme that is NM-CPA secure (comparison-based, in the style of
   Bellare-Desai-Pointcheval-Rogaway; single ciphertext, relation chosen in
   advance) yields a CNM-C commitment scheme:

     commit = encrypt,   opening = encryption randomness,
     extraction key = secret key,   ext = decrypt.

   The two advantages are equal, adversary for adversary.                *)

pragma Goals:printall.

require import AllCore Distr DBool.
require CNM_C.

type pk_t, sk_t, ptxt, ctxt, rand.

op kg : (pk_t * sk_t) distr.
op dr : rand distr.
op enc : pk_t -> ptxt -> rand -> ctxt.
op dec : sk_t -> ctxt -> ptxt option.

section Hypotheses.

declare axiom kg_ll : is_lossless kg.
declare axiom dr_ll : is_lossless dr.

(* perfect correctness *)
declare axiom correct pk sk m r : (pk, sk) \in kg => dec sk (enc pk m r) = Some m.

module type AdvNMCPA = {
  proc init(pk : pk_t) : ptxt distr * (ptxt -> ptxt -> bool)
  proc attack(y : ctxt) : ctxt
}.

module NMCPA(B : AdvNMCPA) = {
  proc main(b : bool) : bool = {
    var pk, sk, md, rel, x0, x1, r, y, y';
    (pk, sk)   <$ kg;
    (md, rel)  <@ B.init(pk);
    x0         <$ md;
    x1         <$ md;
    r          <$ dr;
    y          <- enc pk x0 r;
    y'         <@ B.attack(y);
    return y' <> y /\ dec sk y' <> None /\ rel (if b then x1 else x0) (oget (dec sk y'));
  }
}.

clone import CNM_C as C with
  type pubkey     <- pk_t,
  type xkey       <- sk_t,
  type message    <- ptxt,
  type commitment <- ctxt,
  type openingkey <- rand,
  op Gen          <- kg,
  op Commit       <- fun pk m => dmap dr (fun r => (enc pk m r, r)),
  op Verify       <- fun pk (x : ptxt * (ctxt * rand)) => enc pk x.`1 x.`2.`2 = x.`2.`1,
  op ext          <- dec
proof *.
realize Gen_ll by exact kg_ll.
realize Com_ll by move=> pk m; apply/dmap_ll/dr_ll.
realize S_correct.
by move=> pk xk m c d _ /=; rewrite supp_dmap => -[r [_ /= [-> ->]]].
qed.
realize ext_binding.
by move=> pk xk m c d h /= <-; apply (correct pk xk m d h).
qed.

module BofA(A : AdvNMC) : AdvNMCPA = {
  proc init(pk : pk_t) : ptxt distr * (ptxt -> ptxt -> bool) = {
    var r;
    r <@ A.init(pk);
    return r;
  }

  proc attack(y : ctxt) : ctxt = {
    var c';
    c' <@ A.commit(y);
    return c';
  }
}.

section.

declare module A <: AdvNMC {-NMC}.

lemma cnmc_eq_nmcpa &m b :
  Pr[ NMC(A).main(b) @ &m : res ] = Pr[ NMCPA(BofA(A)).main(b) @ &m : res ].
proof.
byequiv => //; proc; inline *.
wp; call (: true); wp.
rnd (fun (cd : ctxt * rand) => cd.`2) (fun r => (enc pk{1} NMC.m{1} r, r)).
rnd; rnd; wp; call (: true); auto => /> [pk sk] _ /= r x0 _ x1 _.
split => [r' _ | _].
+ by rewrite dmap1E /(\o) /pred1; apply mu_eq => r'' /= /#.
move=> [c d]; rewrite supp_dmap => -[r' [r'_in /= [-> ->]]] /=.
by rewrite r'_in.
qed.

lemma cnmc_adv_eq &m :
    Pr[ NMC(A).main(false) @ &m : res ] - Pr[ NMC(A).main(true) @ &m : res ]
  = Pr[ NMCPA(BofA(A)).main(false) @ &m : res ] - Pr[ NMCPA(BofA(A)).main(true) @ &m : res ].
proof. by rewrite !(cnmc_eq_nmcpa &m). qed.

end section.

end section Hypotheses.
