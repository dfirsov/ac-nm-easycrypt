(* Vaudenay's SAS message authentication from C5: Laur-Asokan-Nyberg
   (ePrint 2005/424), Theorem 5, with C5 in place of their (unsatisfiable)
   comparison-based non-malleability.

   Protocol (one-way authentication of m_a from Alice to Bob), with Charlie
   in the middle:
     1. Alice: r_a <$ K, (c, d) <$ Commit pk (m_a, r_a), sends (m_a, c);
        Charlie delivers (m_a', c') to Bob.
     2. Bob: r_b <$ K, sends r_b; Charlie delivers r_b' to Alice.
     3. Alice sends d; Charlie delivers d' to Bob, who opens c' to y and
        checks that its data part is m_a'.
     4. SAS: Alice shows r_a xor r_b', Bob shows sndm y xor r_b; Bob accepts
        iff they coincide.
   forge: Bob accepts a message m_a' <> m_a.

   As in LAN05 (and C5_ManaIV.ec) the game covers the normal execution
   paths with c' <> c, where c' and r_b' are fixed before d is released;
   the other paths are handled by hiding and binding.

   LAN05, Thm 5:  Pr[forge /\ norm] <= 2^-l Pr[norm] + eps_nm (+ hiding, binding).
   Here (sas_c5), with eps the regularity of xor on keys (2^-l for uniform
   l-bit keys):
     Pr[forge /\ norm] <= eps Pr[norm] / (1 - eps)^2
                          + 2 Adv_C5(Filt(Red C)) / (1 - eps).            *)

pragma Goals:printall.

require import AllCore Distr DBool StdRing StdOrder RealExp.
require import C5 C5_Filter.
import RField RealOrder.

type data, key.

op dkey : key distr.                       (* the SAS key space *)
op ( ^^ ) : key -> key -> key.             (* xor *)
op pair : data -> key -> message.          (* the committed value (m, r) *)
op fstm : message -> data.
op sndm : message -> key.
op eps : real.

section Hypotheses.

declare axiom dkey_ll : is_lossless dkey.
declare axiom fstm_pair a r : fstm (pair a r) = a.
declare axiom sndm_pair a r : sndm (pair a r) = r.
(* xor is eps-regular on dkey; eps = 2^-l for uniform l-bit keys *)
declare axiom key_reg a b : mu dkey (fun r => r ^^ a = b) <= eps.

module type Charlie = {
  proc init(pk : pubkey) : data
  proc a2b(ma : data, c : commitment) : (data * commitment) option
  proc b2a(rb : key) : key
  proc open(d : openingkey) : (openingkey * message) option
}.

module Sas(C : Charlie) = {
  var ma, ma' : data
  var ra, rb, rb' : key
  var c, c' : commitment
  var y : message
  var norm, forge : bool

  proc main() : unit = {
    var pk, d, r, o;
    pk         <$ Gen;
    ma         <@ C.init(pk);
    ra         <$ dkey;
    (c, d)     <$ Commit pk (pair ma ra);
    r          <@ C.a2b(ma, c);
    norm       <- false;
    forge      <- false;
    if (r <> None /\ (oget r).`2 <> c) {
      norm       <- true;
      (ma', c')  <- oget r;
      rb         <$ dkey;
      rb'        <@ C.b2a(rb);
      o          <@ C.open(d);
      y          <- (oget o).`2;
      forge      <- o <> None /\ Verify pk (y, (c', (oget o).`1))
                    /\ fstm y = ma' /\ ma' <> ma
                    /\ ra ^^ rb' = sndm y ^^ rb;
    }
  }
}.

(* LAN05's reduction, as a C5 adversary *)
module Red(C : Charlie) = {
  var ma : data

  proc init(pk : pubkey) : message distr = {
    ma <@ C.init(pk);
    return dmap dkey (pair ma);
  }

  proc commit(c : commitment) : (commitment * relation) option = {
    var r, ma', c', rb, rb', out;
    r   <@ C.a2b(ma, c);
    out <- None;
    if (r <> None /\ (oget r).`2 <> c) {
      (ma', c') <- oget r;
      rb        <$ dkey;
      rb'       <@ C.b2a(rb);
      out       <- Some (c', fun x y => fstm y = ma' /\ ma' <> ma
                                        /\ sndm x ^^ rb' = sndm y ^^ rb);
    }
    return out;
  }

  proc decommit(m : message, d : openingkey) : (openingkey * message) option = {
    var o;
    o <@ C.open(d);
    return o;
  }
}.

declare module C <: Charlie {-G, -Filt, -Red, -Sas}.

local equiv sas_red : Sas(C).main ~ G(Red(C)).main :
  ={glob C} ==> Sas.forge{1} = (G.v /\ G.rel G.m G.m'){2} /\ Sas.norm{1} = G.opd{2}.
proof.
proc; inline Red(C).init Red(C).commit Red(C).decommit.
seq 5 9 : (={glob C, pk, d} /\ Sas.ma{1} = Red.ma{2} /\
           G.m{2} = pair Sas.ma{1} Sas.ra{1} /\ Sas.c{1} = G.c{2} /\
           c{2} = G.c{2} /\ r{1} = r0{2}).
+ call (: true); wp; rnd; rnd{2}.
  rnd (fun r => pair Sas.ma{1} r) (fun m => sndm m).
  wp; call (: true); wp; rnd; skip => /> pk _ ma.
  split.
  + by move=> m; rewrite supp_dmap => -[r [_ ->]]; rewrite sndm_pair.
  move=> h1; split.
  + move=> m; rewrite supp_dmap => -[r0 [_ ->]].
    rewrite dmap1E /(\o) /pred1 sndm_pair.
    by apply mu_eq => x /=; smt(sndm_pair).
  move=> h2 r r_in; split; first by rewrite supp_dmap; exists r.
  move=> _; split; first by rewrite sndm_pair.
  by move=> _; apply dmap_ll; apply dkey_ll.
sp 2 0; if{1}.
+ rcondt{2} 2; first by auto.
  rcondt{2} 12; first by auto; call (: true); auto.
  wp; call (: true); wp; call (: true); rnd; wp; skip => />.
  by move=> &1 &2 _ _ rb _ rb' o; rewrite sndm_pair; smt().
rcondf{2} 2; first by auto.
rcondf{2} 8; first by auto.
by auto => />.
qed.


local lemma red_md_ll : hoare[ Red(C).init : true ==> is_lossless res ].
proof. by proc; call (: true); auto => /> *; smt(dmap_ll dkey_ll). qed.

local lemma red_sparse : hoare[ G(Red(C)).main : true ==> G.opd => sparse eps G.md G.rel ].
proof.
proc; inline Red(C).init Red(C).commit Red(C).decommit.
seq 10 : (G.md = dmap dkey (pair Red.ma) /\ out = None).
+ by wp; call (: true); auto; call (: true); auto.
seq 1 : (G.md = dmap dkey (pair Red.ma) /\
         (out <> None => sparse eps (dmap dkey (pair Red.ma)) (oget out).`2)).
+ if; last by auto.
  wp; call (: true); rnd; wp; skip => /> &hr _ _ rb _ rb' y /=.
  rewrite dmapE /(\o) /=.
  apply (ler_trans (mu dkey (fun r => r ^^ rb' = sndm y ^^ rb))).
  + by apply mu_sub => r /=; rewrite sndm_pair.
  by apply key_reg.
sp; if; last by auto => /> /#.
by wp; call (: true); auto => /> /#.
qed.

lemma sas_c5 &m : 0%r <= eps => eps < 1%r =>
  Pr[ Sas(C).main() @ &m : Sas.forge ]
  <= eps * Pr[ Sas(C).main() @ &m : Sas.norm ] / ((1%r - eps) * (1%r - eps))
   + 2%r * (Pr[ G(Filt(Red(C))).main() @ &m : G.v /\ G.rel G.m G.m' ]
            - Pr[ G(Filt(Red(C))).main() @ &m : G.v /\ G.rel G.n G.m' ]
            - sqrt (Pr[ G(Filt(Red(C))).main() @ &m : G.v /\ G.rel G.n G.m' ]
                    * Pr[ G(Filt(Red(C))).main() @ &m : G.opd /\ !G.v ])) / (1%r - eps).
proof.
move=> ge0e lt1e.
have -> : Pr[ Sas(C).main() @ &m : Sas.forge ] = Pr[ G(Red(C)).main() @ &m : G.v /\ G.rel G.m G.m' ].
+ by byequiv sas_red.
have -> : Pr[ Sas(C).main() @ &m : Sas.norm ] = Pr[ G(Red(C)).main() @ &m : G.opd ].
+ by byequiv sas_red.
exact (c5_filter (Red(C)) red_md_ll eps &m ge0e lt1e red_sparse).
qed.

end section Hypotheses.
