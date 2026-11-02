(* MANA IV from C5: Laur-Nyberg's Lemma 2 with C5 in place of their
   (unsatisfiable) comparison-based non-malleability.

   Protocol (Laur-Nyberg CANS'06, Fig. 2), with Charlie in the middle:
     1. Alice: ka <$ Ka, (c, d) <$ Commit pk ka, sends (ma, c);
        Charlie delivers (ma', c') to Bob.
     2. Bob: kb <$ Kb, sends (mb, kb); Charlie delivers (mb', kb') to Alice.
     3. Alice sends the opening (ka, d); Charlie delivers (ka', d') to Bob,
        who halts unless Verify pk (ka', (c', d')).
     4. oob_A = h (ma, mb') ka kb'  and  oob_B = h (ma', mb) ka' kb.
   d-forge: both accept, oob_A = oob_B, and (ma, mb') <> (ma', mb).

   Lemma 2 of Laur-Nyberg covers the almost-normal execution paths (both
   second-round messages delivered before either third-round message) with
   c' <> c.  For those paths the order alpha, alpha', beta, beta', gamma,
   gamma' is without loss of generality, since Charlie can always delay a
   delivery; this is the game Mana below (the remaining paths are handled by
   hiding and binding in Laur-Nyberg's Lemmas 1, 3-5, and C5 implies both,
   see C5_Sanity.ec and C5_Binding.ec).  Charlie also chooses the inputs.

   Laur-Nyberg (Lemma 2):  Pr[d-forge /\ norm] <= eps_a * Pr[norm] + eps_nm.
   Here (mana_c5):
     Pr[d-forge /\ norm] <= eps_a * Pr[norm] / (1 - eps_a)^2
                            + 2 * Adv_C5(Filt(Red(C))) / (1 - eps_a).
   The reduction Red(C) is Laur-Nyberg's A*: the relation (their A4) is
   fixed at commit time, after Bob's kb and Charlie's (mb', kb').  Applying
   C5 to Red(C) directly would give eps_a + sqrt(eps_a); the filter of
   C5_Filter.ec removes the square root.                                    *)

pragma Goals:printall.

require import AllCore Distr DBool StdRing StdOrder RealExp.
require import C5 C5_Filter.
import RField RealOrder.

type data, kbt, sas.

op dka : message distr.                    (* the sub-key ka, committed by Alice *)
op dkb : kbt distr.                        (* Bob's sub-key kb *)
op h : data * data -> message -> kbt -> sas.

section Hypotheses.

declare axiom dka_ll : is_lossless dka.
declare axiom dkb_ll : is_lossless dkb.

(* h is (eps_a, _)-almost regular w.r.t. the sub-key ka *)
op eps_a : real.
declare axiom h_reg x k t : mu dka (fun ka => h x ka k = t) <= eps_a.

module type Charlie = {
  proc init(pk : pubkey) : data * data
  proc a2b(ma : data, c : commitment) : (data * commitment) option
  proc b2a(mb : data, kb : kbt) : data * kbt
  proc open(m : message, d : openingkey) : (openingkey * message) option
}.

module Mana(C : Charlie) = {
  var ma, mb, ma', mb' : data
  var ka, ka' : message
  var kb, kb' : kbt
  var c, c' : commitment
  var norm, forge : bool

  proc main() : unit = {
    var pk, d, r, o;
    pk         <$ Gen;
    (ma, mb)   <@ C.init(pk);
    ka         <$ dka;
    (c, d)     <$ Commit pk ka;
    r          <@ C.a2b(ma, c);
    norm       <- false;
    forge      <- false;
    if (r <> None /\ (oget r).`2 <> c) {
      norm       <- true;
      (ma', c')  <- oget r;
      kb         <$ dkb;
      (mb', kb') <@ C.b2a(mb, kb);
      o          <@ C.open(ka, d);
      ka'        <- (oget o).`2;
      forge      <- o <> None /\ Verify pk (ka', (c', (oget o).`1))
                    /\ h (ma, mb') ka kb' = h (ma', mb) ka' kb
                    /\ (ma, mb') <> (ma', mb);
    }
  }
}.

(* Laur-Nyberg's A*, as a C5 adversary *)
module Red(C : Charlie) = {
  var ma, mb : data

  proc init(pk : pubkey) : message distr = {
    (ma, mb) <@ C.init(pk);
    return dka;
  }

  proc commit(c : commitment) : (commitment * relation) option = {
    var r, ma', c', kb, mb', kb', out;
    r   <@ C.a2b(ma, c);
    out <- None;
    if (r <> None /\ (oget r).`2 <> c) {
      (ma', c')  <- oget r;
      kb         <$ dkb;
      (mb', kb') <@ C.b2a(mb, kb);
      out        <- Some (c', fun x y => h (ma, mb') x kb' = h (ma', mb) y kb
                                         /\ (ma, mb') <> (ma', mb));
    }
    return out;
  }

  proc decommit(m : message, d : openingkey) : (openingkey * message) option = {
    var o;
    o <@ C.open(m, d);
    return o;
  }
}.

section.

declare module C <: Charlie {-G, -Filt, -Red, -Mana}.

local equiv mana_red : Mana(C).main ~ G(Red(C)).main :
  ={glob C} ==> Mana.forge{1} = (G.v /\ G.rel G.m G.m'){2} /\ Mana.norm{1} = G.opd{2}.
proof.
proc; inline Red(C).init Red(C).commit Red(C).decommit.
seq 7 9 : (={glob C, pk, d} /\ Mana.ma{1} = Red.ma{2} /\ Mana.mb{1} = Red.mb{2} /\
           Mana.ka{1} = G.m{2} /\ Mana.c{1} = G.c{2} /\ c{2} = G.c{2} /\ r{1} = r0{2} /\
           !Mana.norm{1} /\ !Mana.forge{1}).
+ wp; call (: true); wp; rnd; rnd{2}; rnd; wp; call (: true); auto => />; smt(dka_ll).
if{1}.
+ rcondt{2} 2; first by auto.
  rcondt{2} 12; first by auto; call (: true); auto.
  wp; call (: true); wp; call (: true); rnd; wp; skip => /> /#.
rcondf{2} 2; first by auto.
rcondf{2} 8; first by auto.
by auto => />.
qed.

local lemma red_md_ll : hoare[ Red(C).init : true ==> is_lossless res ].
proof. by proc; call (: true); auto => />; apply dka_ll. qed.

local lemma red_sparse : hoare[ G(Red(C)).main : true ==> G.opd => sparse eps_a G.md G.rel ].
proof.
proc; inline Red(C).init Red(C).commit Red(C).decommit.
seq 10 : (G.md = dka /\ out = None).
+ by wp; call (: true); auto; call (: true); auto.
seq 1 : (G.md = dka /\ (out <> None => sparse eps_a dka (oget out).`2)).
+ if; last by auto.
  wp; call (: true); rnd; wp; skip => /> &hr _ _ kb0 _ o y /=.
  apply (ler_trans (mu dka (fun x => h (Red.ma{hr}, o.`1) x o.`2
                                   = h ((oget r0{hr}).`1, Red.mb{hr}) y kb0))).
  + by apply mu_sub => /#.
  by apply h_reg.
sp; if; last by auto => /> /#.
by wp; call (: true); auto => /> /#.
qed.

lemma mana_c5 &m : 0%r <= eps_a => eps_a < 1%r =>
  Pr[ Mana(C).main() @ &m : Mana.forge ]
  <= eps_a * Pr[ Mana(C).main() @ &m : Mana.norm ] / ((1%r - eps_a) * (1%r - eps_a))
   + 2%r * (Pr[ G(Filt(Red(C))).main() @ &m : G.v /\ G.rel G.m G.m' ]
            - Pr[ G(Filt(Red(C))).main() @ &m : G.v /\ G.rel G.n G.m' ]
            - sqrt (Pr[ G(Filt(Red(C))).main() @ &m : G.v /\ G.rel G.n G.m' ]
                    * Pr[ G(Filt(Red(C))).main() @ &m : G.opd /\ !G.v ])) / (1%r - eps_a).
proof.
move=> ge0e lt1e.
have -> : Pr[ Mana(C).main() @ &m : Mana.forge ] = Pr[ G(Red(C)).main() @ &m : G.v /\ G.rel G.m G.m' ].
+ by byequiv mana_red.
have -> : Pr[ Mana(C).main() @ &m : Mana.norm ] = Pr[ G(Red(C)).main() @ &m : G.opd ].
+ by byequiv mana_red.
exact (c5_filter (Red(C)) red_md_ll eps_a &m ge0e lt1e red_sparse).
qed.

end section.

end section Hypotheses.
