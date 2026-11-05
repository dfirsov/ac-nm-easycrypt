# Comparison-based non-malleability, repaired — EasyCrypt development

This is the machine-checked part of the paper *Comparison-Based
Non-Malleability, Repaired* (Denis Firsov; preprint forthcoming).

Laur and Nyberg's comparison-based definition of non-malleable commitments
cannot be satisfied (Firsov–Laur–Zhuchko, ICTAC'22): an adversary that
refuses to open selectively, after seeing the opening, beats the comparison
for every scheme. The paper proposes **AC-NM**, which charges selective
refusals explicitly: in one experiment with the events

    Real = Pr[valid opening ∧ R(m, m')]          (R applied to the committed m)
    B    = Pr[valid opening ∧ R(n, m')]          (R applied to an independent n)
    V    = Pr[opened after seeing d, but invalidly or not at all]

the advantage is `Real − B − sqrt(B·V)`. In the development the definition is
called **C5** (the fifth candidate we examined); hence the file names.

All files check with no `admit`.

## Checking

Requirements:
- EasyCrypt at commit `a2cd7bf1e18d2b0c299f2b13d6004343dd1bf1ca`;
- Alt-Ergo 2.6.3. Z3 and CVC4 are not needed.

```
./check_all.sh                         # every file, plus two negative tests
./check.sh Sim_C5_Game.ec              # one file
./check.sh Sim_C5_Game.ec 1200         # goals at line 1200
```

The scripts use `$EASYCRYPT` if it is set. Otherwise they use a build in
`../tools/easycrypt` if there is one, and otherwise `easycrypt` on the
`PATH`. `check_all.sh` writes `check_all.log` with the EasyCrypt version, the
provers and the result of each file.

Both scripts exit with a nonzero status if any check fails.

The negative tests check that the setup rejects a false lemma
(`negtests/Neg_false.ec`). They also check that it rejects a falsely
strengthened bound: `Cand_Cond.ec` with 1/12 replaced by 1/11. A negative
test passes only if EasyCrypt reports `cannot prove goal` in the test file at
or after the false statement; any other failure, such as a missing binary or
a failed import, fails the test.

## Contents

| Paper | Files | Main lemmas |
|---|---|---|
| §2 the experiment | `C5.ec` | |
| §3 the design space | `Cand_Cond.ec`, `Cand_Ideal.ec`, `Cand_C6.ec` | `cond_unsat`, `c4_ideal`, `c6_sound`, `c6_maul`, `maul_c5` |
| §4 properties of AC-NM | `C5_Sanity.ec`, `C5_Binding.ec`, `C5_Tight.ec` | `AM_adv`, `cnm5_implies_hiding`, `c5_implies_binding`, `c5_tight` |
| §4 ideal model | `C5_Avg.ec`, `C5_IdealMod.ec`, `C5_Real.ec` | `averaging`, `c5_mod` |
| §4 satisfiability | `C5_Sat.ec` | `c5_sat` |
| §5 the a-priori baseline (CNM-AP) | `CNM_AP.ec`, `CNM_AP_Attack.ec`, `CNM_AP_Malleable.ec`, `CNM_AP_Hiding.ec`, `CNM_AP_Binding.ec` | `AL_adv` |
| §5 CNM-AP vs simulation | `CNM_AP_Sim.ec`, `CNM_AP_Converse.ec` | `sim_implies_ap`, `ap_implies_sim` |
| §5 AC-NM vs simulation | `C5_Sim.ec` | `c5_implies_sim` |
| §5, App. A simulation ⇒ AC-NM-init | `CNM_AP_HidLR.ec`, `Sim_C5_Core.ec`, `Sim_C5_Ideal.ec`, `Sim_C5_Game.ec` | `hidlr_eq`, `mix_lower`, `sum_bounds`, `choose_t`, `sim_c5_ideal`, `mix_sqrt` |
| §6 filtering and transfer | `C5_Filter.ec`, `C5_ManaIV.ec`, `C5_SAS.ec` | `c5_filter`, `mana_c5`, `sas_c5` |
| §6 vector AC-NM | `C5_Gen.ec`, `C5_Vector.ec` | `V.c5_filter` |
| §7 Bluetooth Numeric Comparison | `Lindell_A1.ec` | `unsat_sigma1` (valid openings), `unsat_sigma`, `unsat_bot`: the non-malleability definition of Lindell, CT-RSA 2009, App. A, is unsatisfiable |
| §9 commitment-based CNM | `CNM_C.ec`, `CNM_C_PKE.ec`, `CNM_C_Sanity.ec` | |
| (all) | `Instances.ec` | the scheme interface is consistent |

Each file starts with a comment that states its results.

### The reduction from simulation

The reduction from simulation (`Sim_C5_*`) is the longest proof. It works in
three layers:

- `Sim_C5_Core.ec` is the real analysis. It contains the pointwise
  inequality, the truncated geometric mixture of first-hit partition tests
  with an explicit tail, the weight sums, and the choice of `t`.
- `Sim_C5_Ideal.ec` does the counting for an arbitrary distribution of the
  adversary's runs: the partition tests, and the baseline with collisions.
  Its parameters are declared operators, so `sim_c5_ideal` is universally
  quantified.
- `Sim_C5_Game.ec` is the game level, for an abstract adversary. The
  reflection principle of the EasyCrypt standard library (`Reflection.eca`)
  turns the initialisation and one run into distributions. A generic
  composition lemma relates the five games of the reduction to them.
  `mix_sqrt` is Lemma "mix" of Appendix A.

The last step of Theorem 9 is proved on paper only: the test with `k = 2`,
the estimate of the truncation term, and the running times.

### Assumptions

The commitment scheme is abstract. Every hypothesis specific to a result is a
section hypothesis, so it appears as a premise of the exported lemma.
Examples are correctness, γ-unpredictability, distinct messages, and a
mauling map.

The only global axioms are theory parameters. The interface of the abstract
scheme (`Gen_ll`, `Com_ll`) is realised by a concrete scheme in
`Instances.ec`.

### Numerics

`numerics/` has the Python scripts used to stress-test the reduction from
simulation before it was mechanised:
- `enum.py`: exact enumeration in the ideal model;
- `lp.py`: an LP relaxation;
- `moments.py`, `pw.py`: the weight sums and the pointwise inequality.

`lp.py` needs `numpy` and `scipy`.

## License

No license has been chosen yet.
