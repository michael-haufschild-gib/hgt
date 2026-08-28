# JAS completed-theta all-grade Mellin chain

- **ID:** JAS-CTAGMC-1
- **Stage:** 3-formalized
- **Type:** THEOREM / HARD-FRONTIER CLOSURE
- **Source:** read-only `rh-current-frontier-map.md`, JAS `ORIENT + COMP` open core

## Hard frontier target

Let `Phi` be actual reflection-renormalized completed theta source already landed as
`jointAncestryCompletedThetaSourceL2` in maximal domain of closed multiplication operator
`M_exp`. For every Rees/valuation grade `r`, form literal vector

`v_r(x) = exp(r x) Phi(x)`.

The formal theorem package proves simultaneously:

1. every `v_r` lies in `L2(R)` and maximal domain of `M_exp`;
2. exact closed graph ladder `M_exp v_r = v_(r+1)`;
3. every `v_r` is nonzero;
4. every finite grade packet is linearly independent, hence its full exterior compound is nonzero.

This is first completion-sensitive falsifier demanded by JAS: actual completed theta retains every
valuation/Rees grade under one closed singular Mellin graph. It closes full valuation-depth and
finite-compound-retention parts of JAS open core. Surviving burden is prime-support-synchronized
cofinal completion and nonzero `C(PrimeTorus)`-linear sewing. Scalar all-order Xi derivative-current
landing is already present elsewhere in corpus and is not counted again here.

## Corpus basis

Searches used `scripts/formal_tools.py research` only. Corpus supplies arbitrary natural
exponential decay of `Phi`, an internal all-natural exponential-weight `L2` proof, closed maximal
multiplication by `exp`, exact operator application almost everywhere, strict positivity of
`Phi`, and coordinate-power linear independence for a nonvanishing weight with infinite
coordinate range. No corpus theorem assembles actual completed theta into an all-grade closed
operator ladder or proves full grade-packet compound retention.

## Conjecture loop and resolution

### C1 — all-grade graph ladder — PROVED

The module proves all-natural weighted `L2`, defines `v_r` by `MemLp.toLp`, proves maximal-domain
membership using grade `r+1`, and identifies operator output by almost-everywhere multiplication.
Grade zero is definitionally bridged to prior completed-theta landing.

### C2 — nonzero all grades — PROVED

Strict positivity and continuity of `exp(r x) Phi(x)` exclude every grade's `L2` class being zero.

### C3 — complete countable independence and finite compound retention — PROVED

Corpus coordinate-power independence applies to `z(x)=exp(x)` and weight `Phi(x)`. Continuity
upgrades an almost-everywhere vanishing finite combination to pointwise vanishing, transporting
independence through the genuine `L2` quotient. Entire countable grade family is independent;
therefore every finite grade packet has full rank and nonzero top exterior compound.

## Lean artifact

- Module: `GaloisForLFunctions.RHTower.JointAncestryCompletedThetaAllGradeMellinChain`
- `jointAncestryCompletedThetaGradeL2_zero`
- `jointAncestryCompletedThetaGradeDomain_zero`
- `jointAncestrySingularMellinOperator_completedThetaGrade`
- `jointAncestryCompletedThetaGradeL2_ne_zero`
- `linearIndependent_jointAncestryCompletedThetaGradeL2`
- `linearIndependent_jointAncestryCompletedThetaGradeL2_fin`

## Hostile falsification

1. Actual completed theta source only; no abstract Schwartz replacement.
2. One closed maximal operator and its genuine domain; no bounded cutoff surrogate.
3. All natural grades, not a fixed finite range.
4. Nonzero/independence must survive `L2` quotient, not merely pointwise functions.
5. No Xi zero, RH premise, numerical computation, or added axiom.

## Novelty audit

Targeted literature search found adjacent theta-kernel approximation work (Shi,
arXiv:1502.06844), harmonic-oscillator theta/Xi representations (Coffey,
arXiv:math-ph/0612086), and scaling-Hamiltonian multiplication-operator machinery (Connes--Consani,
arXiv:1910.14368). None states the exact result here: actual completed-theta source as a countable
all-grade orbit in one closed maximal multiplication graph, with linear independence retained after
`L2` quotienting. This is a targeted no-match audit, not a proof of global absence from literature.

`[PROVED HERE] [LEAN CLOSED] [INTERNAL SEARCH COMPLETE] [TARGETED EXTERNAL NO-MATCH AUDIT]`

## Formal audit

- `lake env lean GaloisForLFunctions/RHTower/JointAncestryCompletedThetaAllGradeMellinChain.lean`
  passed.
- `lake build GaloisForLFunctions.RHTower.JointAncestryCompletedThetaAllGradeMellinChain` passed.
- Main theorem axiom probes report only `propext`, `Classical.choice`, and `Quot.sound`.
- Formal lint contains no failure involving this module and no forbidden declaration; repository-wide
  exit remains nonzero from unrelated concurrent umbrella-reachability failures.
- Module is wired into `GaloisForLFunctions.RHTower`; frontier map remained read-only.

## Log

- 2026-08-28 — selected after formal SC additive-universality route kill; frontier map read-only;
  conjecture derived from JAS corpus searches, not model memory.
- 2026-08-28 — C1--C3 proved in Lean; exact leaf build and axiom audit passed; promoted to
  `3-formalized`.
