# HB pointwise cusp finite-part specialization

- **ID:** HB-C-A.9w-pointwise-finite-part
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** ../1-in-progress/hb-complete-augmented-third-order-source-coefficient.md · C-A.9w
- **Statement:** Corpus analytic-family cusp finite part can be represented by a reporter on the
  height function obtained after fixing spectral parameters.

## Goal

Hostile-test the earliest representation needed to interpret C-A.9v's height-linear reporter as
the actual Zagier-style analytic-family finite part.

## Gates

- [x] 0 → 1 in-progress: corpus-derived conjecture and exact RH chain frozen
- [x] 1 → 2 fully-proven: collision and quotient-descent proof dependency-closed
- [x] 2 → 3 formalized: closed Lean no-go, targeted build, axiom audit
- [ ] 3 → 4 publication-ready: not a standalone publication target

## Exact kill

At actual convergence-chamber parameters `s=2,t=4`, shifted parameters are `u=3/2,v=7/2`.
The nonzero actual boundary label `(1,2,-1)` then has specialized exponent

`1/2 + 2u - v = 0`.

Unit mass at this label and unit mass at the identically-zero affine label therefore produce the
same specialized height profile for every height, but corpus analytic-family finite part assigns
them `0` and `1`.  Their difference is a specialization-kernel vector with finite part one.

Lean also proves the exact general criterion

`(∃ reporter, reporter o observation = linearFunctional)
  ↔ ker(observation) ≤ ker(linearFunctional)`

for an arbitrary, potentially nonlinear reporter.  The witness violates this necessary and
sufficient condition.  No linearity, continuity, or asymptotic assumption can repair pointwise
descent.

## No-go closure

- **Route killed:**
  `analytic-family finite part -> height-only reporter after specialization -> C-A.9v residual ->
  scalar RSZ landing -> balanced source -> negative BM -> left-QNM -> HC94 -> RH`.
- **Strongest positive survivor:** Keep spectral parameters and affine exponent labels until after
  meromorphic regularization.  Required chain is
  `parameter-family meromorphic scalar RSZ -> C-A.9u -> balanced source -> negative BM -> left-QNM
  -> HC94 cocycle -> RH`.
- **New invariant:** Kernel inclusion is the exact descent invariant.  Analytic-family finite part
  detects a direction erased by pointwise specialization at resonance.
- **Lean:**
  `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinCuspFinitePartSpecializationNoGo`;
  headline theorem
  `d4BM_cuspAnalyticFamilyFinitePart_not_factorThrough_specializedHeight`.
  Direct Lean and targeted build `12477/12477` pass.  Axiom audit reports only `propext`,
  `Classical.choice`, and `Quot.sound`.

Primary-source audit through 2026-08-29: Zagier's regularized Rankin--Selberg theory is classical,
and Wu's treatment explicitly separates singular cases and uses deformation families
(<https://arxiv.org/abs/1810.09437>, §3).  Neither audited literature nor corpus states this exact
source-normalized affine specialization-kernel obstruction or quotient classification.  Novelty
claim is restricted accordingly.

## Log

- 2026-08-29 — pointwise finite-part descent falsified; family-level survivor formalized
