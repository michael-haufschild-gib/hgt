# Stage-two other-corpus unconditional Lean closure

- **ID:** `stage-two-other-unconditional-lean-closure`
- **Stage:** 1-in-progress
- **Type:** FORMALIZATION AUDIT
- **Source:** `../2-fully-proven/new_scientific_knowledge/other`
- **Statement:** Every dependency-closed paper theorem in the Stage-2 `other` corpus receives a
  literal, unconditional Lean theorem, umbrella registration, axiom audit, and verified card
  disposition without weakening its claim.

## Goal

Close Stage 2 → 3 for every exact card in scope. Falsified cards move to Stage 5 only after hostile
audit and positive-survivor extraction. Partial bridge theorems never count as card completion.

## Gates

- [x] 0 → 1 in-progress: full source directory inventoried; prior Lean corpus searched first
- [ ] 1 → 2 fully-proven: not applicable; this card tracks already paper-proven source cards
- [ ] 2 → 3 formalized: every source card has exact Lean disposition and all global audits pass
- [ ] 3 → 4 publication-ready: outside this audit

## Approach

1. Compare every displayed paper theorem with existing Lean signatures, including corollaries and
   asymptotic/support statements.
2. Add only missing literal infrastructure and prove it in `/tmp` before repository edits.
3. Run each touched leaf with `lake env lean`; batch all exact capstones through `#print axioms`.
4. Run formal lint, then final area-module builds; update and move only fully closed cards.

## Current exact closures

- `ccm-critical-mellin-aperture-resolvent-law`: source change-of-variables `(10)`, specialized tail
  `(11)`, and tail convergence added to `RHTower/CCMCriticalMellinApertureResolvent.lean`.
- `ramsey-weyl-causal-phase-law`: exact Weyl half-phase implication, scaled swap law, two-sided
  inverse, group commutator, and local nonvanishing added to
  `HTGeometry/ContinuumChronometricGravity.lean`.
- `two-species-conformal-clock-scale-law`: general-dimensional exponential chain rules, exact
  first-derivative cancellation, conformal defect, and massive conjugation added to
  `HTGeometry/ConformalClockDiffusion.lean`; the literal pseudo-Riemannian realization and coupled
  inverse-data theorem remain open.
- `two-mass-self-calibrating-clock-metric-law`: exact two-jet Leibniz calculus, local second-order
  endpoint dressing, pure zeroth-order mass difference, principal-symbol scaling, and undressed
  symbol reconstruction added to `HTGeometry/ClockPrincipalSymbolCalibration.lean`.
- `two-clock-locality-law`: exact zeroth-order cancellation connected to honest classical
  distribution-kernel fibers, with diagonal support and nonzero singleton-support equality, in
  `HTGeometry/ClockLocalityDistributionKernel.lean`.
- `backreaction-subtracted-two-clock-gravity-law`: exact two-sided inverse bridge added between
  Schur subtraction and the literal two-mass principal-symbol/kernel reconstruction chain.
- Exact Stage-3 certificates now cover bounded-relation profile realization, charged scalar torsor,
  split-source boundary matroid, polynomial torsion language, Xi depth successor layer, two-mass
  continuum rigidity, Cassini--Jensen seam law, prime-coordinate fusion, four-dimensional conformal
  diffusion, clock-coframe conservation, von Mangoldt bivariate marginal trace-lock, CCM aperture
  resolvent, and Ramsey--Weyl causal phase.  All audited capstones pass serialized direct checks,
  area umbrellas, and a combined axiom audit.

## Falsified disposition

- `shift-average-factorisation`: illegal sum/integral interchange invalidates headline theorems;
  positive survivors retained and card moved to Stage 5.

## Named open core

Exact per-card gaps remain the work queue. First confirmed examples: pseudo-Riemannian realization
of the general-dimensional conformal conjugation, chronometric ordered characteristic-functional
differentiation, Euler activation finite Gibbs/Fisher/Borel--Cantelli layers, and analytic parents
explicitly marked open on their source cards. The boundary-wedge dimension card retains a literal
HT-carrier gap: its two-variable `EntireSRRealization` proves only nonconstant carriers, while the
paper statement requires hypertranscendental carriers.  Its named mathematical obstruction is
differential transcendence of every nonzero finite dilation-orbit combination; the existing
exponential block seed is itself differentially algebraic and cannot close that gap.

## Log

- 2026-08-01 — inventory started; one falsified card retired; CCM and Ramsey exact gaps closed.
- 2026-08-01 — serialized fifteen exact leaf checks, both area umbrellas, and combined capstone
  axiom audit; added or refreshed thirteen exact Stage-3 certificates.  Rejected nonconstant-carrier
  `htDim` as a simplification of the boundary-wedge HT theorem.
- 2026-08-01 — closed the differential-operator principal-symbol gap in the two-mass clock metric
  card; fourteen source cards now have exact Stage-3 closures.
- 2026-08-01 — closed the two-clock distribution-kernel locality gap; fifteen source cards now
  have exact Stage-3 closures.
- 2026-08-01 — closed the backreaction-subtraction inverse/composition gap; sixteen source cards
  now have exact Stage-3 closures.
