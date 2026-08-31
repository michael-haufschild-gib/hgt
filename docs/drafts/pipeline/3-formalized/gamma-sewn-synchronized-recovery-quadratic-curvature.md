# Gamma-sewn synchronized-recovery quadratic curvature

- **ID:** REC-Q2
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** corpus-derived from `GammaSewnSynchronizedRecoveryContraction`
- **Statement:** Finite-support synchronized Gamma recovery has exact negative second jet with cost `(1/3)∑ log²p + (1/24)(∑ log p)²`; this cost diverges on cofinal prime supports.

## Goal

Determine whether first-jet-flat Gamma recovery hides a source-natural higher-order channel capable
of combining cofinal prime support with completed-source compatibility.

## Gates

- [x] 0 → 1 in-progress: coefficient-faithful quotient and source prime support already exist
- [x] 1 → 2 fully-proven: exact finite-product second-jet proof and cofinal divergence proof
- [x] 2 → 3 formalized: `GammaSewnSynchronizedRecoveryQuadraticCurvature`, targeted leaf build green, axiom audit clean
- [ ] 3 → 4 publication-ready: standalone exposition and external novelty audit

## Result

For every finite prime support `P`,

`(R_P(x)-1)/x² → -C(P)` as `x → 0+`,

where

`C(P) = (1/3)∑_{p∈P} log(p)² + (1/24)(∑_{p∈P} log(p))²`.

`C(P)>0` for nonempty `P`, and `C(primesBelow N)→∞`. A proposition-level selection produces
positive apertures tending to zero for which normalized loss `(1-R)/x²` tends to `+∞`.

## Frontier

This closes fixed-support curvature and gives a genuine `COF + COMP` producer. It does **not**
prove unnormalized damping, moving-support Ward landing, or RH. The subsequent REC-UD theorem now
proves a support-uniform two-parameter bound: if total prime phase tends to zero, recovery ratio
tends to one. Hence REC-Q2 curvature cannot become nonzero damping in coefficient-faithful
small-total-phase completion; surviving recovery routes require a non-small-phase landing or a
different nonmultiplicative channel.

## Lean certificate

- Module: `GaloisForLFunctions.RHTower.GammaSewnSynchronizedRecoveryQuadraticCurvature`
- Main theorems:
  - `tendsto_gammaSewnSynchronizedRecoveryRatio_quadraticJet_zero`
  - `tendsto_gammaSewnSynchronizedRecoveryQuadraticCost_primesBelow_atTop`
  - `exists_gammaSewnSynchronizedRecovery_cofinal_quadraticLoss_schedule`
- Targeted leaf build: PASS
- Axioms: `propext`, `Classical.choice`, `Quot.sound`

## Log

- 2026-08-31 — REC-Q2 conjectured only after corpus search; proved in scratch, formalized, built, axiom-audited, and wired.
