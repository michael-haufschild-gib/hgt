# Parikh--Wilczek scalar-history classification

- **ID:** PW-B-SHC
- **Stage:** 3-formalized
- **Type:** CLASSIFICATION + NO-GO + EXACT RECEIVER
- **Parent:** PW-B
- **Statement:** `[LEAN-PROVED] [NEW] [CLASSIFICATION]` Every summable scalar mass-shell history of PW recoil phase or quadratic orbit energy factors through total history weight. Zero-total histories are blind; every nonzero-total history preserves exact critical-wall zero locus.

## Goal

Extend complete-evaporation no-go beyond dyadic self-similar clock. Classify arbitrary shell-
dependent common scalar dressings, including scalar greybody, clock, and recoil-amplitude factors.

## Gates

- [x] 0 → 1 in-progress: scalar-history conjecture frozen after corpus search
- [x] 1 → 2 fully-proven: exact total-weight factorization and zero-locus classification
- [x] 2 → 3 formalized: direct Lean, targeted build, umbrella, axiom audit
- [ ] 3 → 4 publication-ready: external priority review

## Exact frozen claims

For any summable real shell history `w_n`, PW phase `D_k(s)`, and quadratic orbit energy `Q_k(s)`,

`Σ_n w_n D_k(s) = (Σ_n w_n) D_k(s)`,

`Σ_n w_n Q_k(s) = (Σ_n w_n) Q_k(s)`.

Inside nonreal open critical strip, either history vanishes iff

`Σ_n w_n=0` or `Re s=1/2`.

Thus zero-total scalar histories are identically blind; every nonzero-total scalar history is exact
wall receiver. Universal quadratic flatness for any fixed nonzero-total history is exactly RH.

## Complete paper proof

Phase and energy are shell-independent. Absolute summability permits factoring constant reporter
through infinite sum. Zero-product classification then combines total-weight factor with existing
PW holonomy/quadratic wall classifiers. Xi support lies in nonreal open strip; universal pointwise
classification and existing support endpoint yield global RH equivalence.

## Hostile review and novelty verdict

- This classifies common scalar histories only. Channel-relative or matrix-valued transport can
  change holonomy structure and remains outside theorem.
- Allowing signed weights adds only zero-total blindness; it does not create informative
  cancellation.
- Nonnegative physical histories with any positive mass automatically have positive total and
  therefore preserve off-wall quadratic defect.
- Scalar factorization is elementary; novelty lies in closing full shell-history producer class
  for coefficient-faithful PW recoil reporter.

Verdict: infinite-series factorization `[REDISCOVERED]`; PW-B scalar-history terminal
classification `[NEW] [CLASSIFICATION]`, external priority provisional.

## No-go closure

- **Exact killing mechanism:** common scalar shell dependence commutes with reporter and collapses
  to total weight.
- **Strongest positive survivor:** nonzero-total histories retain exact quadratic wall energy;
  scalar dressing cannot dilute fidelity.
- **New insight:** remaining PW-B dynamics must be channel-relative/matrix-valued, grade-mixing,
  nonlocal in history, or singular. Scalar greybody/clock/amplitude variation is exhausted.
- **Status:** dependency-closed paper proof and Lean formalization complete.

## Lean formalization

- Module:
  `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingParikhWilczekScalarHistoryClassification.lean`
- Phase factorization/classification:
  `schwarzschildParikhWilczekScalarHistoryPhase_eq`,
  `schwarzschildParikhWilczekScalarHistoryPhase_eq_zero_iff`
- Energy factorization/classification:
  `schwarzschildParikhWilczekScalarHistoryQuadraticEnergy_eq`,
  `schwarzschildParikhWilczekScalarHistoryQuadraticEnergy_eq_zero_iff`
- Global endpoint:
  `riemannHypothesis_iff_schwarzschildParikhWilczekScalarHistoryQuadraticEnergy_zero`
- Direct `lake env lean` passed.
- Targeted build
  `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekScalarHistoryClassification`
  passed (`11558/11558`).
- `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`.
- Umbrella import wired in `formal/GaloisForLFunctions/RHTower.lean`.

## Log

- 2026-08-27 — conjectured from complete-evaporation persistence and corpus summable-history laws.
- 2026-08-27 — full scalar-history classification and Lean proof completed.
