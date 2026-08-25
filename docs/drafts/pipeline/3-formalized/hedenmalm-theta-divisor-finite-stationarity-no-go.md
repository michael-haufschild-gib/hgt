# Hedenmalm theta divisor finite-stationarity no-go

- **ID:** hedenmalm-theta-divisor-finite-stationarity-no-go
- **Stage:** 3-formalized
- **Type:** FALSIFIED
- **Source:** whole-corpus synthesis: fixed theta determinant + prime quantile flow
- **Statement:** Every genuine Xi divisor mode exists on the fixed theta source, but no nonzero finite measure on its quantile carrier is stationary under a genuine prime flow; invariant theta Haar covariance survives only at infinite mass.

## Goal

Test whether RH can be reinterpreted as finite-state stationarity of source-built Xi divisor modes.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [x] 1 → 2  fully-proven: dependency-closed paper proof
- [x] 2 → 3  formalized: Lean theorems `thetaXiDivisorEigenmode_no_finite_stationary_carrier` and `thetaXiDivisorEigenmode_infiniteHaar_survivor`; targeted build green; axioms audited
- [ ] 3 → 4  publication-ready: external novelty audit and standalone exposition

## Approach

Combine fixed compact theta-source eigenmode theorem with strict Lyapunov drift of integer prime translation in source quantile coordinates. Finite invariant mass would preserve mean quantile, contradicting strict drift. Transported additive Haar measure remains invariant because its interior mass is infinite.

## No-go closure

- **Exact killing theorem/mechanism:** `finiteMeasure_eq_zero_of_map_thetaIntegerQuantileFlow_eq_self`; a genuine prime flow strictly increases every interior quantile, so finite stationary mass is zero.
- **Strongest positive survivor:** `thetaXiDivisorEigenmode_infiniteHaar_survivor`; fixed Xi eigenmodes coexist with canonical invariant transported Haar measure of infinite interior mass.
- **New insight:** RH cannot be ordinary equilibrium/stationarity of divisor-mode probability mass. Any viable dynamics must retain a nonzero relative, quotient, or cohomological class over infinite-volume covariance while separately preserving pointwise transverse character.
- **Status:** Paper proof dependency-closed and formalized in `HedenmalmThetaDivisorFiniteStationarityNoGo.lean`. External novelty not claimed.

## Log

- 2026-08-25 — determinant-support synthesis hostile-tested; finite-stationarity variant falsified; infinite-Haar survivor formalized.
