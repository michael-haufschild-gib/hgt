# The finite scattering quotient and its exact floor

- **ID:** finite-scattering-quotient-exact-floor
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-1011/obstacles-summary.md`, A99.
- **Statement:** The geometric height telescope is the logarithmic derivative of `Λ(s)/Λ(s+N)`. At every fixed positive scattering height, RH is equivalent to the exact arithmetic defect floor.

## Formula and proof

For `Re s>1`, `Im s≠0`, logarithmic differentiation identifies the finite telescope with `logDeriv (Λ(s)/Λ(s+N))`. The normalized formula adds the Robin scalar and both original poles, `1/s+1/(s−1)`.

Write `E_N` for the raw energy at height `N+1`, `J_N≥0` for its normalized second-height jump tail, `P_N` for the normalized omitted prime form, and `g₀=gammaHardyPhaseRate(0)`. The corrected energy is

`E_N^corr = E_N + (2g₀−mass(N+1))‖f‖² − P_N`.

The exact identity is `E_N^corr+J_N=W(f)`, the literal closed Weil quadratic form. Thus the floor `E_N^corr≥−J_N`, for every aperture and state, is equivalent to RH. In raw normalization the defect is `J_N+(2g₀−mass(N+1))‖f‖²−P_N`; omitting the last two terms changes the criterion.

## Lean

Modules in `formal/GaloisForLFunctions/HyperbolicArakelovTheory/`:

- `TheFiniteTowerIsACompletedZetaQuotient.lean`: `geometricTower_eq_logDeriv_completedZetaQuotient`, `renormalizedTower_eq_completedZetaQuotient`.
- `TheJumpTailFloorNeedsTheFullArithmeticNormalization.lean`: `correctedScatteringEnergy_add_jumpTail`, `riemannHypothesis_iff_correctedScatteringEnergy_floor`, `riemannHypothesis_iff_scatteringWeilEnergy_full_floor`.

Direct `lake --old env lean` audits passed. Transitive axioms: `propext`, `Classical.choice`, `Quot.sound`. Imported by `HyperbolicArakelovTheory.lean`.
