# Route TT conjecture loop (2026-10-13)

- **ID:** tt-loop-1013
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** docs/reports/rh-current-frontier-map.md §TT
- **Statement:** Working log of the hgtl7 conjecture loop on route TT (theta tail, heat–Cassini, Wold residual).

## Goal
Unconditional Lean proof of RH via route TT, a mix, or a new route. Each cycle: conjecture → attack → paper proof → Lean → anti-theatre/anti-laziness.

## Frontier facts used (Lean only)
- `riemannHypothesis_iff_woldNatResidualAllStrictHalfPowerRate` (R:XiHeatCassiniWoldResidualMertensInverseAbel): RH ⟺ Wold residual `R_N = Σ_{p≤N}(1−1/p)³log p/p − log N − C` is `O(N^{−t})` for all `t<½`.
- `riemannHypothesis_iff_woldNatResidualSqrtMeanSpectrum_zero`: same with √N-window means.
- `summable_xiHeatCassiniWoldNatNearIncrementCovariance`: absolute near-pair budget for `2t+η<1` (pure size).
- Walls: memory `rh-core-walls-catalogue` (wall 1 = √x-precision prime counting).

## Log
| # | Conjecture | Verdict | Lean | Lesson |
|-|-|-|-|-|
