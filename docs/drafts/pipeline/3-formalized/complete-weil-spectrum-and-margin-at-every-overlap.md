# The complete Weil spectrum and its margin at every overlap

- **ID:** complete-weil-spectrum-and-margin-at-every-overlap
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** AGT §6 "Why is positivity marginal at the limit? Open: the exact identity that carries
  the zero margin of Weil's form"; I1/I3 of `docs/reports/review-2910/obstacles-summary.md`; wall 3.26.
- **Statement:** For the tilted unit spline and every `c > 0`: (a) for every `T` off the energy set,
  eventually `#{eigenvalues of W_N(c) < T} = #{m ≥ 1 : E_m(c) < T}`; (b) the bottom eigenvalue of
  `W_N(c)` tends to `e(c) = min_m E_m(c) > 0`; (c) `e(c) → 0` as `c → ∞`
  (`E_m(c) = 2/(Mφ(m)) Σ_{(a,m)=1} (m/a) T(ac/m)`, positive Fourier integrals). Together with
  (d) RH ⟺ eventual positivity at overlap `2(log N)^α`, `α > 1/4`, the RH-sensitive overlap scale is
  `1 ≪ c_N ≲ (log N)^{1/4+ε}`.

## Lean
- `RAPT/TheBoundedCompleteWeilSpectrumIsTheCompletedShellSpectrum.lean` (compiled):
  `card_le_lowerSpectralWindow_of_quasimodes` (min-max with coincident energies),
  `finite_completedConductorEnergy_sublevel`, `eventually_completeWeil_spectral_count_eq_of_reserve_quasimodes`,
  `exists_completedConductorEnergy_eq_floor`, `tendsto_completedEnergyFloor_atTop`,
  `eventually_completeWeil_spectrum_bottom_of_reserve_quasimodes`.
- `RAPT/LogarithmicOverlapOfTheCompleteWeilMatrixIsTheRiemannHypothesis.lean` (compiled):
  `riemannHypothesis_iff_completeWeilEnergy_nonneg_of_growthTwo`,
  `riemannHypothesis_iff_tiltedUnitSpline_completeWeil_nonneg_log` (from SHA's second-order law).
- `RAPT/TheBottomOfTheCompleteWeilSpectrumIsTheCompletedShellEnergy.lean`:
  `tiltedUnitSpline_spectral_count_eq` (a), `tiltedUnitSpline_spectrum_bottom` (b, bottom →
  `completedShellEnergy` = conductor-one energy, via `completedEnergyFloor_eq_completedShellEnergy`),
  `tendsto_tiltedUnitSpline_completedShellEnergy_atTop` (c), `tiltedUnitSpline_overlap_window` (d).
  Quasimodes: `CACT.tendsto_completeWeilMatrix_ramanujan_quasimode_norm`. Axioms standard.

## Log
- 2026-10-30 — generic spectral count, floor and RH-side bridge compiled.
- 2026-10-30 — unconditional instances formalized.
