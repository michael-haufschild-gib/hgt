# The Gamma reserve survives growing overlap

- **ID:** the-gamma-reserve-survives-growing-overlap
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** review-2910 obstacles I17 ("a synthesized-mass floor at growing overlap") and work item
  W09 ("transfer the Montgomery–Vaughan band bound through the profile multiplier and Gamma
  weight"); wall 3.47 (atom-norm degeneration).
- **Statement:** For the tilted unit spline, `M = ‖φ‖²`, every `1 ≤ c ≤ N` and every `x`:
  `∫ f_x² ≥ κ c⁻⁷ (c/N)M Σx²` and `archForm f_x ≥ (κ c⁻⁷ log N − b c)(c/N)M Σx²`, with explicit
  `κ, b` independent of `N, c`. The reserve per unit atom mass tends to `∞` along every schedule
  `c_N⁸ = o(log N)`.

## Proof

1. Band floor: `|φ̂(t)| = (1/8)|Ŝ(t/8)| ≥ (1/8) sinh⁴1/(1 + (t/8)²)²`, so on `[c, 101c]`
   `|φ̂|² ≥ m(c) = sinh⁸1/(64(1 + (101c/8)²)⁴) ≥ (sinh⁸1/(64·161⁴)) c⁻⁸` for `c ≥ 1`.
2. Montgomery–Vaughan through the profile (`noRealZero_highBand_mass`):
   `∫_N^{101N} |f̂_x|² ≥ 48 c² m(c)/N · Σx²`.
3. Synthesized mass: Plancherel `∫_N^{101N}|f̂|² ≤ 2π∫f²`.
4. Gamma reserve: `archForm f ≥ (log N/2π)∫_N^{101N}|f̂|² − (γ_off + log 2)∫f²`
   (`archForm_ge_log_band_sub_mass`) and `∫f² ≤ (1 + 2ec)(c/N)M Σx²` for `N ≥ c`
   (`integral_atomicTest_sq_le_of_le_horizon`).
5. Growth: `κ L/c⁷ − bc ≥ (κ/2)L/c⁷ ≥ (κ/2)L/c⁸ → ∞` when `c⁸/L → 0`.

## Lean

`CriticalArithmeticCorrelationTheory/TheGammaReserveSurvivesGrowingOverlap.lean`:
`tiltedUnitSpline_band_floor`, `splineBandFloor_ge`, `band_mass_ge`, `band_le_two_pi_mass`,
`integral_atomicTest_sq_ge_growing`, `archForm_atomicTest_ge_growing`,
`tendsto_gammaReserve_growing`. Axioms standard; wired into `CriticalArithmeticCorrelationTheory.lean`.

## Log
- 2026-10-30 — paper proof and Lean formalization.
