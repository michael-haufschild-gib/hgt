# Bilinear Conductor Residuals and Unconditional All-Vector Weil Positivity Below 1/9

- **ID:** bilinear-conductor-residuals-and-one-ninth-weil-positivity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-3110/obstacles-summary.md · Q1 / Σ-2 / Σ-3
- **Statement:** For every `0 < α < 1/9`, eventually in `N` and uniformly across `1 ≤ c ≤ (log N)^α`,
  `completeWeilMatrix tiltedUnitSpline c N` is positive definite on all vectors. Polylogarithmic
  conductor packets (`m ≤ (log N)^q`, `α + 2q < 1`) retain `¼ Σ E_m(c) a_m²` for every `0 < α < 1/8`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized: `lake --old env lean` green, `#print axioms` = `[propext, Classical.choice, Quot.sound]`

## Mathematics

**Theorem A (packets below 1/8).** Each of the eight explicit-formula channels of
`r_m = W v_m − E(c,m) v_m` pairs with `v_l` at
`|⟨r_m, v_l⟩| ≪ √(ml)(1+log m)(c(1+log c)²(log N)^{1/k}/log N + c⁵ log N/N)`. Weighting by
`(E_m E_l)^{-1/2}` with `E_m(c) ≥ κ₀ min(1,(m/c)⁷)` gives a bilinear budget `≪ c⁸(log N)^{1/k−1}`.

**Theorem B (all vectors below 1/9).** Split `x = y + u₀ + u₁ + w` along
`Q₁ = ⌊(log N)^q⌋ ≤ R₀ = ⌊exp((log N)^½)⌋ ≤ R₁ = ⌊N^{θ₁}⌋`:
- `u₀ ∈ V_{R₀} ∩ V_{Q₁}^⊥`: energy `≥ ⅛E(a₀) + (¾ log Q₁ − log c − C)‖u₀‖²` (mid-band overlap sharpened to `c^{3/2}(1+log c)/√Q₁`, needs `q > 3α`);
- `u₁ ∈ V_{R₁} ∩ V_{R₀}^⊥`: energy `≥ ⅛E(a₁) + (¼ log R₀ − C c²(1+log c))‖u₁‖²`;
- `w ∈ V_{R₁}^⊥`: asymmetric two-region reserve `(k₁/4)P_w + (b k₁/2c⁷)S_w`, `k₁ ≍ θ₁ log N ≫ c⁹`;
- three cross terms paid by fractions of these reserves; result `(κ₀+2)‖z‖² ≤ W(z)` on `V_{Q₁}^⊥`;
- Schur synthesis with `Σ_{m≤Q₁} ‖r_m‖²/E_m(c) ≪ (c⁹ + c²Q₁²(1+log Q₁)²)(log N)^{1/k−1} → 0`.

The three `c⁹` costs (two-region gap, band–terminal cross, inverse-energy residual sum) set the
exponent `1/9`; the eighth-root receiver `TheTiltedSplineReceivesAtTheEighthRoot` gives the ceiling `1/8`.

## Lean
- `CACT/BilinearConductorResidualsAndOneEighthPackets`:
  `exists_completeWeil_bilinear_conductor_residual_variable_rate`,
  `exists_tiltedUnitSpline_quadratic_inv_energy_residual_sum_le`,
  `eventually_tiltedUnitSpline_polylog_conductorSubspace_energy_ge`,
  `eventually_tiltedUnitSpline_fixed_conductorSubspace_pos_below_one_eighth`.
- `CACT/SharpenedMidBandAndCrossBounds`:
  `exists_completeWeilEnergy_ge_three_quarters_log_homogeneous`,
  `norm_separatedCrossErrorMatrix_sq_le_of_mem_conductorSubspace`,
  `exists_completeWeil_cross_le_c9_split_reserves`.
- `CACT/TelescopedConductorSplitAndOneNinthWeilPositivity`:
  `eventually_tiltedUnitSpline_complement_coercive_below_one_ninth`,
  `eventually_tiltedUnitSpline_spectralFloorWeilMatrix_posDef_below_one_ninth`,
  `eventually_tiltedUnitSpline_completeWeilMatrix_posDef_below_one_ninth`,
  `eventually_tiltedUnitSpline_weilQuad_nonneg_below_one_ninth`,
  `exists_tiltedUnitSpline_completeWeilEnergy_ge_poleDefect_reserve_below_one_ninth`,
  `eventually_tiltedUnitSpline_all_conductors_pos_below_one_ninth`.
- `EHT/EdgeBelowOneNinth`:
  `eventually_ofReal_rpow_log_le_edge_tiltedUnitSpline_below_one_ninth`,
  `frequently_edge_mem_eighthRoot_window_of_not_riemannHypothesis_below_one_ninth`.
