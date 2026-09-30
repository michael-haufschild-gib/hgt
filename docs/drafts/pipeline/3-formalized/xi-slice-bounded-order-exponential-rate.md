# Slice positivity at bounded orders for almost every height, exponential rate

- **ID:** XI-SLICE-BOUNDED-ORDER-EXPONENTIAL
- **Stage:** 3-formalized
- **Type:** PARTIAL PRODUCER (slice receiver, route LA); sharpens MUST-577/583/585
- **Parent:** `rh-goal-loop-opus-2026-09-29.md`, cycle 59
- **STATUS:** MUST-587

## Theorem [L]

`RHTower.eventually_volume_xiSliceCoeff_nonpos_bounded_order_exp_le`: there are `C, c > 0` such that
for every `K ≥ 1` and all large `T`,

`|{t ∈ [T, 2T] : c_{2k}(t) ≤ 0 for some k ≥ K}| ≤ C T e^{−cK}`,

with `c = ε/60`, `ε = 10⁻⁹`. Axioms: `propext, Classical.choice, Quot.sound`.

## Mechanism

1. **Fixed length.** Keep `x = T^{1/30000}`. The window, Lorentzian and far-majorant exceptional sets
   of the box bound are then `≤ C T e^{−κ/120000}/ε + C T^{1/2}`, as in MUST-577.
2. **Prime part: `D_x = P_x + H_x`** with `|H_x| ≤ 48/R` on the box (MUST-583).
3. **Cascade of prime ranges.** Put `u = 2T^{1/15000} ≥ N_x` and `c_j = u^{2^{−j}}` (`cascadeCut`).
   Then `P_x = Σ_{j≤J} P_{(c_{j+1}, c_j]} + P_{(0, c_{J+1}]}` (`selbergPrimePoly_eq_sum_range`).
   - Range `j` uses `m_j = 3750·2^j` moments. Since `c_j^{m_j} = u^{3750} ≤ 2^{3750} T^{1/4}`
     (`cascadeCut_pow`), the mean-value length term is `≤ T` for every range at once
     (`eventually_cascade_length_le`).
   - Energy on `Re z = ½ + δ ≥ ½ + R/2`: `≤ c_{j+1}^{−δ}·20/δ² ≤ e^{−κ2^{−j−2}/15000}·80/R²`
     (`sum_selbergPrimeRangeCoeff_sq_le_rpow`, `exp_le_cascadeCut`).
   - Threshold `M_j = (εL/100)(3/4)^j`. Then `(m_jV_j/M_j²)^{m_j} ≤ e^{−κ/16}` whenever
     `3·10⁹(32/9)^j ≤ κ²ε²` (`large_range_tail_le`, `cascade_large_range_volume_le`).
   - Last range: energy `≤ C₃ (log c_{J+1})²`, with `C₃ = 1 + |C|/log 2`
     (`sum_selbergPrimeRangeCoeff_sq_le_sq_log`, from `Σ Λ²/n ≤ log N(log N + C)`). Its base is
     `(2/3)C₃(8/9)^{J+1}/ε² ≤ e^{−1}`, so it costs `e^{−3750·2^{J+1}}`
     (`small_range_tail_le`, `cascade_small_range_volume_le`).
   - `J = log₄⌊κ²ε²/(3·10⁹)⌋` gives `(32/9)^j ≤ 4^J`, `3750·2^{J+1} ≥ κε/15` and `J+1 ≤ κ²`
     (`cascade_J_facts`). The thresholds sum to `≤ εL/25 ≤ εL/8`.
   - Result: `exists_volume_largeNearBox_selbergPrimePoly_cascade_le`, measure
     `≤ (4140/π)T(κ²e^{−κ/16} + e^{−κε/15})`.
4. **One scale.** `exists_volume_not_zetaLogDerivScaleData_le_exp`: measure
   `≤ C T (e^{−κ/120000}/ε + κ²e^{−κ/16} + e^{−κε/15}) + C T^{1/2} ≤ C' T e^{−κε/30} + C T^{1/2}`.
5. **Dyadic assembly** with `κ₀ = K/2` and `e^{−c2^jκ₀} ≤ e^{−cκ₀}2^{−j}` for `cκ₀ ≥ 1`.

## Lean modules (in `formal/GaloisForLFunctions/RHTower/`, wired in `RHTower.lean`)

- `SelbergPrimeRangeCascade`: `edPoly_Icc_eq_of_support`,
  `volume_largeNearBox_edPoly_primeSupported_le`, `largeNearBox_sum_subset`,
  `selbergPrimeRangeCoeff`, `selbergPrimeRangePoly`, `selbergPrimeCoeff_eq_sum_range`,
  `selbergPrimePoly_eq_sum_range`, `selbergPrimeRangePoly_eq`,
  `sum_selbergPrimeRangeCoeff_sq_le_rpow`, `exists_sum_selbergPrimeRangeCoeff_sq_le_log`.
- `ZetaLogDerivTypicalBoxPrimeCascade`: the cutoffs, `volume_tail_le_pow`, `large_range_tail_le`,
  `small_range_tail_le`, `length_term_le_of_floor`, `cascade_large_range_volume_le`,
  `sum_selbergPrimeRangeCoeff_sq_le_sq_log`, `cascade_small_range_volume_le`,
  `largeNearBox_add_subset`, `eventually_cascade_length_le`, `cascade_J_facts`,
  `exists_volume_largeNearBox_selbergPrimePoly_cascade_le`, `scale_terms_cascade_le`,
  `exists_volume_not_zetaLogDerivScaleData_le_exp`.
- `XiSliceBoundedOrderExponentialRate`: `sq_mul_exp_neg_div_le`, `scale_bound_exp_le`,
  `exp_neg_two_pow_mul_le`, `volume_dyadic_scale_exp_le`,
  `eventually_volume_xiSliceCoeff_nonpos_bounded_order_exp_le`.

Leaf builds with `--old`; axioms standard; `.ilean` collision sweep clean.

## Limits

- **Rate.** `e^{−cK}` matches the zero-shadow scale. Zeros with `β − ½ ≍ K/log T` obstruct order
  `≍ K`, and near-line density controls them only exponentially.
- **Fixed `K`.** Density zero at a fixed `K` is still the average-distance problem.
- **Constants.** `c = 1/(6·10¹⁰)` reflects `ε = 10⁻⁹` (the saddle's level) and has not been
  optimized.
