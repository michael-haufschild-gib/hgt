# Exceptional-Conductor Emptiness Above Polylogarithms and Sharpened Power-of-Logarithm Weil Positivity

- **ID:** exceptional-conductor-emptiness-sharpened-power-log
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** Unconditional emptiness of exceptional Ramanujan conductors across `[⌈(log N)^A⌉₊, ⌊N^θ⌋₊]` for `0 < θ < 1/2`, `0 < α < 1/4`, `A > 8α`; coercivity of the complete Weil energy on `(conductorSubspace ⌊N^θ⌋₊ N)ᗮ` for `0 < α < 1/16`; linear-in-conductor `O(m (1 + log m)^2)` complete-Weil residual and defect-localized prime cross-pairing; and unconditional all-vector complete-Weil positivity across `1 ≤ c ≤ (log N)^α` for every `0 < α < sharpenedPowerLogExponent := 2 / 71`.

## Main theorems

Fix `E_N := EuclideanSpace ℝ (PrimeHorizonIndex N)`, `v_m := normalizedRamanujanHorizonVector m N`, `V_M := conductorSubspace M N`, and `φ₀ := tiltedUnitSpline`.

1. **Emptiness of exceptional conductors above polylogarithms (`Π-5` / Q2a).** For every `C²` profile `φ` supported in `[0, 1]` with `∫ φ² > 0`, every `0 < θ < 1/2`, every `0 < α < 1/4`, and every `A > 8α`, eventually in `N`, for all `1 ≤ c ≤ (log N)^α` and all `m ∈ [⌈(log N)^A⌉₊, ⌊N^θ⌋₊]`,
   `completeWeilEnergy φ c N v_m ≥ ((1 - 2θ) / 4) log m > 0`,
   so `{m ∈ [⌈(log N)^A⌉₊, ⌊N^θ⌋₊] : completeWeilEnergy φ c N v_m ≤ 0} = ∅`.

2. **Polynomial-conductor orthogonal-complement coercivity and negative-index ceiling.** For every `0 < θ < 1` and every `0 < α < 1/16`, there exists `c_orth > 0` such that eventually in `N`, for all `1 ≤ c ≤ (log N)^α` and all `z ∈ (V_{⌊N^θ⌋₊})ᗮ`,
   `completeWeilEnergy φ₀ c N z ≥ (c_orth log N / c^7) ‖z‖²`,
   and every subspace `U ≤ E_N` on which `completeWeilEnergy φ₀ c N ≤ 0` satisfies `Module.finrank ℝ U ≤ ⌊N^θ⌋₊`.

3. **Summed-residual perturbation and linear `m (1 + log m)²` conductor residual.**
   - Replacing `M² sup_{m ≤ M} ‖E v_m‖²` by `∑_{m ≤ M} ‖E v_m‖²` in low-band Schur decoupling controls the block interaction norm by `(4 / 3) ∑_{m=1}^Q ‖E v_m‖²`.
   - On `2 ≤ m ≤ N`, splitting the collar difference kernel at adaptive distance `D = m` and bounding far rows via zero-period-mean Abel summation (`|∑_{j ∈ [l,k)} c̃_m(j)| ≤ m`) and near rows via weighted Schur with `∑_{j=1}^N (j / N) v_m(j)² ≤ 2 / log N` yields
     `‖(A_center(α, N) - (α / N) A_pole(N)) v_m‖² ≤ 742 α² m (1 + log m)² / log N`.
   - Combining this with variable-cutoff prime, Mertens, upward-shell, downward-collar, and separated residuals yields
     `‖completeWeilMatrix φ c N v_m - E_m(φ, c) v_m‖² ≤ C m (1 + log m)² (c^5 / log N + c^10 (log N / N)² + c^3 (1 + log(c Y_N)) / log N + c^3 (1 + log m)^k / (log Y_N)^k)`.

4. **Defect-localized prime cross-pairing.** For `u = ∑_{m=1}^{R'} a_m v_m ∈ V_{R'}` and `w ∈ (V_{R'})ᗮ` with `(R')^6 ≤ N` and `(1 + log R')² ≤ √(log N)`, splitting `Icc 1 N = Icc 1 (N / R'^4) ∪ Ioc (N / R'^4) N` bounds the deep prime residual `n ≤ N / R'^4` by `O(1) ‖u‖` via `abs_normalizedRamanujan_correction_le` at quotient `y ≥ R'^4 ≥ m R'^3`, while on `n > N / R'^4` pairing against the localized tail of `w` (`∑_{n > N / R'^4} w_n² ≤ ((4 log R' + 2) / log N) poleDefect_N(w)`) gives
   `|⟪fullPrimeMatrix N u, w⟫| ≤ C_loc (‖u‖ ‖w‖ + ((1 + log R')^(5/2) / √(log N)) ‖u‖ √(poleDefect_N(w)))`.

5. **All-vector power-of-logarithm positivity up to `α < 2 / 71`.** Setting `Q₁(N) := ⌊(log N)^(17α/2)⌋₊`, `Y_N := exp((log N)^((1 - 36α)/2))` at shell order `k = 2`, and absorbing the defect-localized cross-pairing on `(V_{R'})ᗮ` into `(b / (2 c^7)) poleDefect_N(w)` reduces the high-tail confinement scale from `c^46` (`α < 1/46`) and `c^16` (`80α < 2`) to `35α < 1` and `71α < 2`, establishing unconditional positive definiteness of `completeWeilMatrix φ₀ c N` across `1 ≤ c ≤ (log N)^α` for every `0 < α < sharpenedPowerLogExponent := 2 / 71` (`> 1 / 36 > powerLogPositivityExponent`), together with spectral floor `(κ / (2 c^7)) ‖x‖²`, `weilQuad ≥ 0`, zero-mass-loss `poleDefect` reserve, emptiness of nonpositive conductors across `[1, N]` for `0 < α < 2 / 71`, and confinement of any nonpositive conductors in `[1, ⌊N^θ⌋₊]` (`0 < θ < 1/2`, `0 < α < 1/4`) to `[1, ⌈(log N)^9⌉₊]`.

## Lean

1. `CompletedArithmeticForms/ExceptionalConductorsVanishAbovePolylog.lean` (wired into `CompletedArithmeticForms.lean`).
   Exact declarations:
   - `abs_sum_Ico_normalizedRamanujanMode_le`
   - `abs_sum_Icc_normalizedRamanujanMode_div_le`
   - `eventually_completeWeilEnergy_mode_ge_log_above_polylog`
   - `eventually_exceptionalConductors_above_polylog_empty`
   - `eventually_tiltedUnitSpline_mode_ge_log_above_polylog`
   - `eventually_tiltedUnitSpline_exceptionalConductors_above_polylog_empty`

2. `CriticalArithmeticCorrelationTheory/PolynomialConductorComplementCoercivityAndSharpenedOverlap.lean` (wired into `CriticalArithmeticCorrelationTheory.lean`).
   Exact declarations:
   - `eventually_completeWeilEnergy_ge_on_polynomialConductorOrthogonal`
   - `eventually_completeWeil_global_negIndex_le_polynomialConductor`
   - `matrix_posDef_of_sum_conductor_residuals`
   - `fullWeilCenter_residual_linear_conductor_bound`
   - `exists_completeWeil_linear_conductor_residual_variable_rate`
   - `exists_tiltedUnitSpline_linear_conductor_residual_variable_rate`
   - `sharpenedPowerLogExponent`
   - `sharpenedPowerLogExponent_pos`
   - `powerLogPositivityExponent_lt_sharpened`
   - `one_div_36_lt_sharpened`
   - `exists_fullPrimeMatrix_orthog_inner_defect_localized`
   - `eventually_tiltedUnitSpline_spectralFloorWeilMatrix_posDef_sharpened`
   - `eventually_tiltedUnitSpline_completeWeilEnergy_ge_spectral_floor_sharpened`
   - `eventually_tiltedUnitSpline_completeWeilMatrix_posDef_sharpened`
   - `eventually_tiltedUnitSpline_weilQuad_nonneg_sharpened`
   - `exists_tiltedUnitSpline_completeWeilEnergy_ge_poleDefect_reserve_sharpened`
   - `eventually_tiltedUnitSpline_nonpositiveConductors_below_rpow_subset_polylog`
   - `eventually_tiltedUnitSpline_all_conductors_pos_sharpened`

Standalone `lake --old env lean` verification passed on both modules with exit code `0`; `#print axioms` on all public theorems reports `[propext, Classical.choice, Quot.sound]`.
