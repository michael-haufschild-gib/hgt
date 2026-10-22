import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovStrongScaleMain
import GaloisForLFunctions.RHTower.SmoothAFEZetaCriticalDetectorFullLongMomentExpansion

/-!
# Strong-scale asymptotics of the differentiated Barban–Vehov long moments

Take the long window `(L, L M]` at the strong scale `L = M³`. The exact base, cross and
differentiated Barban–Vehov lcm forms are compared with their polynomial main terms with
explicit errors `3/M`, `30/M` and `300/M` after normalization by `log² M`, `log³ M` and `log⁴ M`.
Consequently the harmonic moments `∑_{M³ < k ≤ M⁴} b_M(k)² / k`, the cross moment with the
log-differentiated coefficient, and the differentiated moment converge after normalization to
`1`, `-(3 + 1/2)` and `3² + 3 + 2/3`. The full differentiated Levinson detector energy at
`λ = r / log M` therefore converges to `1 - 7r + (38/3) r²`.

## Main results

- `abs_barbanVehovFullLongBaseLcm_cube_div_log_sq_sub_polynomial_le`,
  `abs_barbanVehovFullLongCrossLcm_cube_div_log_cube_sub_polynomial_le`,
  `abs_barbanVehovFullLongDerivativeLcm_cube_div_log_four_sub_polynomial_le`: explicit error
  bounds `3/M`, `30/M`, `300/M` for `M ≥ 8`.
- `tendsto_barbanVehovFullLongBaseLcm_cube_div_log_sq_one`,
  `tendsto_barbanVehovFullLongCrossLcm_cube_div_log_cube`,
  `tendsto_barbanVehovFullLongDerivativeLcm_cube_div_log_four`: limits `1`, `-(3 + 1/2)`,
  `3² + 3 + 2/3` of the normalized lcm forms.
- `tendsto_levinsonCriticalDetectorFullLongBaseMoment_cube_div_log_sq_one`,
  `tendsto_levinsonCriticalDetectorFullLongCrossMoment_cube_div_log_cube`,
  `tendsto_levinsonCriticalDetectorFullLongDerivativeMoment_cube_div_log_four`: the same limits for
  the harmonic moments of the Barban–Vehov coefficients.
- `tendsto_levinsonCriticalDetectorFullLongEnergy_cube`: the full differentiated long energy at
  `λ = r / log M` tends to `1 - 7r + (38/3) r²`.

## Hypotheses

All results are unconditional; the explicit error bounds assume `M ≥ 8`.
-/

open Filter Topology

namespace RHTower.Sieve

noncomputable section

/-- For `M ≥ 2`, `log(M³ M + 1) ≤ 5 log M`. -/
theorem log_cube_mul_add_one_le_five_log
    {M : ℕ} (hM : 2 ≤ M) :
    Real.log (M ^ (3 : ℕ) * M + 1 : ℕ) ≤ 5 * Real.log M := by
  have hprodPos : 0 < M ^ (3 : ℕ) * M := by positivity
  have hprod1 : 1 ≤ M ^ (3 : ℕ) * M := hprodPos
  have hpow : M ^ (3 : ℕ) * M + 1 ≤ M ^ (5 : ℕ) := by
    calc
      M ^ (3 : ℕ) * M + 1 ≤ M ^ (3 : ℕ) * M + M ^ (3 : ℕ) * M := Nat.add_le_add_left hprod1 _
      _ = 2 * (M ^ (3 : ℕ) * M) := by ring
      _ ≤ M * (M ^ (3 : ℕ) * M) := Nat.mul_le_mul_right _ hM
      _ = M ^ (5 : ℕ) := by ring
  have hleftPos : (0 : ℝ) < ((M ^ (3 : ℕ) * M + 1 : ℕ) : ℝ) := by positivity
  have hpowR : ((M ^ (3 : ℕ) * M + 1 : ℕ) : ℝ) ≤ ((M ^ (5 : ℕ) : ℕ) : ℝ) := by
    exact_mod_cast hpow
  have hlog := Real.log_le_log hleftPos hpowR
  rw [show ((M ^ (5 : ℕ) : ℕ) : ℝ) = (M : ℝ) ^ (5 : ℕ) by norm_num, Real.log_pow] at hlog
  norm_num at hlog
  norm_num [Nat.cast_pow]
  exact hlog

/-- For `M ≥ 8`, the base lcm form at `L = M³`, normalized by `log² M`, is within `3/M` of its
normalized polynomial main term. -/
theorem abs_barbanVehovFullLongBaseLcm_cube_div_log_sq_sub_polynomial_le
    {M : ℕ} (hM : 8 ≤ M) :
    |barbanVehovFullLongBaseLcm (M ^ (3 : ℕ)) M / Real.log M ^ (2 : ℕ) -
        barbanVehovLongBasePolynomialMain M / Real.log M ^ (2 : ℕ)| ≤
      3 / (M : ℝ) := by
  have hM0 : 0 < M := by omega
  have hlog : Real.log (M : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (by omega : 1 < M))).ne'
  have herr := abs_barbanVehovFullLongBaseLcm_cube_sub_continuous_le hM
  rw [barbanVehovFullLongBaseContinuous_cube_eq_polynomialMain hM0] at herr
  rw [← sub_div, abs_div, abs_of_nonneg (sq_nonneg (Real.log M))]
  calc
    |barbanVehovFullLongBaseLcm (M ^ (3 : ℕ)) M -
        barbanVehovLongBasePolynomialMain M| / Real.log M ^ (2 : ℕ) ≤
      (((M : ℝ) * Real.log M) ^ (2 : ℕ) * (3 / ((M ^ (3 : ℕ) : ℕ) : ℝ))) /
        Real.log M ^ (2 : ℕ) := div_le_div_of_nonneg_right herr (sq_nonneg _)
    _ = 3 / (M : ℝ) := by
      norm_num [Nat.cast_pow]
      field_simp [hlog]

/-- For `M ≥ 8`, the cross lcm form at `L = M³`, normalized by `log³ M`, is within `30/M` of its
normalized polynomial main term. -/
theorem abs_barbanVehovFullLongCrossLcm_cube_div_log_cube_sub_polynomial_le
    {M : ℕ} (hM : 8 ≤ M) :
    |barbanVehovFullLongCrossLcm (M ^ (3 : ℕ)) M / Real.log M ^ (3 : ℕ) -
        barbanVehovLongCrossPolynomialMain 3 M / Real.log M ^ (3 : ℕ)| ≤
      30 / (M : ℝ) := by
  have hM0 : 0 < M := by omega
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM0
  have hlogPos : 0 < Real.log (M : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  have hlog : Real.log (M : ℝ) ≠ 0 := hlogPos.ne'
  have hK := log_cube_mul_add_one_le_five_log (by omega : 2 ≤ M)
  have herr := abs_barbanVehovFullLongCrossLcm_cube_sub_continuous_le hM
  rw [barbanVehovFullLongCrossContinuous_cube_eq_polynomialMain hM0] at herr
  rw [← sub_div, abs_div, abs_of_nonneg (pow_nonneg hlogPos.le 3)]
  calc
    |barbanVehovFullLongCrossLcm (M ^ (3 : ℕ)) M -
        barbanVehovLongCrossPolynomialMain 3 M| / Real.log M ^ (3 : ℕ) ≤
      (((M : ℝ) * Real.log M) ^ (2 : ℕ) *
          (6 * Real.log (M ^ (3 : ℕ) * M + 1 : ℕ) / ((M ^ (3 : ℕ) : ℕ) : ℝ))) /
        Real.log M ^ (3 : ℕ) := div_le_div_of_nonneg_right herr (pow_nonneg hlogPos.le 3)
    _ = 6 * Real.log (M ^ (3 : ℕ) * M + 1 : ℕ) /
        ((M : ℝ) * Real.log M) := by
      norm_num [Nat.cast_pow]
      field_simp [hlog, hMR.ne']
    _ ≤ 30 / (M : ℝ) := by
      rw [div_le_iff₀ (mul_pos hMR hlogPos), div_eq_mul_inv]
      field_simp [hMR.ne']
      nlinarith

/-- For `M ≥ 8`, the differentiated lcm form at `L = M³`, normalized by `log⁴ M`, is within `300/M`
of its normalized polynomial main term. -/
theorem abs_barbanVehovFullLongDerivativeLcm_cube_div_log_four_sub_polynomial_le
    {M : ℕ} (hM : 8 ≤ M) :
    |barbanVehovFullLongDerivativeLcm (M ^ (3 : ℕ)) M / Real.log M ^ (4 : ℕ) -
        barbanVehovLongDerivativePolynomialMain 3 M / Real.log M ^ (4 : ℕ)| ≤
      300 / (M : ℝ) := by
  have hM0 : 0 < M := by omega
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM0
  have hlogPos : 0 < Real.log (M : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  have hlog : Real.log (M : ℝ) ≠ 0 := hlogPos.ne'
  let K := Real.log (M ^ (3 : ℕ) * M + 1 : ℕ)
  have hK0 : 0 ≤ K := by
    dsimp [K]
    exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ M ^ (3 : ℕ) * M + 1))
  have hK : K ≤ 5 * Real.log M :=
    log_cube_mul_add_one_le_five_log (by omega : 2 ≤ M)
  have hKsq : K ^ (2 : ℕ) ≤ 25 * Real.log M ^ (2 : ℕ) := by
    have h1 := mul_le_mul_of_nonneg_left hK hK0
    have h2 := mul_le_mul_of_nonneg_right hK (by positivity : 0 ≤ 5 * Real.log M)
    nlinarith
  have herr := abs_barbanVehovFullLongDerivativeLcm_cube_sub_continuous_le hM
  rw [barbanVehovFullLongDerivativeContinuous_cube_eq_polynomialMain hM0] at herr
  rw [← sub_div, abs_div, abs_of_nonneg (pow_nonneg hlogPos.le 4)]
  calc
    |barbanVehovFullLongDerivativeLcm (M ^ (3 : ℕ)) M -
        barbanVehovLongDerivativePolynomialMain 3 M| / Real.log M ^ (4 : ℕ) ≤
      (((M : ℝ) * Real.log M) ^ (2 : ℕ) *
          (12 * Real.log (M ^ (3 : ℕ) * M + 1 : ℕ) ^ (2 : ℕ) / ((M ^ (3 : ℕ) : ℕ) : ℝ))) /
        Real.log M ^ (4 : ℕ) := div_le_div_of_nonneg_right herr (pow_nonneg hlogPos.le 4)
    _ = 12 * K ^ (2 : ℕ) / ((M : ℝ) * Real.log M ^ (2 : ℕ)) := by
      dsimp [K]
      norm_num [Nat.cast_pow]
      field_simp [hlog, hMR.ne']
    _ ≤ 300 / (M : ℝ) := by
      rw [div_le_iff₀ (mul_pos hMR (sq_pos_of_pos hlogPos))]
      rw [div_eq_mul_inv]
      field_simp [hMR.ne']
      nlinarith

private theorem tendsto_const_div_nat (c : ℝ) :
    Tendsto (fun M : ℕ => c / (M : ℝ)) atTop (𝓝 0) := by
  exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop

/-- The base lcm form at `L = M³` divided by `log² M` tends to `1`. -/
theorem tendsto_barbanVehovFullLongBaseLcm_cube_div_log_sq_one :
    Tendsto (fun M : ℕ =>
      barbanVehovFullLongBaseLcm (M ^ (3 : ℕ)) M / Real.log M ^ (2 : ℕ))
      atTop (𝓝 1) := by
  have habs : Tendsto (fun M : ℕ =>
      |barbanVehovFullLongBaseLcm (M ^ (3 : ℕ)) M / Real.log M ^ (2 : ℕ) -
        barbanVehovLongBasePolynomialMain M / Real.log M ^ (2 : ℕ)|) atTop (𝓝 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      ?_ (tendsto_const_div_nat 3)
    filter_upwards [eventually_ge_atTop 8] with M hM
    exact abs_barbanVehovFullLongBaseLcm_cube_div_log_sq_sub_polynomial_le hM
  have hdiff : Tendsto (fun M : ℕ =>
      barbanVehovFullLongBaseLcm (M ^ (3 : ℕ)) M / Real.log M ^ (2 : ℕ) -
        barbanVehovLongBasePolynomialMain M / Real.log M ^ (2 : ℕ)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs] using habs
  simpa only [sub_add_cancel, zero_add] using
    hdiff.add tendsto_barbanVehovLongBasePolynomialMain_div_log_sq_one

/-- The cross lcm form at `L = M³` divided by `log³ M` tends to `-(3 + 1/2)`. -/
theorem tendsto_barbanVehovFullLongCrossLcm_cube_div_log_cube :
    Tendsto (fun M : ℕ =>
      barbanVehovFullLongCrossLcm (M ^ (3 : ℕ)) M / Real.log M ^ (3 : ℕ))
      atTop (𝓝 (-(3 + 1 / 2 : ℝ))) := by
  have habs : Tendsto (fun M : ℕ =>
      |barbanVehovFullLongCrossLcm (M ^ (3 : ℕ)) M / Real.log M ^ (3 : ℕ) -
        barbanVehovLongCrossPolynomialMain 3 M / Real.log M ^ (3 : ℕ)|) atTop (𝓝 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      ?_ (tendsto_const_div_nat 30)
    filter_upwards [eventually_ge_atTop 8] with M hM
    exact abs_barbanVehovFullLongCrossLcm_cube_div_log_cube_sub_polynomial_le hM
  have hdiff : Tendsto (fun M : ℕ =>
      barbanVehovFullLongCrossLcm (M ^ (3 : ℕ)) M / Real.log M ^ (3 : ℕ) -
        barbanVehovLongCrossPolynomialMain 3 M / Real.log M ^ (3 : ℕ)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs] using habs
  simpa only [sub_add_cancel, zero_add] using
    hdiff.add (tendsto_barbanVehovLongCrossPolynomialMain_div_log_cube 3)

/-- The differentiated lcm form at `L = M³` divided by `log⁴ M` tends to `3² + 3 + 2/3`. -/
theorem tendsto_barbanVehovFullLongDerivativeLcm_cube_div_log_four :
    Tendsto (fun M : ℕ =>
      barbanVehovFullLongDerivativeLcm (M ^ (3 : ℕ)) M / Real.log M ^ (4 : ℕ))
      atTop (𝓝 ((3 : ℝ) ^ (2 : ℕ) + 3 + 2 / 3)) := by
  have habs : Tendsto (fun M : ℕ =>
      |barbanVehovFullLongDerivativeLcm (M ^ (3 : ℕ)) M / Real.log M ^ (4 : ℕ) -
        barbanVehovLongDerivativePolynomialMain 3 M / Real.log M ^ (4 : ℕ)|) atTop (𝓝 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      ?_ (tendsto_const_div_nat 300)
    filter_upwards [eventually_ge_atTop 8] with M hM
    exact abs_barbanVehovFullLongDerivativeLcm_cube_div_log_four_sub_polynomial_le hM
  have hdiff : Tendsto (fun M : ℕ =>
      barbanVehovFullLongDerivativeLcm (M ^ (3 : ℕ)) M / Real.log M ^ (4 : ℕ) -
        barbanVehovLongDerivativePolynomialMain 3 M / Real.log M ^ (4 : ℕ)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs] using habs
  simpa only [sub_add_cancel, zero_add] using
    hdiff.add (tendsto_barbanVehovLongDerivativePolynomialMain_div_log_four 3)

private theorem self_le_cube {M : ℕ} (hM : 0 < M) : M ≤ M ^ (3 : ℕ) := by
  calc
    M ≤ M * M := Nat.le_mul_of_pos_right M hM
    _ ≤ (M * M) * M := Nat.le_mul_of_pos_right (M * M) hM
    _ = M ^ (3 : ℕ) := by ring

/-- The harmonic moment `∑_{M³ < k ≤ M⁴} b_M(k)² / k` divided by `log² M` tends to `1`. -/
theorem tendsto_levinsonCriticalDetectorFullLongBaseMoment_cube_div_log_sq_one :
    Tendsto (fun M : ℕ =>
      RHTower.levinsonCriticalDetectorFullLongBaseMoment (M ^ (3 : ℕ)) M /
        Real.log M ^ (2 : ℕ)) atTop (𝓝 1) := by
  refine tendsto_barbanVehovFullLongBaseLcm_cube_div_log_sq_one.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with M hM
  rw [levinsonCriticalDetectorFullLongBaseMoment_eq_lcm
    (by omega) (self_le_cube (by omega))]

/-- The cross harmonic moment of the base and log-differentiated Barban–Vehov coefficients on
`(M³, M⁴]`, divided by `log³ M`, tends to `-(3 + 1/2)`. -/
theorem tendsto_levinsonCriticalDetectorFullLongCrossMoment_cube_div_log_cube :
    Tendsto (fun M : ℕ =>
      RHTower.levinsonCriticalDetectorFullLongCrossMoment (M ^ (3 : ℕ)) M /
        Real.log M ^ (3 : ℕ)) atTop (𝓝 (-(3 + 1 / 2 : ℝ))) := by
  refine tendsto_barbanVehovFullLongCrossLcm_cube_div_log_cube.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with M hM
  rw [levinsonCriticalDetectorFullLongCrossMoment_eq_lcm
    (by omega) (self_le_cube (by omega))]

/-- The differentiated harmonic moment on `(M³, M⁴]` divided by `log⁴ M` tends to `3² + 3 + 2/3`. -/
theorem tendsto_levinsonCriticalDetectorFullLongDerivativeMoment_cube_div_log_four :
    Tendsto (fun M : ℕ =>
      RHTower.levinsonCriticalDetectorFullLongDerivativeMoment (M ^ (3 : ℕ)) M /
        Real.log M ^ (4 : ℕ)) atTop (𝓝 ((3 : ℝ) ^ (2 : ℕ) + 3 + 2 / 3)) := by
  refine tendsto_barbanVehovFullLongDerivativeLcm_cube_div_log_four.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with M hM
  rw [levinsonCriticalDetectorFullLongDerivativeMoment_eq_lcm
    (by omega) (self_le_cube (by omega))]

/-- The full differentiated long Levinson detector energy on `(M³, M⁴]` at `λ = r / log M` tends to
`1 - 7r + (38/3) r²`. -/
theorem tendsto_levinsonCriticalDetectorFullLongEnergy_cube (r : ℝ) :
    Tendsto (fun M : ℕ =>
      RHTower.levinsonCriticalDetectorFullLongEnergy
        (r / Real.log M) (M ^ (3 : ℕ)) M) atTop
      (𝓝 (1 - 7 * r + (38 / 3 : ℝ) * r ^ (2 : ℕ))) := by
  have hbase := tendsto_levinsonCriticalDetectorFullLongBaseMoment_cube_div_log_sq_one
  have hcross := tendsto_levinsonCriticalDetectorFullLongCrossMoment_cube_div_log_cube
  have hderiv := tendsto_levinsonCriticalDetectorFullLongDerivativeMoment_cube_div_log_four
  have hlim := (hbase.add (hcross.const_mul (2 * r))).add
    (hderiv.const_mul (r ^ (2 : ℕ)))
  have hfun : Tendsto (fun M : ℕ =>
      RHTower.levinsonCriticalDetectorFullLongEnergy
        (r / Real.log M) (M ^ (3 : ℕ)) M) atTop
      (𝓝 (1 + 2 * r * (-(3 + 1 / 2)) +
        r ^ (2 : ℕ) * ((3 : ℝ) ^ (2 : ℕ) + 3 + 2 / 3))) := by
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with M hM
    have hlog : Real.log (M : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hM)).ne'
    change RHTower.levinsonCriticalDetectorFullLongBaseMoment (M ^ (3 : ℕ)) M /
          Real.log M ^ (2 : ℕ) +
        2 * r * (RHTower.levinsonCriticalDetectorFullLongCrossMoment (M ^ (3 : ℕ)) M /
          Real.log M ^ (3 : ℕ)) +
        r ^ (2 : ℕ) * (RHTower.levinsonCriticalDetectorFullLongDerivativeMoment (M ^ (3 : ℕ)) M /
          Real.log M ^ (4 : ℕ)) = _
    rw [RHTower.levinsonCriticalDetectorFullLongEnergy_eq_momentQuadratic
      (r / Real.log M) (M ^ (3 : ℕ)) (by omega)]
    field_simp [hlog]
  convert hfun using 1
  ring

end

end RHTower.Sieve
