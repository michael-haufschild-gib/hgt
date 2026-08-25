/- Sharp beta-coefficient asymptotic for the dyadic Mangoldt-square hyperbola. -/

import GaloisForLFunctions.RHTower.Sieve.VonMangoldtSquareDyadicHyperbola

noncomputable section

open Filter Topology

namespace RHTower.Sieve

private theorem tendsto_inv_natCast_atTop_zero' :
    Tendsto (fun M : ℕ => (1 : ℝ) / (M : ℝ)) atTop (𝓝 0) :=
  Tendsto.div_atTop tendsto_const_nhds tendsto_natCast_atTop_atTop

private theorem tendsto_shiftedCube_div_fourth_zero :
    Tendsto (fun M : ℕ => ((M : ℝ) + 1) ^ 3 / (M : ℝ) ^ 4)
      atTop (𝓝 0) := by
  have hinv := tendsto_inv_natCast_atTop_zero'
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have hbase := (hone.add hinv).pow 3 |>.mul hinv
  have hfinal : Tendsto (fun M : ℕ =>
      (1 + 1 / (M : ℝ)) ^ 3 * (1 / (M : ℝ))) atTop
      (𝓝 ((1 + 0) ^ 3 * 0)) := hbase
  simpa only [add_zero, one_pow, one_mul] using hfinal.congr' (by
    filter_upwards [eventually_gt_atTop 0] with M hM
    have hMne : (M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
    field_simp [hMne]
    )

private theorem tendsto_dyadicQuadraticMain_div_fourth :
    Tendsto (fun M : ℕ =>
      (vonMangoldtSquareDyadicQuadraticCoeff ^ 2 *
        ((M : ℝ) * ((M : ℝ) + 1) *
          ((M : ℝ) ^ 2 + (M : ℝ) + 1) / 6)) /
        (M : ℝ) ^ 4) atTop
      (𝓝 (vonMangoldtSquareDyadicQuadraticCoeff ^ 2 / 6)) := by
  have hinv := tendsto_inv_natCast_atTop_zero'
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have hfactor := ((hone.add hinv).mul
    ((hone.add hinv).add (hinv.pow 2)))
  have hscaled := hfactor.const_mul
    (vonMangoldtSquareDyadicQuadraticCoeff ^ 2 / 6)
  have hfinal : Tendsto (fun M : ℕ =>
      (vonMangoldtSquareDyadicQuadraticCoeff ^ 2 / 6) *
        ((1 + 1 / (M : ℝ)) *
          (1 + 1 / (M : ℝ) + (1 / (M : ℝ)) ^ 2))) atTop
      (𝓝 ((vonMangoldtSquareDyadicQuadraticCoeff ^ 2 / 6) *
        ((1 + 0) * (1 + 0 + 0 ^ 2)))) := hscaled
  have hfinal' : Tendsto (fun M : ℕ =>
      (vonMangoldtSquareDyadicQuadraticCoeff ^ 2 / 6) *
        ((1 + 1 / (M : ℝ)) *
          (1 + 1 / (M : ℝ) + (1 / (M : ℝ)) ^ 2))) atTop
      (𝓝 (vonMangoldtSquareDyadicQuadraticCoeff ^ 2 / 6)) := by
    simpa using hfinal
  apply hfinal'.congr'
  filter_upwards [eventually_gt_atTop 0] with M hM
  have hMne : (M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  field_simp [hMne]

private theorem tendsto_quadraticIncrementConvolution_dyadicProfile_div_fourth :
    Tendsto (fun M : ℕ =>
      quadraticIncrementConvolution vonMangoldtSquareDyadicProfile M /
        (M : ℝ) ^ 4) atTop
      (𝓝 (vonMangoldtSquareDyadicQuadraticCoeff ^ 2 / 6)) := by
  let main : ℕ → ℝ := fun M =>
    vonMangoldtSquareDyadicQuadraticCoeff ^ 2 *
      ((M : ℝ) * ((M : ℝ) + 1) *
        ((M : ℝ) ^ 2 + (M : ℝ) + 1) / 6)
  let err : ℕ → ℝ := fun M =>
    quadraticIncrementConvolution vonMangoldtSquareDyadicProfile M /
        (M : ℝ) ^ 4 - main M / (M : ℝ) ^ 4
  have hmajor : Tendsto (fun M : ℕ =>
      (5 * vonMangoldtSquareDyadicLinearError *
        (vonMangoldtSquareDyadicQuadraticCoeff +
          vonMangoldtSquareDyadicLinearError)) *
        (((M : ℝ) + 1) ^ 3 / (M : ℝ) ^ 4)) atTop (𝓝 0) := by
    simpa using tendsto_shiftedCube_div_fourth_zero.const_mul
      (5 * vonMangoldtSquareDyadicLinearError *
        (vonMangoldtSquareDyadicQuadraticCoeff +
          vonMangoldtSquareDyadicLinearError))
  have herr : Tendsto err atTop (𝓝 0) := by
    apply squeeze_zero_norm' ?_ hmajor
    filter_upwards [eventually_gt_atTop 0] with M hM
    have hden : 0 < (M : ℝ) ^ 4 := pow_pos (by exact_mod_cast hM) 4
    simp only [err]
    rw [← sub_div, Real.norm_eq_abs, abs_div, abs_of_pos hden]
    simp only [main]
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right
      (abs_quadraticIncrementConvolution_vonMangoldtSquareDyadicProfile_sub_le M)
      hden.le
  have hmain : Tendsto (fun M => main M / (M : ℝ) ^ 4) atTop
      (𝓝 (vonMangoldtSquareDyadicQuadraticCoeff ^ 2 / 6)) :=
    tendsto_dyadicQuadraticMain_div_fourth
  have htotal := hmain.add herr
  have htotal' : Tendsto (fun M => main M / (M : ℝ) ^ 4 + err M) atTop
      (𝓝 (vonMangoldtSquareDyadicQuadraticCoeff ^ 2 / 6)) := by
    simpa using htotal
  apply htotal'.congr'
  filter_upwards [] with M
  simp only [err, main]
  ring

private theorem tendsto_quadraticIncrementConvolution_dyadicProfile_pred_div_fourth :
    Tendsto (fun M : ℕ =>
      quadraticIncrementConvolution vonMangoldtSquareDyadicProfile (M - 1) /
        (M : ℝ) ^ 4) atTop
      (𝓝 (vonMangoldtSquareDyadicQuadraticCoeff ^ 2 / 6)) := by
  apply (Filter.tendsto_add_atTop_iff_nat 1).mp
  have hQ := tendsto_quadraticIncrementConvolution_dyadicProfile_div_fourth
  have hinv := tendsto_inv_natCast_atTop_zero'
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have hratioBase := (hone.add hinv).inv₀ (by norm_num : (1 + 0 : ℝ) ≠ 0)
  have hratio := hratioBase.pow 4
  have hprod := hQ.mul hratio
  have hfinal : Tendsto (fun n : ℕ =>
      (quadraticIncrementConvolution vonMangoldtSquareDyadicProfile n /
          (n : ℝ) ^ 4) *
        (1 + 1 / (n : ℝ))⁻¹ ^ 4) atTop
      (𝓝 (vonMangoldtSquareDyadicQuadraticCoeff ^ 2 / 6)) := by
    simpa using hprod
  apply hfinal.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hs : n + 1 - 1 = n := by omega
  rw [hs]
  push_cast
  field_simp [hnne]

/-- Sharp dyadic hyperbola asymptotic before converting from dyadic index to logarithmic height. -/
theorem tendsto_vonMangoldtSquareHyperbolaMass_pow_two_div_fourth :
    Tendsto (fun M : ℕ =>
      vonMangoldtSquareHyperbolaMass (2 ^ M) / (M : ℝ) ^ 4) atTop
      (𝓝 (vonMangoldtSquareDyadicQuadraticCoeff ^ 2 / 6)) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_quadraticIncrementConvolution_dyadicProfile_pred_div_fourth
    tendsto_quadraticIncrementConvolution_dyadicProfile_div_fourth
  · filter_upwards [eventually_gt_atTop 0] with M hM
    exact div_le_div_of_nonneg_right
      (quadraticIncrementConvolution_pred_le_vonMangoldtSquareHyperbolaMass_pow_two M)
      (pow_nonneg (Nat.cast_nonneg M) 4)
  · filter_upwards [eventually_gt_atTop 0] with M hM
    exact div_le_div_of_nonneg_right
      (vonMangoldtSquareHyperbolaMass_pow_two_le_quadraticIncrementConvolution M)
      (pow_nonneg (Nat.cast_nonneg M) 4)

theorem vonMangoldtSquareDyadicQuadraticCoeff_sq_div_six :
    vonMangoldtSquareDyadicQuadraticCoeff ^ 2 / 6 = Real.log 2 ^ 4 / 24 := by
  rw [vonMangoldtSquareDyadicQuadraticCoeff]
  ring

/-- The dyadic logarithmic normalization has the sharp beta coefficient `1/24`. -/
theorem tendsto_vonMangoldtSquareHyperbolaMass_pow_two_div_logFourth :
    Tendsto (fun M : ℕ =>
      vonMangoldtSquareHyperbolaMass (2 ^ M) /
        ((M : ℝ) * Real.log 2) ^ 4) atTop (𝓝 (1 / 24 : ℝ)) := by
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have h := tendsto_vonMangoldtSquareHyperbolaMass_pow_two_div_fourth.mul_const
    (Real.log 2 ^ 4)⁻¹
  rw [vonMangoldtSquareDyadicQuadraticCoeff_sq_div_six] at h
  convert h using 1
  · funext M
    by_cases hM : M = 0
    · subst M
      norm_num
    · have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM
      field_simp [hMR, hlog]
  · field_simp [hlog]

end RHTower.Sieve
