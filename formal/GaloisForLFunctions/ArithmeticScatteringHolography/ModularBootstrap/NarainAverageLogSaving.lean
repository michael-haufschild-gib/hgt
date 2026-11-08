import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainAverageVKRate

/-!
# Every logarithmic saving for the averaged scalar remainder

The arithmetic exponential saving dominates every fixed polynomial in
logarithmic height, giving little-o estimates with arbitrary logarithmic loss.
-/

open Complex RHTower Filter Topology Asymptotics
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- The arithmetic exponential saving dominates every polynomial in logarithmic height. -/
theorem tendsto_pow_mul_exp_neg_vkWidth {c : ℝ} (hc : 0 < c) (N : ℕ) :
    Tendsto (fun L : ℝ => L ^ N * Real.exp (-(c * L * vkHadamardWidth L))) atTop (𝓝 0) := by
  have hN : 0 < (N : ℝ) + 1 := by positivity
  have heps : 0 < c / ((N : ℝ) + 1) := div_pos hc hN
  have hsmall := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (s := 1) (by norm_num)).bound heps
  have hbound : ∀ᶠ L : ℝ in atTop,
      ‖L ^ N * Real.exp (-(c * L * vkHadamardWidth L))‖ ≤ 1 / L := by
    filter_upwards [hsmall,
      GaloisForLFunctions.ConjugateDiagonalGeometry.WindowPortFlux.eventually_inv_log_le_vkWidth,
      eventually_ge_atTop (3 : ℝ)] with L hs hw hL
    have hL0 : 0 < L := by linarith only [hL]
    have hl : 0 < Real.log L := Real.log_pos (by linarith only [hL])
    change 1 / Real.log L ≤ vkHadamardWidth L at hw
    have hs' : Real.log L ^ 2 ≤ c / ((N : ℝ) + 1) * L := by
      simpa only [Real.rpow_two, Real.rpow_one, Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg (Real.log L)), abs_of_pos hL0] using hs
    have hscaled := mul_le_mul_of_nonneg_left hs' hN.le
    have hcancel : ((N : ℝ) + 1) * (c / ((N : ℝ) + 1) * L) = c * L := by
      field_simp [hN.ne']
    rw [hcancel] at hscaled
    have hlog : ((N : ℝ) + 1) * Real.log L ≤ c * L / Real.log L := by
      apply (le_div_iff₀ hl).mpr
      nlinarith only [hscaled]
    have hwidth : c * L / Real.log L ≤ c * L * vkHadamardWidth L := by
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hw (mul_nonneg hc.le hL0.le)
    have hpow : L ^ (N + 1) ≤ Real.exp (c * L * vkHadamardWidth L) := by
      calc
        _ = Real.exp (((N + 1 : ℕ) : ℝ) * Real.log L) := by
          rw [Real.exp_nat_mul, Real.exp_log hL0]
        _ ≤ _ := Real.exp_le_exp.mpr (by
          simpa only [Nat.cast_add, Nat.cast_one] using hlog.trans hwidth)
    have hprod : L ^ N * Real.exp (-(c * L * vkHadamardWidth L)) * L ≤ 1 := by
      calc
        _ = L ^ (N + 1) * Real.exp (-(c * L * vkHadamardWidth L)) := by
          rw [pow_succ]
          ring
        _ ≤ Real.exp (c * L * vkHadamardWidth L) * Real.exp (-(c * L * vkHadamardWidth L)) :=
          mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _)
        _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    rw [Real.norm_of_nonneg (by positivity)]
    exact (le_div_iff₀ hL0).mpr hprod
  exact squeeze_zero_norm' hbound (Tendsto.div_atTop tendsto_const_nhds tendsto_id)

/-- The actual averaged remainder saves every fixed inverse power of logarithmic height. -/
theorem narainScalarHeatAverage_logarithmic_saving (Y Z : Height) (N : ℕ) :
    (fun y : ℝ => (y : ℂ) * narainScalarHeatAverage Y Z y +
      (3 / (Real.pi : ℂ)) * (Real.log y : ℂ) - narainAverageConstant Y Z)
      =o[𝓝[>] 0] (fun y : ℝ => y ^ ((1 : ℝ) / 2) / (-Real.log y) ^ N) := by
  obtain ⟨C, c, hC, hc, hrate⟩ := narainScalarHeatAverage_vk_rate Y Z
  have hL : Tendsto (fun y : ℝ => -Real.log y) (𝓝[>] 0) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have hprofile := ((tendsto_pow_mul_exp_neg_vkWidth hc N).comp hL).const_mul C
  simp only [Function.comp_apply, mul_zero] at hprofile
  have hquot : Tendsto (fun y : ℝ =>
      ‖(y : ℂ) * narainScalarHeatAverage Y Z y +
        (3 / (Real.pi : ℂ)) * (Real.log y : ℂ) - narainAverageConstant Y Z‖ /
          (y ^ ((1 : ℝ) / 2) / (-Real.log y) ^ N)) (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero_norm' _ hprofile
    filter_upwards [hrate, hL.eventually_gt_atTop (0 : ℝ), self_mem_nhdsWithin] with y hb hLy hy
    have hy0 : 0 < y := hy
    have hp : 0 < y ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hy0 _
    have hpow : 0 < (-Real.log y) ^ N := pow_pos hLy N
    rw [Real.norm_of_nonneg (by positivity)]
    calc
      _ ≤ (C * y ^ ((1 : ℝ) / 2) *
          Real.exp (-(c * (-Real.log y) * vkHadamardWidth (-Real.log y)))) /
            (y ^ ((1 : ℝ) / 2) / (-Real.log y) ^ N) :=
        div_le_div_of_nonneg_right hb (div_nonneg hp.le hpow.le)
      _ = _ := by
        field_simp [hp.ne', hpow.ne']
  rw [← isLittleO_norm_left]
  apply (isLittleO_iff_tendsto' ?_).mpr hquot
  filter_upwards [hL.eventually_gt_atTop (0 : ℝ), self_mem_nhdsWithin] with y hLy hy
  have hpos : 0 < y ^ ((1 : ℝ) / 2) / (-Real.log y) ^ N :=
    div_pos (Real.rpow_pos_of_pos hy _) (pow_pos hLy N)
  exact fun h => (hpos.ne' h).elim

#print axioms tendsto_pow_mul_exp_neg_vkWidth
#print axioms narainScalarHeatAverage_logarithmic_saving
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
