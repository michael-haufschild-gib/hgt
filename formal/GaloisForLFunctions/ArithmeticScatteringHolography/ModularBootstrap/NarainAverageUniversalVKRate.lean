import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainAverageVKRate
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainUniversalVKAbsorption

/-!
# One explicit arithmetic exponent for every averaged Narain source

The fixed-width ceiling affects only the onset threshold. Applying the
universal absorption bound to the actual contour gives exponent one over
128, followed by exact Fourier normalization of the physical remainder.
-/

open Complex RHTower Filter Topology MeasureTheory
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- Every target pair shares the same explicit boundary saving exponent. -/
theorem exists_narainMeanBoundary_universal_vk_decay (Y Z : Height) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop,
      ‖∫ t : ℝ, Complex.exp ((L : ℂ) * ((t : ℂ) * I)) * narainMellinMean Y Z ((t : ℂ) * I)‖ ≤
        C * Real.exp (-(L * vkHadamardWidth L / 128)) := by
  obtain ⟨δ, T₀, C, N, hδ, _, _, hC, hcontour⟩ := exists_narainMeanBoundary_vk_contour_bound Y Z
  obtain ⟨D, hD, hsaving⟩ := exists_narainVK_saving_universal hδ N
  refine ⟨(C + 1) * D, mul_pos (by linarith only [hC]) hD, ?_⟩
  filter_upwards [hsaving, eventually_ge_atTop T₀, eventually_ge_atTop (0 : ℝ)] with L hs hL hL0
  calc
    _ ≤ C * (1 + L) ^ N * narainVKCost L *
        (Real.exp (-(narainVKWidth δ L * L)) + Real.exp (-(Real.pi * L / 4))) :=
      hcontour L L hL0 hL
    _ = C * ((1 + L) ^ N * narainVKCost L *
        (Real.exp (-(narainVKWidth δ L * L)) + Real.exp (-(Real.pi * L / 4)))) := by ring
    _ ≤ C * (D * Real.exp (-(L * vkHadamardWidth L / 128))) := mul_le_mul_of_nonneg_left hs hC
    _ = C * D * Real.exp (-(L * vkHadamardWidth L / 128)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (zero_le_one : (0 : ℝ) ≤ 1)) hD.le)
      (Real.exp_nonneg _)

/-- The literal physical remainder has a target-independent arithmetic exponent. -/
theorem narainScalarHeatAverage_universal_vk_rate (Y Z : Height) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ y : ℝ in 𝓝[>] 0,
      ‖(y : ℂ) * narainScalarHeatAverage Y Z y +
        (3 / (Real.pi : ℂ)) * (Real.log y : ℂ) - narainAverageConstant Y Z‖ ≤
          C * y ^ ((1 : ℝ) / 2) *
            Real.exp (-((-Real.log y) * vkHadamardWidth (-Real.log y) / 128)) := by
  obtain ⟨C, hC, hdecay⟩ := exists_narainMeanBoundary_universal_vk_decay Y Z
  have hL : Tendsto (fun y : ℝ => -Real.log y) (𝓝[>] 0) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  refine ⟨C / (2 * Real.pi), div_pos hC (by positivity), ?_⟩
  filter_upwards [hL.eventually hdecay, self_mem_nhdsWithin] with y hbound hy
  have hy0 : 0 < y := hy
  rw [norm_narainScalarHeatAverage_remainder_eq Y Z hy0]
  calc
    _ ≤ y ^ ((1 : ℝ) / 2) / (2 * Real.pi) *
        (C * Real.exp (-((-Real.log y) * vkHadamardWidth (-Real.log y) / 128))) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by ring

/-- Elementary logarithms expose the same numerical exponent constant at every target height. -/
theorem narainScalarHeatAverage_universal_vk_log_rate (Y Z : Height) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ y : ℝ in 𝓝[>] 0,
      let L := -Real.log y
      ‖(y : ℂ) * narainScalarHeatAverage Y Z y +
        (3 / (Real.pi : ℂ)) * (Real.log y : ℂ) - narainAverageConstant Y Z‖ ≤
          C * y ^ ((1 : ℝ) / 2) * Real.exp (-(L /
            (128 * 10 ^ (8 : ℕ) *
              (Real.log L ^ ((2 : ℝ) / 3) * Real.log (Real.log L) ^ ((5 : ℝ) / 3))))) := by
  obtain ⟨C, hC, hrate⟩ := narainScalarHeatAverage_universal_vk_rate Y Z
  have hL : Tendsto (fun y : ℝ => -Real.log y) (𝓝[>] 0) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  refine ⟨C, hC, ?_⟩
  filter_upwards [hrate, hL.eventually_ge_atTop (Real.exp (Real.exp 1))] with y hy hlarge
  have hl : Real.exp 1 ≤ Real.log (-Real.log y) := by
    rw [← Real.log_exp (Real.exp 1)]
    exact Real.log_le_log (Real.exp_pos _) hlarge
  have hl0 : 0 < Real.log (-Real.log y) := (Real.exp_pos _).trans_le hl
  have hll : 1 ≤ Real.log (Real.log (-Real.log y)) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos _) hl
  have heq : (-Real.log y) * vkHadamardWidth (-Real.log y) / 128 =
      (-Real.log y) / (128 * 10 ^ (8 : ℕ) *
        (Real.log (-Real.log y) ^ ((2 : ℝ) / 3) *
          Real.log (Real.log (-Real.log y)) ^ ((5 : ℝ) / 3))) := by
    unfold vkHadamardWidth
    rw [show -(2 : ℝ) / 3 = -((2 : ℝ) / 3) by ring,
      show -(5 : ℝ) / 3 = -((5 : ℝ) / 3) by ring,
      Real.rpow_neg hl0.le, Real.rpow_neg (zero_le_one.trans hll)]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  dsimp only
  rwa [heq] at hy

#print axioms exists_narainMeanBoundary_universal_vk_decay
#print axioms narainScalarHeatAverage_universal_vk_rate
#print axioms narainScalarHeatAverage_universal_vk_log_rate
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
