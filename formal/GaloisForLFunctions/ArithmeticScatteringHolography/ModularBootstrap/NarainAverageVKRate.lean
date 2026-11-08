import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanVKContour
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainVKAbsorption
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanBoundaryIdentity

/-!
# Quantitative arithmetic saving for the averaged scalar source

The moving contour at logarithmic height retains the Vinogradov–Korobov
profile. Exact Fourier normalization transfers it to the physical remainder.
-/

open Complex RHTower Filter Topology MeasureTheory
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- Exponential Mellin decay allows contour height equal to the logarithmic frequency. -/
theorem exists_narainMeanBoundary_vk_decay (Y Z : Height) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ᶠ L : ℝ in atTop,
      ‖∫ t : ℝ, Complex.exp ((L : ℂ) * ((t : ℂ) * I)) * narainMellinMean Y Z ((t : ℂ) * I)‖ ≤
        C * Real.exp (-(c * L * vkHadamardWidth L)) := by
  obtain ⟨δ, T₀, C, N, hδ, _, _, hC, hcontour⟩ := exists_narainMeanBoundary_vk_contour_bound Y Z
  obtain ⟨D, c, hD, hc, hsaving⟩ := exists_narainVK_saving hδ N
  refine ⟨(C + 1) * D, c, mul_pos (by linarith only [hC]) hD, hc, ?_⟩
  filter_upwards [hsaving, eventually_ge_atTop T₀, eventually_ge_atTop (0 : ℝ)] with L hs hL hL0
  calc
    _ ≤ C * (1 + L) ^ N * narainVKCost L *
        (Real.exp (-(narainVKWidth δ L * L)) + Real.exp (-(Real.pi * L / 4))) :=
      hcontour L L hL0 hL
    _ = C * ((1 + L) ^ N * narainVKCost L *
        (Real.exp (-(narainVKWidth δ L * L)) + Real.exp (-(Real.pi * L / 4)))) := by ring
    _ ≤ C * (D * Real.exp (-(c * L * vkHadamardWidth L))) := mul_le_mul_of_nonneg_left hs hC
    _ = C * D * Real.exp (-(c * L * vkHadamardWidth L)) := by ring
    _ ≤ _ := by gcongr; linarith

/-- Every fixed positive target-height pair has an unconditional saving beyond its square-root remainder. -/
theorem narainScalarHeatAverage_vk_rate (Y Z : Height) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ᶠ y : ℝ in 𝓝[>] 0,
      ‖(y : ℂ) * narainScalarHeatAverage Y Z y +
        (3 / (Real.pi : ℂ)) * (Real.log y : ℂ) - narainAverageConstant Y Z‖ ≤
          C * y ^ ((1 : ℝ) / 2) *
            Real.exp (-(c * (-Real.log y) * vkHadamardWidth (-Real.log y))) := by
  obtain ⟨C, c, hC, hc, hdecay⟩ := exists_narainMeanBoundary_vk_decay Y Z
  have hL : Tendsto (fun y : ℝ => -Real.log y) (𝓝[>] 0) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  refine ⟨C / (2 * Real.pi), c, div_pos hC (by positivity), hc, ?_⟩
  filter_upwards [hL.eventually hdecay, self_mem_nhdsWithin] with y hbound hy
  have hy0 : 0 < y := hy
  rw [norm_narainScalarHeatAverage_remainder_eq Y Z hy0]
  calc
    _ ≤ y ^ ((1 : ℝ) / 2) / (2 * Real.pi) *
        (C * Real.exp (-(c * (-Real.log y) * vkHadamardWidth (-Real.log y)))) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by ring

/-- The quantitative saving in elementary logarithmic form, with `L=log(1/y)`. -/
theorem narainScalarHeatAverage_vk_log_rate (Y Z : Height) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ᶠ y : ℝ in 𝓝[>] 0,
      let L := -Real.log y
      ‖(y : ℂ) * narainScalarHeatAverage Y Z y +
        (3 / (Real.pi : ℂ)) * (Real.log y : ℂ) - narainAverageConstant Y Z‖ ≤
          C * y ^ ((1 : ℝ) / 2) * Real.exp (-(c * L /
            (Real.log L ^ ((2 : ℝ) / 3) * Real.log (Real.log L) ^ ((5 : ℝ) / 3)))) := by
  obtain ⟨C, c, hC, hc, hrate⟩ := narainScalarHeatAverage_vk_rate Y Z
  have hL : Tendsto (fun y : ℝ => -Real.log y) (𝓝[>] 0) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  refine ⟨C, c / 10 ^ (8 : ℕ), hC, by positivity, ?_⟩
  filter_upwards [hrate, hL.eventually_ge_atTop (Real.exp (Real.exp 1))] with y hy hlarge
  have harg : 0 < -Real.log y := (Real.exp_pos _).trans_le hlarge
  have hl : Real.exp 1 ≤ Real.log (-Real.log y) := by
    rw [← Real.log_exp (Real.exp 1)]
    exact Real.log_le_log (Real.exp_pos _) hlarge
  have hl0 : 0 < Real.log (-Real.log y) := (Real.exp_pos _).trans_le hl
  have hll : 1 ≤ Real.log (Real.log (-Real.log y)) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos _) hl
  have hll0 : 0 ≤ Real.log (Real.log (-Real.log y)) := zero_le_one.trans hll
  have heq : c * (-Real.log y) * vkHadamardWidth (-Real.log y) =
      (c / 10 ^ (8 : ℕ)) * (-Real.log y) /
        (Real.log (-Real.log y) ^ ((2 : ℝ) / 3) *
          Real.log (Real.log (-Real.log y)) ^ ((5 : ℝ) / 3)) := by
    unfold vkHadamardWidth
    rw [show -(2 : ℝ) / 3 = -((2 : ℝ) / 3) by ring,
      show -(5 : ℝ) / 3 = -((5 : ℝ) / 3) by ring,
      Real.rpow_neg hl0.le, Real.rpow_neg hll0]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  dsimp only
  rwa [heq] at hy

#print axioms narainScalarHeatAverage_vk_log_rate

#print axioms exists_narainMeanBoundary_vk_decay
#print axioms narainScalarHeatAverage_vk_rate
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
