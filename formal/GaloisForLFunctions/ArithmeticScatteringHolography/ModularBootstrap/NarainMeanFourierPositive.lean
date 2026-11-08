import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanFourierSource

/-!
# The positive-frequency tail of the Narain source profile

Exponential large-height heat decay bounds the height-weighted source.
Exact main-term subtraction then gives exponential Fourier decay on the positive ray.
-/

open Complex RHTower MeasureTheory Filter Topology
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- Exponential large-height decay bounds the height-weighted actual average. -/
theorem exists_eventually_height_mul_narainScalarHeatAverage_bound (Y Z : Height) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ y : ℝ in atTop, y * ‖narainScalarHeatAverage Y Z y‖ ≤ D := by
  obtain ⟨c, hc, htop⟩ := exists_isBigO_narainScalarHeatAverage_exp Y Z
  obtain ⟨C, hb⟩ := htop.bound
  refine ⟨max C 0 / c, by positivity, ?_⟩
  filter_upwards [hb, eventually_ge_atTop (0 : ℝ)] with y hy hy0
  rw [Real.norm_of_nonneg (Real.exp_nonneg _)] at hy
  have he : y * Real.exp (-c * y) ≤ 1 / c := by
    apply (le_div_iff₀ hc).mpr
    have hlinear : c * y ≤ Real.exp (c * y) := by
      have h := Real.add_one_le_exp (c * y)
      linarith only [h]
    calc
      _ = (c * y) * Real.exp (-c * y) := by ring
      _ ≤ Real.exp (c * y) * Real.exp (-c * y) :=
        mul_le_mul_of_nonneg_right hlinear (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add, show c * y + -c * y = 0 by ring, Real.exp_zero]
  calc
    _ ≤ y * (max C 0 * Real.exp (-c * y)) :=
      mul_le_mul_of_nonneg_left
        (hy.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _))) hy0
    _ = max C 0 * (y * Real.exp (-c * y)) := by ring
    _ ≤ max C 0 * (1 / c) := mul_le_mul_of_nonneg_left he (le_max_right _ _)
    _ = _ := by ring

/-- The physical large-height source gives exponential decay of the positive Fourier ray. -/
theorem exists_narainMeanBoundaryFourier_positive_bound (Y Z : Height) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ L : ℝ in atTop,
      ‖narainMeanBoundaryFourier Y Z L‖ ≤ C * (1 + L) * Real.exp (-(L / 2)) := by
  obtain ⟨D, hD, hb⟩ := exists_eventually_height_mul_narainScalarHeatAverage_bound Y Z
  let a : ℝ := 3 / Real.pi
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  refine ⟨D + a + ‖narainAverageConstant Y Z‖, by positivity, ?_⟩
  filter_upwards [Real.tendsto_exp_atTop.eventually hb, eventually_ge_atTop (0 : ℝ)] with L hA hL
  have hnorm := norm_narainMeanBoundaryFourier_log Y Z (Real.exp_pos L)
  rw [Real.log_exp] at hnorm
  have hden : Real.exp L ^ ((1 : ℝ) / 2) = Real.exp (L / 2) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos L), Real.log_exp]
    congr 1
    ring
  rw [hnorm, hden]
  have htri := (norm_sub_le
    ((Real.exp L : ℂ) * narainScalarHeatAverage Y Z (Real.exp L) +
      (3 / (Real.pi : ℂ)) * (L : ℂ)) (narainAverageConstant Y Z)).trans
    (add_le_add (norm_add_le
      ((Real.exp L : ℂ) * narainScalarHeatAverage Y Z (Real.exp L))
      ((3 / (Real.pi : ℂ)) * (L : ℂ))) le_rfl)
  simp only [norm_mul, norm_div, Complex.norm_ofNat,
    Complex.norm_of_nonneg (Real.exp_nonneg L), Complex.norm_of_nonneg Real.pi_pos.le,
    Complex.norm_of_nonneg hL] at htri
  have hr : ‖(Real.exp L : ℂ) * narainScalarHeatAverage Y Z (Real.exp L) +
      (3 / (Real.pi : ℂ)) * (L : ℂ) - narainAverageConstant Y Z‖ ≤
        (D + a + ‖narainAverageConstant Y Z‖) * (1 + L) := by
    have hpoly : D + a * L + ‖narainAverageConstant Y Z‖ ≤
        (D + a + ‖narainAverageConstant Y Z‖) * (1 + L) := by
      nlinarith only [mul_nonneg hD hL, mul_nonneg (norm_nonneg (narainAverageConstant Y Z)) hL, ha]
    exact (htri.trans (by dsimp only [a]; linarith only [hA])).trans hpoly
  calc
    _ ≤ ((D + a + ‖narainAverageConstant Y Z‖) * (1 + L)) / Real.exp (L / 2) :=
      div_le_div_of_nonneg_right hr (Real.exp_nonneg _)
    _ = _ := by rw [div_eq_mul_inv, ← Real.exp_neg]

#print axioms exists_eventually_height_mul_narainScalarHeatAverage_bound
#print axioms exists_narainMeanBoundaryFourier_positive_bound
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
