import Mathlib

/-!
# Wirtinger's inequality: the sharp Poincaré constant of one circle

For a `C¹` function on `[a,b]` with equal endpoint values, the mean-square deviation from the
average is at most `((b-a)/2π)²` times the mean square of the derivative.  The constant is the
reciprocal of the first nonzero eigenvalue of the Laplacian on the circle of circumference `b-a`,
and is attained by the first Fourier mode.

The proof is Parseval's identity together with the relation between the Fourier coefficients of a
function and of its derivative, both of which mathlib supplies for `AddCircle`.  mathlib has no
Poincaré or Wirtinger inequality.
-/

open MeasureTheory intervalIntegral Set Complex Real

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The Fourier coefficient of index zero on an interval is the average. -/
theorem fourierCoeffOn_zero_eq_average {a b : ℝ} (hab : a < b) (f : ℝ → ℂ) :
    fourierCoeffOn hab f 0 = (b - a)⁻¹ • ∫ x in a..b, f x := by
  rw [fourierCoeffOn_eq_integral]
  simp [one_div]

private theorem memLp_two_of_continuousOn {a b : ℝ} (hab : a < b) {g : ℝ → ℂ}
    (hg : ContinuousOn g (Set.uIcc a b)) : MemLp g 2 (volume.restrict (Set.Ioc a b)) := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc a b)) := by
    constructor
    rw [Measure.restrict_apply_univ, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  have hsub : Set.Ioc a b ⊆ Set.uIcc a b := by
    rw [Set.uIcc_of_le (le_of_lt hab)]
    exact Set.Ioc_subset_Icc_self
  obtain ⟨C, hC⟩ := (isCompact_uIcc (a := a) (b := b)).exists_bound_of_continuousOn hg
  refine MemLp.of_bound ?_ C ?_
  · exact (hg.mono hsub).aestronglyMeasurable measurableSet_Ioc
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hC x (hsub hx)

/-- **Wirtinger's inequality** on an interval, for a `C¹` function with equal endpoint values.
The mean square deviation from the average is at most `((b-a)/2π)²` times the mean square of the
derivative. -/
theorem wirtinger_intervalIntegral {a b : ℝ} (hab : a < b) {f f' : ℝ → ℂ}
    (hf : ∀ x ∈ Set.uIcc a b, HasDerivAt f (f' x) x)
    (hf'c : ContinuousOn f' (Set.uIcc a b)) (hper : f b = f a) :
    (b - a)⁻¹ * (∫ x in a..b, ‖f x‖ ^ 2) - ‖(b - a)⁻¹ • ∫ x in a..b, f x‖ ^ 2
      ≤ ((b - a) / (2 * π)) ^ 2 * ((b - a)⁻¹ * ∫ x in a..b, ‖f' x‖ ^ 2) := by
  classical
  have hba : (0 : ℝ) < b - a := by linarith
  have hfc : ContinuousOn f (Set.uIcc a b) := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hf'int : IntervalIntegrable f' volume a b := hf'c.intervalIntegrable
  have hL2f := memLp_two_of_continuousOn hab hfc
  have hL2f' := memLp_two_of_continuousOn hab hf'c
  set K : ℝ := ((b - a) / (2 * π)) ^ 2 with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hP := hasSum_sq_fourierCoeffOn hab hL2f
  have hP' := hasSum_sq_fourierCoeffOn hab hL2f'
  have hcomp : ∀ n : ℤ, n ≠ 0 →
      ‖fourierCoeffOn hab f n‖ ^ 2 ≤ K * ‖fourierCoeffOn hab f' n‖ ^ 2 := by
    intro n hn
    have hrel := fourierCoeffOn_of_hasDerivAt hab hn hf hf'int
    rw [hper, sub_self, mul_zero, zero_sub] at hrel
    have hden : ‖(-2 * (π : ℂ) * I * (n : ℂ))‖ = 2 * π * |(n : ℝ)| := by
      simp [abs_of_pos Real.pi_pos]
    have hnum : ‖((b : ℂ) - (a : ℂ))‖ = b - a := by
      rw [show ((b : ℂ) - (a : ℂ)) = (((b - a : ℝ)) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hba]
    have hnorm : ‖fourierCoeffOn hab f n‖
        = (b - a) / (2 * π * |(n : ℝ)|) * ‖fourierCoeffOn hab f' n‖ := by
      rw [hrel, norm_mul, norm_neg, norm_mul, hnum, norm_div, norm_one, hden]
      ring
    have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      have h1 : (1 : ℤ) ≤ |n| := Int.one_le_abs (by omega)
      have h2 : ((1 : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast h1
      rw [Int.cast_abs] at h2
      simpa using h2
    rw [hnorm, mul_pow, hK, div_pow, div_pow]
    have hstep : (b - a) ^ 2 / (2 * π * |(n : ℝ)|) ^ 2 ≤ (b - a) ^ 2 / (2 * π) ^ 2 := by
      refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
      have h5 : (1 : ℝ) ≤ |(n : ℝ)| ^ 2 := by nlinarith [hn1]
      calc (2 * π) ^ 2 = (2 * π) ^ 2 * 1 := by ring
        _ ≤ (2 * π) ^ 2 * |(n : ℝ)| ^ 2 := mul_le_mul_of_nonneg_left h5 (by positivity)
        _ = (2 * π * |(n : ℝ)|) ^ 2 := by ring
    exact mul_le_mul_of_nonneg_right hstep (by positivity)
  have hs1 := hP.update 0 0
  have hs2 := (hP'.update 0 0).mul_left K
  have hterm : ∀ n : ℤ,
      Function.update (fun i => ‖fourierCoeffOn hab f i‖ ^ 2) 0 0 n
        ≤ K * Function.update (fun i => ‖fourierCoeffOn hab f' i‖ ^ 2) 0 0 n := by
    intro n
    by_cases hn : n = 0
    · subst hn; simp
    · rw [Function.update_of_ne hn, Function.update_of_ne hn]
      exact hcomp n hn
  have hmain := hasSum_le hterm hs1 hs2
  have hzero' : (0 : ℝ) ≤ ‖fourierCoeffOn hab f' 0‖ ^ 2 := by positivity
  have hcast : ‖fourierCoeffOn hab f 0‖ ^ 2 = ‖(b - a)⁻¹ • ∫ x in a..b, f x‖ ^ 2 := by
    rw [fourierCoeffOn_zero_eq_average]
  simp only [smul_eq_mul] at hmain
  rw [← hcast]
  nlinarith [hmain, hzero', hK0]

end

end GaloisForLFunctions.HTGeometry
