import GaloisForLFunctions.RHTower.WeilLogShiftEdgeExponential
import GaloisForLFunctions.RHTower.WeilLogShiftProjectedSecondMoment
import GaloisForLFunctions.HTGeometry.LocalExponentialTestClosure

/-! Uniform exponential and factorial absolute-moment bounds for the actual projected index law. -/

open MeasureTheory ProbabilityTheory

namespace RHTower

theorem finiteWeilCanonicalProjectedIndex_exponential_bound (r t : ℕ) (a : ℝ) :
    (∫ x : ℝ, Real.exp (a * x)
      ∂(finiteWeilCanonicalProjectedProbabilityLaw r (2 * (r + 1) ^ 2 + t) 1 0 : Measure ℝ)) ≤
      4 * Real.exp (|a| + a ^ 2 / 8) := by
  rw [finiteWeilCanonicalProjectedProbabilityLaw, finiteWeilCanonicalObservableLaw_integral_real]
  simpa only [one_mul, zero_mul, add_zero] using
    finiteWeilCanonicalEdge_centered_exponential_bound r t a

theorem finiteWeilCanonicalProjectedIndex_exponential_abs_bound (r t : ℕ) :
    (∫ x : ℝ, Real.exp |x|
      ∂(finiteWeilCanonicalProjectedProbabilityLaw r (2 * (r + 1) ^ 2 + t) 1 0 : Measure ℝ)) ≤
      8 * Real.exp (9 / 8 : ℝ) := by
  let μ := (finiteWeilCanonicalProjectedProbabilityLaw r (2 * (r + 1) ^ 2 + t) 1 0 : Measure ℝ)
  have hi (f : ℝ → ℝ) : Integrable f μ :=
    finiteWeilCanonicalProjectedProbabilityLaw_integrable _ _ _ _ f
  have hpoint (x : ℝ) : Real.exp |x| ≤ Real.exp x + Real.exp (-x) := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
      linarith only [Real.exp_pos (-x)]
    · rw [abs_of_nonpos hx]
      linarith only [Real.exp_pos x]
  have hp := finiteWeilCanonicalProjectedIndex_exponential_bound r t 1
  have hn := finiteWeilCanonicalProjectedIndex_exponential_bound r t (-1)
  norm_num at hp hn
  calc
    _ ≤ ∫ x : ℝ, (Real.exp x + Real.exp (-x)) ∂μ :=
      integral_mono (hi _) (hi _) hpoint
    _ = (∫ x : ℝ, Real.exp x ∂μ) + ∫ x : ℝ, Real.exp (-x) ∂μ := integral_add (hi _) (hi _)
    _ ≤ _ := by dsimp [μ]; linarith

theorem finiteWeilCanonicalProjectedIndex_abs_moment_bound (r t p : ℕ) :
    (∫ x : ℝ, |x| ^ p
      ∂(finiteWeilCanonicalProjectedProbabilityLaw r (2 * (r + 1) ^ 2 + t) 1 0 : Measure ℝ)) ≤
      (p.factorial : ℝ) * (8 * Real.exp (9 / 8 : ℝ)) := by
  let μ := (finiteWeilCanonicalProjectedProbabilityLaw r (2 * (r + 1) ^ 2 + t) 1 0 : Measure ℝ)
  have hi (f : ℝ → ℝ) : Integrable f μ :=
    finiteWeilCanonicalProjectedProbabilityLaw_integrable _ _ _ _ f
  have hpoint (x : ℝ) : |x| ^ p ≤ (p.factorial : ℝ) * Real.exp |x| := by
    simpa only [one_pow, div_one, one_mul] using
      HTGeometry.abs_pow_le_const_mul_exp (a := 1) zero_lt_one p x
  calc
    _ ≤ ∫ x : ℝ, (p.factorial : ℝ) * Real.exp |x| ∂μ :=
      integral_mono (hi _) (hi _) hpoint
    _ = (p.factorial : ℝ) * ∫ x : ℝ, Real.exp |x| ∂μ := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (finiteWeilCanonicalProjectedIndex_exponential_abs_bound r t) (Nat.cast_nonneg _)

end RHTower
