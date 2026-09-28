import GaloisForLFunctions.HilbertMetric.CentroidGauge

/-!
# Sharp Gaussian Harnack comparison

Completing the Hilbert-space square gives an exact defect for Gaussian transport
between two positive times. The same comparison controls every nonnegative
weighted row of the existing Gaussian distance matrix, including coincident
points and empty configurations. Logarithmic time parameters cover all positive
early times and all positive time increments.
-/

open scoped BigOperators RealInnerProductSpace NNReal

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Exact nonnegative remainder behind Gaussian space-time comparison. -/
theorem gaussianHarnack_square (s r : ℝ) (x y z : E) :
    ‖x - z‖ ^ 2 / (4 * Real.exp s) -
      ‖y - z‖ ^ 2 / (4 * (Real.exp s + Real.exp r)) +
      ‖x - y‖ ^ 2 / (4 * Real.exp r) =
    ‖Real.exp r • (x - z) - Real.exp s • (y - x)‖ ^ 2 /
      (4 * Real.exp s * Real.exp r * (Real.exp s + Real.exp r)) := by
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right]
  simp only [real_inner_comm y x, real_inner_comm z x, real_inner_comm z y]
  field_simp [Real.exp_ne_zero, ne_of_gt (add_pos (Real.exp_pos s) (Real.exp_pos r))]
  ring

/-- The pointwise Harnack bound has the Euclidean action constant `1/4`. -/
theorem gaussianHarnack (s r : ℝ) (x y z : E) :
    Real.exp (-‖x - z‖ ^ 2 / (4 * Real.exp s)) ≤
      Real.exp (‖x - y‖ ^ 2 / (4 * Real.exp r)) *
        Real.exp (-‖y - z‖ ^ 2 / (4 * (Real.exp s + Real.exp r))) := by
  rw [← Real.exp_add, Real.exp_le_exp]
  simp only [neg_div]
  have h := gaussianHarnack_square s r x y z
  have hn : 0 ≤ ‖Real.exp r • (x - z) - Real.exp s • (y - x)‖ ^ 2 /
      (4 * Real.exp s * Real.exp r * (Real.exp s + Real.exp r)) := by positivity
  linarith

/-- Equality determines the source centre by the straight space-time characteristic. -/
theorem gaussianHarnack_eq_iff (s r : ℝ) (x y z : E) :
    Real.exp (-‖x - z‖ ^ 2 / (4 * Real.exp s)) =
        Real.exp (‖x - y‖ ^ 2 / (4 * Real.exp r)) *
          Real.exp (-‖y - z‖ ^ 2 / (4 * (Real.exp s + Real.exp r))) ↔
      Real.exp r • (x - z) = Real.exp s • (y - x) := by
  rw [← Real.exp_add, Real.exp_injective.eq_iff]
  simp only [neg_div]
  have h := gaussianHarnack_square s r x y z
  have hd : 4 * Real.exp s * Real.exp r * (Real.exp s + Real.exp r) ≠ 0 := by
    positivity
  constructor
  · intro he
    have hz : ‖Real.exp r • (x - z) - Real.exp s • (y - x)‖ ^ 2 = 0 := by
      have heq : ‖Real.exp r • (x - z) - Real.exp s • (y - x)‖ ^ 2 /
          (4 * Real.exp s * Real.exp r * (Real.exp s + Real.exp r)) = 0 := by linarith
      exact (div_eq_zero_iff.mp heq).resolve_right hd
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))
  · intro he
    rw [he, sub_self, norm_zero, zero_pow (by omega), zero_div] at h
    linarith

variable {ι : Type*}

/-- Every Gaussian Gram entry obeys the same comparison across rows and bandwidths. -/
theorem gaussianDistanceMatrix_harnack (p : ι → E) (s r : ℝ) (i j k : ι) :
    gaussianDistanceMatrix p (1 / (4 * Real.exp s)) i k ≤
      Real.exp (‖p i - p j‖ ^ 2 / (4 * Real.exp r)) *
        gaussianDistanceMatrix p (1 / (4 * (Real.exp s + Real.exp r))) j k := by
  simpa only [gaussianDistanceMatrix, neg_div, one_div, neg_mul, div_eq_mul_inv,
    mul_comm, one_mul, mul_neg] using gaussianHarnack s r (p i) (p j) (p k)

/-- Harnack comparison for a Gaussian matrix applied to any nonnegative source. -/
theorem gaussianDistanceMatrix_weighted_harnack [Fintype ι] (p : ι → E) (w : ι → ℝ≥0)
    (s r : ℝ) (i j : ι) :
    (∑ k, (w k : ℝ) * gaussianDistanceMatrix p (1 / (4 * Real.exp s)) i k) ≤
      Real.exp (‖p i - p j‖ ^ 2 / (4 * Real.exp r)) *
        ∑ k, (w k : ℝ) *
          gaussianDistanceMatrix p (1 / (4 * (Real.exp s + Real.exp r))) j k := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  calc
    _ ≤ (w k : ℝ) * (Real.exp (‖p i - p j‖ ^ 2 / (4 * Real.exp r)) *
        gaussianDistanceMatrix p (1 / (4 * (Real.exp s + Real.exp r))) j k) :=
      mul_le_mul_of_nonneg_left (gaussianDistanceMatrix_harnack p s r i j k) (w k).coe_nonneg
    _ = _ := by ring

end

end GaloisForLFunctions.HilbertMetric
