import Mathlib

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Positive signal amplitude, with admissibility carried as data. -/
abbrev PositiveSignal := {q : ℝ // 0 < q}

/-- Universal local quadratic model for a matched-filter profile. -/
def greedyBumpProfile {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (Q : PositiveSignal) (g δ : E) : ℝ :=
  @inner ℝ E _ g δ - (Q : ℝ) / 2 * ‖δ‖ ^ 2

/-- Newton displacement in the matched isotropic geometry. -/
def greedyBumpDisplacement {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (Q : PositiveSignal) (g : E) : E :=
  ((Q : ℝ)⁻¹) • g

/-- Exact quadratic completion underlying Proposition 5.1. -/
theorem greedyBumpProfile_completion {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (Q : PositiveSignal) (g δ : E) :
    greedyBumpProfile Q g δ =
      ‖g‖ ^ 2 / (2 * (Q : ℝ)) -
        (Q : ℝ) / 2 * ‖δ - greedyBumpDisplacement Q g‖ ^ 2 := by
  rw [norm_sub_sq_real]
  simp only [greedyBumpProfile, greedyBumpDisplacement, real_inner_smul_right,
    norm_smul, Real.norm_eq_abs]
  rw [abs_of_pos (inv_pos.mpr Q.property)]
  rw [real_inner_comm δ g]
  field_simp [ne_of_gt Q.property]
  ring

/-- The Newton displacement attains the exact local-profile gain. -/
theorem greedyBumpProfile_at_displacement {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (Q : PositiveSignal) (g : E) :
    greedyBumpProfile Q g (greedyBumpDisplacement Q g) =
      ‖g‖ ^ 2 / (2 * (Q : ℝ)) := by
  rw [greedyBumpProfile_completion]
  simp

/-- Every displacement is bounded by the Newton-profile gain. -/
theorem greedyBumpProfile_le_gain {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (Q : PositiveSignal) (g δ : E) :
    greedyBumpProfile Q g δ ≤ ‖g‖ ^ 2 / (2 * (Q : ℝ)) := by
  rw [greedyBumpProfile_completion]
  exact sub_le_self _ (mul_nonneg
    (div_nonneg (le_of_lt Q.property) (by norm_num)) (sq_nonneg _))

/-- Positive-definite template metric, with nondegeneracy carried as data. -/
structure PositiveTemplateMetric (D : ℕ) where
  matrix : Matrix (Fin D) (Fin D) ℝ
  posDef : matrix.PosDef

/-- Matched high-signal Hessian `H_Q = Q G`. -/
def greedyBumpHessian {D : ℕ} (Q : PositiveSignal)
    (G : PositiveTemplateMetric D) : Matrix (Fin D) (Fin D) ℝ :=
  (Q : ℝ) • G.matrix

/-- Determinant volume scales by exactly `Q^D`. -/
theorem greedyBumpHessian_det {D : ℕ} (Q : PositiveSignal)
    (G : PositiveTemplateMetric D) :
    (greedyBumpHessian Q G).det =
      (Q : ℝ) ^ D * G.matrix.det := by
  simp [greedyBumpHessian]

/-- Matched trace penalty collapses to dimension divided by signal. -/
theorem greedyBumpHessian_trace_inv_mul {D : ℕ} (Q : PositiveSignal)
    (G : PositiveTemplateMetric D) :
    Matrix.trace ((greedyBumpHessian Q G)⁻¹ * G.matrix) =
      (D : ℝ) / (Q : ℝ) := by
  letI : Invertible (Q : ℝ) := invertibleOfNonzero (ne_of_gt Q.property)
  have hdet : IsUnit G.matrix.det :=
    (Matrix.isUnit_iff_isUnit_det G.matrix).mp G.posDef.isUnit
  rw [greedyBumpHessian, Matrix.inv_smul _ _ hdet, Matrix.smul_mul,
    Matrix.nonsing_inv_mul _ hdet, Matrix.trace_smul, Matrix.trace_one]
  simp [invOf_eq_inv, div_eq_mul_inv]
  ring

/-- Proposition 5.1's local bias term is exactly `D/(2Q)`. -/
theorem greedyBump_matched_bias {D : ℕ} (Q : PositiveSignal)
    (G : PositiveTemplateMetric D) :
    (1 / 2 : ℝ) * Matrix.trace
      ((greedyBumpHessian Q G)⁻¹ * G.matrix) =
        (D : ℝ) / (2 * (Q : ℝ)) := by
  rw [greedyBumpHessian_trace_inv_mul]
  field_simp

/-- Every coordinate of a standard Gaussian has unit second moment. -/
theorem greedyBump_integral_coordinate_sq_stdGaussian {D : ℕ} (i : Fin D) :
    ∫ x : EuclideanSpace ℝ (Fin D), (x i) ^ 2
      ∂ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin D)) = 1 := by
  rw [← variance_of_integral_eq_zero (by fun_prop)]
  · rw [← ProbabilityTheory.multivariateGaussian_zero_one]
    simpa using ProbabilityTheory.variance_eval_multivariateGaussian
      (μ := (0 : EuclideanSpace ℝ (Fin D)))
      (S := (1 : Matrix (Fin D) (Fin D) ℝ)) Matrix.PosSemidef.one i
  · simpa using ProbabilityTheory.integral_strongDual_stdGaussian
      (E := EuclideanSpace ℝ (Fin D)) (EuclideanSpace.proj i)

/-- Corollary 5.1's `chi-square_D` variable has exact mean `D`. -/
theorem greedyBump_integral_norm_sq_stdGaussian (D : ℕ) :
    ∫ x : EuclideanSpace ℝ (Fin D), ‖x‖ ^ 2
      ∂ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin D)) = D := by
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum]
  · simp [greedyBump_integral_coordinate_sq_stdGaussian]
  · intro i hi
    exact ((IsGaussian.memLp_two_id
      (μ := ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin D)))).continuousLinearMap_comp
        (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin D) →L[ℝ] ℝ)).integrable_sq

/-- `chi-square_D` realized as squared norm of the standard Gaussian score. -/
def greedyBumpChiSquare (D : ℕ) : ProbabilityMeasure ℝ where
  val := (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin D))).map
    (fun x => ‖x‖ ^ 2)
  property := Measure.isProbabilityMeasure_map (by fun_prop)

/-- The bundled `chi-square_D` law has exact mean `D`. -/
theorem greedyBumpChiSquare_mean (D : ℕ) :
    ∫ u : ℝ, u ∂(greedyBumpChiSquare D : Measure ℝ) = D := by
  change ∫ u : ℝ, u ∂((ProbabilityTheory.stdGaussian
    (EuclideanSpace ℝ (Fin D))).map (fun x => ‖x‖ ^ 2)) = D
  rw [integral_map (by fun_prop) (by fun_prop)]
  exact greedyBump_integral_norm_sq_stdGaussian D

/-- Newton displacement has the paper's normalized `chi-square_D` law. -/
theorem greedyBumpDisplacement_chiSquare_law (D : ℕ) (Q : PositiveSignal) :
    (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin D))).map
      (fun g => (Q : ℝ) ^ 2 * ‖greedyBumpDisplacement Q g‖ ^ 2) =
        (greedyBumpChiSquare D : Measure ℝ) := by
  have hfun :
      (fun g : EuclideanSpace ℝ (Fin D) =>
        (Q : ℝ) ^ 2 * ‖greedyBumpDisplacement Q g‖ ^ 2) =
      fun g => ‖g‖ ^ 2 := by
    funext g
    simp only [greedyBumpDisplacement, norm_smul, Real.norm_eq_abs]
    rw [abs_of_pos (inv_pos.mpr Q.property)]
    field_simp [ne_of_gt Q.property]
  rw [hfun]
  change _ = (ProbabilityTheory.stdGaussian
    (EuclideanSpace ℝ (Fin D))).map (fun g => ‖g‖ ^ 2)
  rfl

/-- Expected optimized local-profile gain is exactly `D/(2Q)`. -/
theorem greedyBump_expected_profile_gain (D : ℕ) (Q : PositiveSignal) :
    ∫ g : EuclideanSpace ℝ (Fin D),
        greedyBumpProfile Q g (greedyBumpDisplacement Q g)
      ∂ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin D)) =
        (D : ℝ) / (2 * (Q : ℝ)) := by
  simp_rw [greedyBumpProfile_at_displacement]
  rw [integral_div, greedyBump_integral_norm_sq_stdGaussian]

/-- Exact, independence-free local/remote maximum decomposition. -/
theorem greedyBump_max_decomposition (baseline localValue remote : ℝ) :
    max localValue remote - baseline =
      (localValue - baseline) + max (remote - localValue) 0 := by
  rcases le_total remote localValue with h | h
  · simp [max_eq_left h, sub_nonpos.mpr h]
  · simp [max_eq_right h, sub_nonneg.mpr h]

/-- Remote competition correction is always nonnegative. -/
theorem greedyBump_remote_correction_nonneg (localValue remote : ℝ) :
    0 ≤ max (remote - localValue) 0 := le_max_right _ _

end

end GaloisForLFunctions.HTGeometry

