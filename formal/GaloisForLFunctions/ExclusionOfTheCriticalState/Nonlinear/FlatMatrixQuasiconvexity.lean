import GaloisForLFunctions.ExclusionOfTheCriticalState.Nonlinear.FlatQuasiconvexVariation
import GaloisForLFunctions.HilbertMetric.Geometry.CompactJacobianNullLagrangian

/-!
# A nonconvex flat loss with an exact quasiconvexity gap

Adding any multiple of the determinant to the sum of four flat entry
losses leaves compact-gradient excess action unchanged. Its entire gap
is the sum of four scalar flat gaps. For determinant coefficient two,
the integrand fails ordinary convexity, giving a genuine nonconvex
compact-variation inequality on every finite-dimensional Haar space.
-/

open MeasureTheory Set
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex
open HilbertMetric.Geometry.CompactJacobian
noncomputable section

/-- Flat entry losses with a determinant null Lagrangian. -/
def matrixFlatLoss (τ : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  potential (A 0 0) + potential (A 0 1) + potential (A 1 0) + potential (A 1 1) + τ * A.det

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def compactC2Variation (u : CompactC2 E) : CompactVariation E :=
  ⟨u.val, u.property.1.of_le (by norm_num), u.property.2⟩

variable (μ : Measure E) [μ.IsAddHaarMeasure]

/-- The full matrix excess retains its exact scalar gap independently of the determinant weight. -/
theorem matrixFlatLoss_excess (τ : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ)
    (u v : CompactC2 E) (s t : E) :
    (∫ x, matrixFlatLoss τ (A + jacobian u v s t x) - matrixFlatLoss τ A ∂μ) =
      flatVariationAction μ (A 0 0) (compactC2Variation u) s +
      flatVariationAction μ (A 0 1) (compactC2Variation u) t +
      flatVariationAction μ (A 1 0) (compactC2Variation v) s +
      flatVariationAction μ (A 1 1) (compactC2Variation v) t := by
  have h00 := flatVariationAction_integrable μ (A 0 0) (compactC2Variation u) s
  have h01 := flatVariationAction_integrable μ (A 0 1) (compactC2Variation u) t
  have h10 := flatVariationAction_integrable μ (A 1 0) (compactC2Variation v) s
  have h11 := flatVariationAction_integrable μ (A 1 1) (compactC2Variation v) t
  have hd := (determinant_excess_integrable μ A u v s t).const_mul τ
  have h2 : Integrable (fun x =>
      (potential (A 0 0 + variationSlope (compactC2Variation u) s x) - potential (A 0 0)) +
      (potential (A 0 1 + variationSlope (compactC2Variation u) t x) - potential (A 0 1))) μ := h00.add h01
  have h3 : Integrable (fun x =>
      (potential (A 0 0 + variationSlope (compactC2Variation u) s x) - potential (A 0 0)) +
      (potential (A 0 1 + variationSlope (compactC2Variation u) t x) - potential (A 0 1)) +
      (potential (A 1 0 + variationSlope (compactC2Variation v) s x) - potential (A 1 0))) μ := h2.add h10
  have h4 : Integrable (fun x =>
      (potential (A 0 0 + variationSlope (compactC2Variation u) s x) - potential (A 0 0)) +
      (potential (A 0 1 + variationSlope (compactC2Variation u) t x) - potential (A 0 1)) +
      (potential (A 1 0 + variationSlope (compactC2Variation v) s x) - potential (A 1 0)) +
      (potential (A 1 1 + variationSlope (compactC2Variation v) t x) - potential (A 1 1))) μ := h3.add h11
  have he (x : E) : matrixFlatLoss τ (A + jacobian u v s t x) - matrixFlatLoss τ A =
      (potential (A 0 0 + variationSlope (compactC2Variation u) s x) - potential (A 0 0)) +
      (potential (A 0 1 + variationSlope (compactC2Variation u) t x) - potential (A 0 1)) +
      (potential (A 1 0 + variationSlope (compactC2Variation v) s x) - potential (A 1 0)) +
      (potential (A 1 1 + variationSlope (compactC2Variation v) t x) - potential (A 1 1)) +
      τ * ((A + jacobian u v s t x).det - A.det) := by
    simp only [matrixFlatLoss, Matrix.add_apply]
    change potential (A 0 0 + variationSlope (compactC2Variation u) s x) +
        potential (A 0 1 + variationSlope (compactC2Variation u) t x) +
        potential (A 1 0 + variationSlope (compactC2Variation v) s x) +
        potential (A 1 1 + variationSlope (compactC2Variation v) t x) +
        τ * (A + jacobian u v s t x).det -
        (potential (A 0 0) + potential (A 0 1) + potential (A 1 0) + potential (A 1 1) + τ * A.det) = _
    ring
  simp_rw [he]
  rw [integral_add h4 hd,
    integral_add h3 h11, integral_add h2 h10,
    integral_add h00 h01, integral_const_mul, integral_determinant_excess, mul_zero, add_zero]
  rfl

/-- Every compact C² gradient perturbation has nonnegative excess, for every determinant weight. -/
theorem matrixFlatLoss_quasiconvex (τ : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ)
    (u v : CompactC2 E) (s t : E) :
    0 ≤ ∫ x, matrixFlatLoss τ (A + jacobian u v s t x) - matrixFlatLoss τ A ∂μ := by
  rw [matrixFlatLoss_excess]
  exact add_nonneg (add_nonneg (add_nonneg (flatVariationAction_nonneg μ _ _ _)
    (flatVariationAction_nonneg μ _ _ _)) (flatVariationAction_nonneg μ _ _ _))
    (flatVariationAction_nonneg μ _ _ _)

/-- Zero matrix excess is exactly simultaneous vanishing of the four scalar flat gaps. -/
theorem matrixFlatLoss_excess_zero_iff (τ : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ)
    (u v : CompactC2 E) (s t : E) :
    (∫ x, matrixFlatLoss τ (A + jacobian u v s t x) - matrixFlatLoss τ A ∂μ) = 0 ↔
      flatVariationAction μ (A 0 0) (compactC2Variation u) s = 0 ∧
      flatVariationAction μ (A 0 1) (compactC2Variation u) t = 0 ∧
      flatVariationAction μ (A 1 0) (compactC2Variation v) s = 0 ∧
      flatVariationAction μ (A 1 1) (compactC2Variation v) t = 0 := by
  rw [matrixFlatLoss_excess]
  have h00 := flatVariationAction_nonneg μ (A 0 0) (compactC2Variation u) s
  have h01 := flatVariationAction_nonneg μ (A 0 1) (compactC2Variation u) t
  have h10 := flatVariationAction_nonneg μ (A 1 0) (compactC2Variation v) s
  have h11 := flatVariationAction_nonneg μ (A 1 1) (compactC2Variation v) t
  constructor
  · intro h
    exact ⟨by linarith only [h, h00, h01, h10, h11],
      by linarith only [h, h00, h01, h10, h11],
      by linarith only [h, h00, h01, h10, h11],
      by linarith only [h, h00, h01, h10, h11]⟩
  · rintro ⟨h0, h1, h2, h3⟩
    rw [h0, h1, h2, h3, add_zero, add_zero, add_zero]

/-- The compact-gradient inequality does not come from convexity of the matrix integrand. -/
theorem matrixFlatLoss_not_convex : ¬ ConvexOn ℝ univ (matrixFlatLoss 2) := by
  intro h
  let A : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]
  have hmid : (1 / 2 : ℝ) • A + (1 / 2 : ℝ) • (-A) = 0 := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul,
      Matrix.zero_apply]
    ring
  have hneg : potential (-1) = 0 := (potential_zero_iff _).mpr (by norm_num)
  have hA : matrixFlatLoss 2 A = potential 1 - 2 := by
    norm_num [matrixFlatLoss, A, Matrix.det_fin_two, hneg]
    ring
  have hnA : matrixFlatLoss 2 (-A) = potential 1 - 2 := by
    norm_num [matrixFlatLoss, A, Matrix.det_fin_two, Matrix.neg_apply, hneg]
    ring
  have hz : matrixFlatLoss 2 0 = 0 := by
    norm_num [matrixFlatLoss, Matrix.det_fin_two]
  have hc := h.2 (mem_univ A) (mem_univ (-A))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  rw [hmid, hA, hnA, hz] at hc
  have hb := (potential_bounds 1).2
  norm_num only [smul_eq_mul, one_pow] at hc hb
  linarith only [hc, hb]

#print axioms matrixFlatLoss_excess
#print axioms matrixFlatLoss_quasiconvex
#print axioms matrixFlatLoss_excess_zero_iff
#print axioms matrixFlatLoss_not_convex
end
end GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex
