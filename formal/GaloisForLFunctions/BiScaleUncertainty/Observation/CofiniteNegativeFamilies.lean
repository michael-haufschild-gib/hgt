import GaloisForLFunctions.BiScaleUncertainty.Observation.CoordinateNegativeFamilies
import GaloisForLFunctions.BiScaleUncertainty.Observation.CoordinateTailDensity

/-!
# Cofinite polynomial ideals retain signed dimensions

Every finite negative family can be represented by polynomial tests divisible
by an arbitrary power of a nonzero bounded coordinate.
-/

open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.Observation
open HilbertMetric

/-- Every prescribed monomial divisor preserves all finite negative dimensions of the signed form. -/
theorem exists_negative_polynomial_tail_family {μ : Measure ℝ} [IsFiniteMeasure μ]
    {φ : ℝ → ℝ} (hφ : MeasurableEmbedding φ) (hb : ∀ᵐ x ∂μ, |φ x| ≤ 1)
    (hzero : ∀ᵐ x ∂μ, φ x ≠ 0) (N : ℕ)
    (J : ℝ → ℝ) (hJ : MemLp J ∞ μ) (n : ℕ) (v : Fin n → Lp ℝ 2 μ)
    (hv : ∀ c : Fin n → ℝ, c ≠ 0 →
      finiteFamilyQuadratic (_root_.RHTower.linftyMultiplierOperator J hJ) v c < 0) :
    ∃ P : Fin n → Polynomial ℝ, (∀ i, Polynomial.X ^ N ∣ P i) ∧
      ∀ c : Fin n → ℝ, c ≠ 0 →
        (∫ x, (∑ i, c i * (P i).eval (φ x)) ^ 2 * J x ∂μ) < 0 := by
  apply exists_negative_polynomial_family_in_dense_submodule φ (coordinateTailSpan hφ hb N)
    (coordinateTailSpan_dense hφ hb hzero N) (fun P => Polynomial.X ^ N ∣ P) ?_ J hJ n v hv
  intro w hw
  obtain ⟨Q, hQ⟩ := exists_polynomial_coordinate_tail_of_mem hφ hb N hw
  refine ⟨Polynomial.X ^ N * Q, ⟨Q, rfl⟩, ?_⟩
  simpa only [Polynomial.eval_mul, Polynomial.eval_X_pow] using hQ

/-- Disjoint negative windows give arbitrarily high-degree polynomial test families of the same dimension. -/
theorem exists_negative_polynomial_tails_of_disjoint_tests {μ : Measure ℝ} [IsFiniteMeasure μ]
    {φ : ℝ → ℝ} (hφ : MeasurableEmbedding φ) (hb : ∀ᵐ x ∂μ, |φ x| ≤ 1)
    (hzero : ∀ᵐ x ∂μ, φ x ≠ 0) (N : ℕ)
    (J : ℝ → ℝ) (hJ : MemLp J ∞ μ) (n : ℕ) (v : Fin n → Lp ℝ 2 μ)
    (hdisj : ∀ i j, i ≠ j → ∀ᵐ x ∂μ, v i x * v j x = 0)
    (hneg : ∀ i, _root_.RHTower.linftyMultiplierQuadratic J hJ (v i) < 0) :
    ∃ P : Fin n → Polynomial ℝ, (∀ i, Polynomial.X ^ N ∣ P i) ∧
      ∀ c : Fin n → ℝ, c ≠ 0 →
        (∫ x, (∑ i, c i * (P i).eval (φ x)) ^ 2 * J x ∂μ) < 0 :=
  exists_negative_polynomial_tail_family hφ hb hzero N J hJ n v
    (finiteFamilyQuadratic_neg_of_disjoint_tests J hJ n v hdisj hneg)

#print axioms exists_negative_polynomial_tails_of_disjoint_tests
end GaloisForLFunctions.BiScaleUncertainty.Observation
