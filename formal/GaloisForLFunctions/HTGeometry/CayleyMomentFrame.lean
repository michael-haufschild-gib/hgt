import GaloisForLFunctions.HTGeometry.CofinalCholeskyFiniteFrame
import Mathlib.MeasureTheory.Measure.ResolventTransform

/-!
# Cayley moments as finite reciprocal-moment frames

This module lifts the finite triangular Cayley algebra to arbitrary finite Borel measures on the
real line. The reciprocal kernels are uniformly bounded at the regular node `-i`, so their
integrals exist without moment hypotheses. Integration of the pointwise Cayley expansion then
identifies every finite prefix of circle moments exactly with the corresponding finite prefix of
regular reciprocal moments.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex MeasureTheory

noncomputable section

/-- The Cayley map from the real line to the unit circle. -/
def realCayley (x : ℝ) : ℂ := ((x : ℂ) - I) / ((x : ℂ) + I)

/-- The `r`-th reciprocal moment at the regular Cauchy node `-i`. -/
def reciprocalMoment (μ : Measure ℝ) (r : ℕ) : ℂ :=
  ∫ x, (((x : ℂ) + I)⁻¹) ^ r ∂μ

/-- The `n`-th positive circle moment after the Cayley transform. -/
def cayleyMoment (μ : Measure ℝ) (n : ℕ) : ℂ :=
  ∫ x, realCayley x ^ n ∂μ

/-- The real line stays at distance at least one from the pole `-i`. -/
theorem one_le_norm_real_add_I (x : ℝ) :
    1 ≤ ‖(x : ℂ) + I‖ := by
  have h := Complex.abs_im_le_norm ((x : ℂ) + I)
  norm_num at h ⊢
  exact h

/-- Consequently the regular reciprocal kernel at `-i` is bounded by one. -/
theorem norm_inv_real_add_I_le_one (x : ℝ) :
    ‖((x : ℂ) + I)⁻¹‖ ≤ 1 := by
  rw [norm_inv]
  apply (inv_le_one₀ (by linarith [one_le_norm_real_add_I x])).2
  exact one_le_norm_real_add_I x

/-- Every reciprocal power at `-i` is integrable against a finite measure. -/
theorem integrable_reciprocalPower (μ : Measure ℝ) [IsFiniteMeasure μ] (r : ℕ) :
    Integrable (fun x : ℝ => (((x : ℂ) + I)⁻¹) ^ r) μ := by
  have hne : ∀ x : ℝ, (x : ℂ) + I ≠ 0 := by
    intro x h
    have := congrArg Complex.im h
    norm_num at this
  have hcont : Continuous (fun x : ℝ => (((x : ℂ) + I)⁻¹) ^ r) :=
    ((Complex.continuous_ofReal.add continuous_const).inv₀ hne).pow r
  apply Integrable.of_bound hcont.aestronglyMeasurable 1
  filter_upwards with x
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (norm_inv_real_add_I_le_one x)

/-- Pointwise Cayley powers are the finite triangular transform of reciprocal powers at `-i`. -/
theorem realCayley_pow_expansion (x : ℝ) (n : ℕ) :
    realCayley x ^ n =
      cayleyTriangularTransform (fun r => (((x : ℂ) + I)⁻¹) ^ r) n := by
  apply cayley_pow_expansion
  intro h
  have := congrArg Complex.im h
  norm_num at this

/-- Integration commutes with the finite triangular Cayley transform. -/
theorem cayleyMoment_eq_triangularTransform
    (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ) :
    cayleyMoment μ n = cayleyTriangularTransform (reciprocalMoment μ) n := by
  rw [cayleyMoment]
  simp_rw [realCayley_pow_expansion]
  simp only [cayleyTriangularTransform]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro r hr
    rw [integral_mul_const, integral_const_mul]
    rfl
  · intro r hr
    exact (integrable_reciprocalPower μ r).const_mul _ |>.mul_const _

/-- Equality of finite Cayley-moment prefixes is equivalent to equality of finite reciprocal-
moment prefixes at `-i`. This is the measure-level finite frame/regular Cauchy coordinate bridge. -/
theorem cayleyMoment_prefix_iff_reciprocalMoment_prefix
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (N : ℕ) :
    (∀ n ≤ N, cayleyMoment μ n = cayleyMoment ν n) ↔
      ∀ r ≤ N, reciprocalMoment μ r = reciprocalMoment ν r := by
  simp_rw [cayleyMoment_eq_triangularTransform]
  exact cayleyTriangularTransform_prefix_iff

end

end GaloisForLFunctions.HTGeometry
