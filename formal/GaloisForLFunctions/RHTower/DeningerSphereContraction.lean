import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# The two deformations contracting the unit sphere

An isometry of a real inner product space with no eigenvector lets the identity of the unit sphere
be deformed to that isometry along normalized straight lines, because the segment from `x` to `S x`
never meets the origin.  If moreover a unit vector is orthogonal to the range of the isometry, the
isometry can then be slid to that constant vector along a quarter circle, which stays on the
sphere.

These are the two pointwise facts behind the contractibility of the unit sphere of an
infinite-dimensional Hilbert space.

* `deningerSphereLine_ne_zero` : the straight-line deformation is defined.
* `deningerSphereSlide_norm` : the quarter-circle deformation stays on the sphere.
-/

namespace RHTower

open scoped InnerProductSpace

section SphereDeformation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **The straight-line deformation avoids the origin.**  If `S` has no eigenvector then the
segment from a unit vector `x` to `S x` never passes through the origin, so it can be normalized. -/
theorem deningerSphereLine_ne_zero (S : H →ₗᵢ[ℝ] H)
    (hS : ∀ (y : H) (c : ℝ), y ≠ 0 → S y ≠ c • y)
    {x : H} (hx : ‖x‖ = 1) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) • x + t • S x ≠ 0 := by
  have hxne : x ≠ 0 := by
    intro h
    rw [h, norm_zero] at hx
    exact zero_ne_one hx
  intro hzero
  rcases eq_or_lt_of_le ht0 with rfl | htpos
  · rw [sub_zero, one_smul, zero_smul, add_zero] at hzero
    exact hxne hzero
  · refine hS x (-(1 - t) / t) hxne ?_
    have ht : t ≠ 0 := ne_of_gt htpos
    have h1 : t • S x = -((1 - t) • x) := by
      rw [← neg_eq_iff_add_eq_zero.mpr hzero]
    have h2 : S x = t⁻¹ • (-((1 - t) • x)) := by
      rw [← h1, smul_smul, inv_mul_cancel₀ ht, one_smul]
    rw [h2, smul_neg, smul_smul, ← neg_smul, div_eq_inv_mul]
    congr 1
    ring

/-- **The quarter-circle deformation stays on the sphere.**  If `e` is a unit vector orthogonal to
the range of the isometry `S`, then `√(1 - t²)·S x + t·e` is a unit vector for every unit `x` and
every `t ∈ [0, 1]`. -/
theorem deningerSphereSlide_norm (S : H →ₗᵢ[ℝ] H) {e : H} (he : ‖e‖ = 1)
    (hperp : ∀ y : H, ⟪S y, e⟫_ℝ = 0)
    {x : H} (hx : ‖x‖ = 1) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖Real.sqrt (1 - t ^ (2 : ℕ)) • S x + t • e‖ = 1 := by
  have hsq : (0 : ℝ) ≤ 1 - t ^ (2 : ℕ) := by nlinarith
  have hSx : ‖S x‖ = 1 := by rw [S.norm_map, hx]
  have hinner : ⟪Real.sqrt (1 - t ^ (2 : ℕ)) • S x, t • e⟫_ℝ = 0 := by
    rw [real_inner_smul_left, real_inner_smul_right, hperp x]
    ring
  have hnormsq : ‖Real.sqrt (1 - t ^ (2 : ℕ)) • S x + t • e‖ ^ (2 : ℕ) = 1 := by
    rw [norm_add_sq_real, hinner, norm_smul, norm_smul, hSx, he, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg ht0,
      mul_one, mul_one, Real.sq_sqrt hsq]
    ring
  have hnn : 0 ≤ ‖Real.sqrt (1 - t ^ (2 : ℕ)) • S x + t • e‖ := norm_nonneg _
  nlinarith [hnormsq, hnn]

end SphereDeformation

end RHTower
