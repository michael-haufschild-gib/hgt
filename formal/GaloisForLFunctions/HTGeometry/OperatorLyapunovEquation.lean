import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.ConjSqrt
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Normed.Ring.Units

/-!
# The Lyapunov operator of a strictly positive element

For `x` in a unital C⋆-algebra, the **Lyapunov operator** is the bounded real-linear map
`Λ_x : y ↦ x y + y x`.  When `x` is strictly positive, `Λ_x` is a linear homeomorphism: writing
`x = c + z` with `c` the midpoint of a Loewner interval `[α, β]` containing `x`, the operator
`Λ_x = 2c·id + Λ_z` is a Neumann perturbation of a nonzero scalar, because
`‖Λ_z‖ ≤ 2‖z‖ ≤ β - α < α + β = 2c`.

Invertibility of `Λ_x` is what makes the squaring map `y ↦ y²` a local diffeomorphism at a
strictly positive point, hence what makes `CFC.sqrt` Fréchet differentiable; the explicit bound
`‖Λ_x⁻¹‖ ≤ (2α)⁻¹` comes from the same Neumann series.
-/

open scoped NNReal Ring

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The **Lyapunov operator** `Λ_x : y ↦ x y + y x`, as a bounded real-linear map. -/
noncomputable def lyapunov (x : A) : A →L[ℝ] A :=
  ContinuousLinearMap.mul ℝ A x + (ContinuousLinearMap.mul ℝ A).flip x

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma lyapunov_apply (x y : A) : lyapunov x y = x * y + y * x := rfl

omit [PartialOrder A] [StarOrderedRing A] in
lemma lyapunov_add (x z : A) : lyapunov (x + z) = lyapunov x + lyapunov z := by
  ext y
  simp only [lyapunov_apply, add_apply, add_mul, mul_add]
  abel

omit [PartialOrder A] [StarOrderedRing A] in
lemma lyapunov_smul_one (c : ℝ) :
    lyapunov (c • (1 : A)) = (2 * c) • (1 : A →L[ℝ] A) := by
  ext y
  simp only [lyapunov_apply, smul_apply, one_apply_eq_self,
    smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  module

omit [PartialOrder A] [StarOrderedRing A] in
lemma norm_lyapunov_le (x : A) : ‖lyapunov x‖ ≤ 2 * ‖x‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
  calc ‖lyapunov x y‖ = ‖x * y + y * x‖ := rfl
    _ ≤ ‖x * y‖ + ‖y * x‖ := norm_add_le _ _
    _ ≤ ‖x‖ * ‖y‖ + ‖y‖ * ‖x‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖x‖ * ‖y‖ := by ring

/-- An element of a Loewner interval is within half its length of the midpoint. -/
lemma norm_sub_midpoint_le {x : A} {α β : ℝ} (hαβ : α ≤ β) (hx : IsSelfAdjoint x)
    (h1 : α • (1 : A) ≤ x) (h2 : x ≤ β • (1 : A)) :
    ‖x - ((α + β) / 2) • (1 : A)‖ ≤ (β - α) / 2 := by
  have hrnn : (0 : ℝ) ≤ (β - α) / 2 := by linarith
  have hspecl : ∀ t ∈ spectrum ℝ x, α ≤ t := by
    rw [← algebraMap_le_iff_le_spectrum (a := x) hx, Algebra.algebraMap_eq_smul_one]
    exact h1
  have hspecr : ∀ t ∈ spectrum ℝ x, t ≤ β := by
    rw [← le_algebraMap_iff_spectrum_le (a := x) hx, Algebra.algebraMap_eq_smul_one]
    exact h2
  have hzeq : cfc (fun t : ℝ => t - (α + β) / 2) x = x - ((α + β) / 2) • (1 : A) := by
    rw [cfc_sub _ _ x, cfc_id' ℝ x, cfc_const _ x, Algebra.algebraMap_eq_smul_one]
  have hzsa : IsSelfAdjoint (x - ((α + β) / 2) • (1 : A)) :=
    hx.sub (IsSelfAdjoint.smul (star_trivial _) (IsSelfAdjoint.one A))
  have hzznn : (0 : A) ≤ (x - ((α + β) / 2) • (1 : A)) * (x - ((α + β) / 2) • (1 : A)) := by
    nth_rewrite 1 [← hzsa.star_eq]
    exact star_mul_self_nonneg _
  have hzz : (x - ((α + β) / 2) • (1 : A)) * (x - ((α + β) / 2) • (1 : A))
      ≤ algebraMap ℝ A (((β - α) / 2) * ((β - α) / 2)) := by
    rw [← hzeq, ← cfc_mul _ _ x]
    refine cfc_le_algebraMap _ _ x fun t ht => ?_
    have hl := hspecl t ht
    have hr := hspecr t ht
    nlinarith
  have h1n : ‖(x - ((α + β) / 2) • (1 : A)) * (x - ((α + β) / 2) • (1 : A))‖
      ≤ ((β - α) / 2) * ((β - α) / 2) :=
    (CStarAlgebra.norm_le_iff_le_algebraMap _ (by positivity) hzznn).mpr hzz
  have h2n : ‖x - ((α + β) / 2) • (1 : A)‖ * ‖x - ((α + β) / 2) • (1 : A)‖
      = ‖(x - ((α + β) / 2) • (1 : A)) * (x - ((α + β) / 2) • (1 : A))‖ := by
    rw [← CStarRing.norm_star_mul_self, hzsa.star_eq]
  nlinarith [norm_nonneg (x - ((α + β) / 2) • (1 : A)), h1n, h2n, hrnn]

/-- **The Lyapunov operator of a strictly positive element is invertible.** -/
theorem isUnit_lyapunov {x : A} {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hx : IsSelfAdjoint x)
    (h1 : α • (1 : A) ≤ x) (h2 : x ≤ β • (1 : A)) : IsUnit (lyapunov x) := by
  have hc : (0 : ℝ) < (α + β) / 2 := by linarith
  have hznorm : ‖x - ((α + β) / 2) • (1 : A)‖ ≤ (β - α) / 2 :=
    norm_sub_midpoint_le hαβ hx h1 h2
  set z := x - ((α + β) / 2) • (1 : A) with hzdef
  set K : A →L[ℝ] A := (2 * ((α + β) / 2))⁻¹ • lyapunov z with hK
  have hKnorm : ‖K‖ < 1 := by
    have hb : ‖K‖ ≤ (2 * ((α + β) / 2))⁻¹ * (2 * ‖z‖) := by
      rw [hK, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (norm_lyapunov_le z) (by positivity)
    have hb2 : (2 * ((α + β) / 2))⁻¹ * (2 * ‖z‖) ≤ (2 * ((α + β) / 2))⁻¹ * (2 * ((β - α) / 2)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hfin : (2 * ((α + β) / 2))⁻¹ * (2 * ((β - α) / 2)) < 1 := by
      rw [inv_mul_eq_div, div_lt_one (by linarith)]
      linarith
    linarith
  have hunit : IsUnit ((1 : A →L[ℝ] A) + K) := by
    have hu := isUnit_one_sub_of_norm_lt_one (x := -K) (by simpa using hKnorm)
    simpa using hu
  have hne : (2 * ((α + β) / 2)) ≠ 0 := by positivity
  have hscalar : IsUnit ((2 * ((α + β) / 2)) • (1 : A →L[ℝ] A)) := by
    rw [← Algebra.algebraMap_eq_smul_one]
    exact (isUnit_iff_ne_zero.mpr hne).map (algebraMap ℝ (A →L[ℝ] A))
  have hfac : lyapunov x = ((2 * ((α + β) / 2)) • (1 : A →L[ℝ] A)) * ((1 : A →L[ℝ] A) + K) := by
    have hxz : x = ((α + β) / 2) • (1 : A) + z := by rw [hzdef]; abel
    rw [hxz, lyapunov_add, lyapunov_smul_one, ← Algebra.algebraMap_eq_smul_one,
      ← Algebra.smul_def, smul_add, ← Algebra.algebraMap_eq_smul_one]
    congr 1
    rw [hK, smul_smul, mul_inv_cancel₀ hne, one_smul]
  rw [hfac]
  exact hscalar.mul hunit

/-- **The Lyapunov operator of any strictly positive element is invertible.** -/
theorem isUnit_lyapunov_of_isStrictlyPositive {x : A} (hx : IsStrictlyPositive x) :
    IsUnit (lyapunov x) := by
  rcases subsingleton_or_nontrivial A with hsub | hnt
  · have : Subsingleton (A →L[ℝ] A) := ⟨fun f g => by ext y; exact Subsingleton.elim _ _⟩
    exact isUnit_of_subsingleton _
  · have hxne : x⁻¹ʳ ≠ 0 := by
      intro h
      have h1 : (1 : A) = 0 := by
        rw [← Ring.mul_inverse_cancel x hx.isUnit, h, mul_zero]
      exact one_ne_zero h1
    have hinvpos : 0 < ‖x⁻¹ʳ‖ := norm_pos_iff.mpr hxne
    have hxpos : 0 < ‖x‖ := by
      have h1 : (1 : ℝ) ≤ ‖x‖ * ‖x⁻¹ʳ‖ := by
        have := norm_mul_le x x⁻¹ʳ
        rw [Ring.mul_inverse_cancel x hx.isUnit, norm_one] at this
        exact this
      nlinarith [norm_nonneg x, hinvpos]
    have hupper : x ≤ ‖x‖ • (1 : A) := by
      have h := hx.isSelfAdjoint.le_algebraMap_norm_self
      rwa [Algebra.algebraMap_eq_smul_one] at h
    have hlower : ‖x⁻¹ʳ‖⁻¹ • (1 : A) ≤ x := by
      have hiu : x⁻¹ʳ ≤ ‖x⁻¹ʳ‖ • (1 : A) := by
        have h := hx.ringInverse.isSelfAdjoint.le_algebraMap_norm_self
        rwa [Algebra.algebraMap_eq_smul_one] at h
      have hcmp := CStarAlgebra.ringInverse_le_ringInverse hiu hx.ringInverse
      rw [Ring.inverse_inverse hx.isUnit] at hcmp
      refine le_trans (le_of_eq ?_) hcmp
      have hmul : (‖x⁻¹ʳ‖ • (1 : A)) * (‖x⁻¹ʳ‖⁻¹ • (1 : A)) = 1 := by
        rw [smul_mul_smul_comm, one_mul, mul_inv_cancel₀ hinvpos.ne', one_smul]
      have hmul' : (‖x⁻¹ʳ‖⁻¹ • (1 : A)) * (‖x⁻¹ʳ‖ • (1 : A)) = 1 := by
        rw [smul_mul_smul_comm, one_mul, inv_mul_cancel₀ hinvpos.ne', one_smul]
      have hrep : (‖x⁻¹ʳ‖ • (1 : A))
          = ((⟨‖x⁻¹ʳ‖ • (1 : A), ‖x⁻¹ʳ‖⁻¹ • (1 : A), hmul, hmul'⟩ : Aˣ) : A) := rfl
      rw [hrep, Ring.inverse_unit]
      rfl
    have hle : ‖x⁻¹ʳ‖⁻¹ ≤ ‖x‖ := by
      have h1 : (1 : ℝ) ≤ ‖x‖ * ‖x⁻¹ʳ‖ := by
        have := norm_mul_le x x⁻¹ʳ
        rw [Ring.mul_inverse_cancel x hx.isUnit, norm_one] at this
        exact this
      rw [inv_le_iff_one_le_mul₀ hinvpos]
      linarith
    exact isUnit_lyapunov (inv_pos.mpr hinvpos) hle hx.isSelfAdjoint hlower hupper

/-- A strictly positive element of a nontrivial unital C⋆-algebra dominates a positive multiple
of the identity. -/
lemma exists_pos_smul_one_le [Nontrivial A] {a : A} (ha : IsStrictlyPositive a) :
    ∃ α : ℝ, 0 < α ∧ α • (1 : A) ≤ a := by
  have hane : a⁻¹ʳ ≠ 0 := by
    intro h
    have h1 : (1 : A) = 0 := by rw [← Ring.mul_inverse_cancel a ha.isUnit, h, mul_zero]
    exact one_ne_zero h1
  have hinvpos : 0 < ‖a⁻¹ʳ‖ := norm_pos_iff.mpr hane
  refine ⟨‖a⁻¹ʳ‖⁻¹, inv_pos.mpr hinvpos, ?_⟩
  have hiu : a⁻¹ʳ ≤ ‖a⁻¹ʳ‖ • (1 : A) := by
    have h := ha.ringInverse.isSelfAdjoint.le_algebraMap_norm_self
    rwa [Algebra.algebraMap_eq_smul_one] at h
  have hcmp := CStarAlgebra.ringInverse_le_ringInverse hiu ha.ringInverse
  rw [Ring.inverse_inverse ha.isUnit] at hcmp
  refine le_trans (le_of_eq ?_) hcmp
  have hmul : (‖a⁻¹ʳ‖ • (1 : A)) * (‖a⁻¹ʳ‖⁻¹ • (1 : A)) = 1 := by
    rw [smul_mul_smul_comm, one_mul, mul_inv_cancel₀ hinvpos.ne', one_smul]
  have hmul' : (‖a⁻¹ʳ‖⁻¹ • (1 : A)) * (‖a⁻¹ʳ‖ • (1 : A)) = 1 := by
    rw [smul_mul_smul_comm, one_mul, inv_mul_cancel₀ hinvpos.ne', one_smul]
  have hrep : (‖a⁻¹ʳ‖ • (1 : A))
      = ((⟨‖a⁻¹ʳ‖ • (1 : A), ‖a⁻¹ʳ‖⁻¹ • (1 : A), hmul, hmul'⟩ : Aˣ) : A) := rfl
  rw [hrep, Ring.inverse_unit]
  rfl

end

end GaloisForLFunctions.HTGeometry
