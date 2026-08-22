import GaloisForLFunctions.HTGeometry.BuresWasserstein.KantorovichConverse
import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinNormBounds

/-!
# Perturbation bounds for the square root and the inverse near the identity

The factorisation `c - 1 = (√c - 1)(√c + 1)` together with `1 ≤ √c + 1` gives the Lipschitz
bound `‖√c - 1‖ ≤ ‖c - 1‖` with no constant, and the same identity in the form
`a⁻¹ - 1 = -a⁻¹(a - 1)` bounds the inverse.  These are the elementary estimates that make the
Wasserstein vector field a contraction near the identity.
-/

open scoped Ring

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- `1 + x` is strictly positive for nonnegative `x`. -/
lemma isStrictlyPositive_one_add {x : A} (hx : 0 ≤ x) : IsStrictlyPositive (x + 1) := by
  have hle : (1 : ℝ) • (1 : A) ≤ x + 1 := by
    rw [one_smul]
    simpa using hx
  refine (CStarAlgebra.isUnit_of_le _ hle
    (IsStrictlyPositive.smul one_pos isStrictlyPositive_one)).isStrictlyPositive ?_
  exact le_trans (by simp) hle

/-- The inverse of `1 + x` is a contraction for nonnegative `x`. -/
lemma norm_ringInverse_one_add_le {x : A} (hx : 0 ≤ x) : ‖(x + 1)⁻¹ʳ‖ ≤ 1 := by
  have hle : (1 : ℝ) • (1 : A) ≤ x + 1 := by
    rw [one_smul]
    simpa using hx
  have h := ringInverse_le_of_smul_one_le one_pos hle
  rw [inv_one, one_smul] at h
  exact norm_le_of_le_smul_one (a := (x + 1)⁻¹ʳ)
    (isStrictlyPositive_one_add hx).ringInverse.nonneg zero_le_one
    (by rw [one_smul]; exact h)

/-- **The square root is a contraction at the identity**: `‖√c - 1‖ ≤ ‖c - 1‖`. -/
theorem norm_cfcSqrt_sub_one_le {c : A} (hc : 0 ≤ c) :
    ‖CFC.sqrt c - 1‖ ≤ ‖c - 1‖ := by
  have hs : CFC.sqrt c * CFC.sqrt c = c := CFC.sqrt_mul_sqrt_self c hc
  have hnn : (0 : A) ≤ CFC.sqrt c := CFC.sqrt_nonneg c
  have hpos : IsStrictlyPositive (CFC.sqrt c + 1) := isStrictlyPositive_one_add hnn
  have hfac : (CFC.sqrt c - 1) * (CFC.sqrt c + 1) = c - 1 := by
    have h : (CFC.sqrt c - 1) * (CFC.sqrt c + 1) = CFC.sqrt c * CFC.sqrt c - 1 := by
      noncomm_ring
    rw [h, hs]
  have hsplit : CFC.sqrt c - 1 = (c - 1) * (CFC.sqrt c + 1)⁻¹ʳ := by
    rw [← hfac, mul_assoc, Ring.mul_inverse_cancel _ hpos.isUnit, mul_one]
  calc ‖CFC.sqrt c - 1‖ = ‖(c - 1) * (CFC.sqrt c + 1)⁻¹ʳ‖ := by rw [hsplit]
    _ ≤ ‖c - 1‖ * ‖(CFC.sqrt c + 1)⁻¹ʳ‖ := norm_mul_le _ _
    _ ≤ ‖c - 1‖ * 1 := mul_le_mul_of_nonneg_left (norm_ringInverse_one_add_le hnn)
        (norm_nonneg _)
    _ = ‖c - 1‖ := mul_one _

/-- The half power is a contraction at the identity. -/
theorem norm_rpow_half_sub_one_le {a : A} (ha : 0 ≤ a) :
    ‖a ^ (1/2 : ℝ) - 1‖ ≤ ‖a - 1‖ := by
  rw [← CFC.sqrt_eq_rpow]
  exact norm_cfcSqrt_sub_one_le ha

omit [StarOrderedRing A] in
/-- The inverse is Lipschitz at the identity with constant `‖a⁻¹‖`. -/
theorem norm_ringInverse_sub_one_le {a : A} (ha : IsStrictlyPositive a) :
    ‖(a⁻¹ʳ : A) - 1‖ ≤ ‖(a⁻¹ʳ : A)‖ * ‖a - 1‖ := by
  have hsplit : (a⁻¹ʳ : A) - 1 = a⁻¹ʳ * (1 - a) := by
    rw [mul_sub, mul_one, Ring.inverse_mul_cancel _ ha.isUnit]
  calc ‖(a⁻¹ʳ : A) - 1‖ = ‖a⁻¹ʳ * (1 - a)‖ := by rw [hsplit]
    _ ≤ ‖(a⁻¹ʳ : A)‖ * ‖(1 : A) - a‖ := norm_mul_le _ _
    _ = ‖(a⁻¹ʳ : A)‖ * ‖a - 1‖ := by rw [← norm_neg ((1 : A) - a), neg_sub]

/-- The negative half power is Lipschitz at the identity. -/
theorem norm_rpow_neg_half_sub_one_le {a : A} (ha : IsStrictlyPositive a) :
    ‖(a ^ (-(1/2) : ℝ) : A) - 1‖ ≤ ‖(a ^ (-(1/2) : ℝ) : A)‖ * ‖a ^ (1/2 : ℝ) - 1‖ := by
  have hpos : IsStrictlyPositive (a ^ (1/2 : ℝ) : A) := ha.rpow a _
  rw [← ringInverse_rpow_half ha]
  exact norm_ringInverse_sub_one_le hpos

end

end GaloisForLFunctions.HTGeometry
