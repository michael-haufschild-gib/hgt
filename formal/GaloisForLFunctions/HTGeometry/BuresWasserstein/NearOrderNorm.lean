import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinNearOrder
import GaloisForLFunctions.HTGeometry.OperatorNormLoewner

/-!
# The near-order dominates the operator norm

If `p ⪯ q`, that is `1 ≤ p⁻¹ # q`, then `‖p‖ ≤ ‖q‖`.  Writing `X := p⁻¹ # q`, the Riccati
equation gives `X p X = q`, so with `P := √p` one has `q = (P X)^* (P X)` and
`‖q‖ = ‖P X‖²`.  Since `1 ≤ X` forces `‖X⁻¹‖ ≤ 1`, we get `‖P‖ ≤ ‖P X‖ ‖X⁻¹‖ ≤ ‖P X‖`, and
`‖p‖ = ‖P‖² ≤ ‖P X‖² = ‖q‖`.
-/

open scoped NNReal Ring

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

open GaloisForLFunctions.HTGeometry

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **The near-order dominates the operator norm.** -/
theorem NearLE.norm_le {p q : A} (hp : IsStrictlyPositive p) (hq : IsStrictlyPositive q)
    (h : NearLE p q) : ‖p‖ ≤ ‖q‖ := by
  obtain ⟨X, hXdef⟩ : ∃ x : A, x = gm p⁻¹ʳ q := ⟨_, rfl⟩
  have hX1 : (1 : A) ≤ X := by rw [hXdef]; exact h
  have hXpos : IsStrictlyPositive X := by
    refine isStrictlyPositive_of_smul_one_le one_pos ?_
    rwa [one_smul]
  have hXsa : IsSelfAdjoint X := hXpos.isSelfAdjoint
  -- the Riccati equation
  have hric : X * p * X = q := by
    have h1 := gm_riccati hp.ringInverse hq
    rwa [Ring.inverse_inverse hp.isUnit, ← hXdef] at h1
  -- factor through the square root of `p`
  obtain ⟨P, hPdef⟩ : ∃ z : A, z = CFC.sqrt p := ⟨_, rfl⟩
  have hPsa : IsSelfAdjoint P := by rw [hPdef]; exact (CFC.sqrt_nonneg p).isSelfAdjoint
  have hPP : P * P = p := by rw [hPdef]; exact CFC.sqrt_mul_sqrt_self p hp.nonneg
  have hfac : q = star (P * X) * (P * X) := by
    rw [star_mul, hPsa.star_eq, hXsa.star_eq, ← hric, ← hPP]
    noncomm_ring
  have hnq : ‖q‖ = ‖P * X‖ * ‖P * X‖ := by
    rw [hfac, CStarRing.norm_star_mul_self]
  -- `‖X⁻¹‖ ≤ 1`
  have hXinv : ‖(X⁻¹ʳ : A)‖ ≤ 1 := by
    have h1 : (X⁻¹ʳ : A) ≤ (1 : ℝ) • (1 : A) := by
      have := ringInverse_le_of_smul_one_le (a := X) (m := 1) one_pos (by rwa [one_smul])
      rwa [inv_one] at this
    exact norm_le_of_le_smul_one hXpos.ringInverse.nonneg zero_le_one h1
  have hPle : ‖P‖ ≤ ‖P * X‖ := by
    have hid : P = P * X * X⁻¹ʳ := by
      rw [mul_assoc, Ring.mul_inverse_cancel _ hXpos.isUnit, mul_one]
    calc ‖P‖ = ‖P * X * (X⁻¹ʳ : A)‖ := by rw [← hid]
      _ ≤ ‖P * X‖ * ‖(X⁻¹ʳ : A)‖ := norm_mul_le _ _
      _ ≤ ‖P * X‖ * 1 := mul_le_mul_of_nonneg_left hXinv (norm_nonneg _)
      _ = ‖P * X‖ := mul_one _
  have hnp : ‖p‖ = ‖P‖ * ‖P‖ := by
    have h1 : p = star P * P := by rw [hPsa.star_eq, hPP]
    rw [h1, CStarRing.norm_star_mul_self]
  rw [hnp, hnq]
  exact mul_le_mul hPle hPle (norm_nonneg _) (norm_nonneg _)

end

end GaloisForLFunctions.HTGeometry.BuresWasserstein
