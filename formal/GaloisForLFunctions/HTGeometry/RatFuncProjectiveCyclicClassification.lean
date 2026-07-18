import GaloisForLFunctions.HTGeometry.RatFuncProjectiveNormalForm
import Mathlib.GroupTheory.OrderOfElement

/-!
# Cyclic projective normal-form classification

This leaf refines the scaling-or-translation projective normal form by separating the scaling
case into nontrivial finite cyclic and infinite-order branches.  It is the purely projective
four-branch parent of the scalar persistent-gauge classification.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K : Type*} [Field K]

/-- Every coefficient-fixing rational-function automorphism over an algebraically closed field is
either the identity, conjugate to a nontrivial finite-order scaling, conjugate to an infinite-order
scaling, or conjugate to unit translation. -/
theorem ratFuncAlgEquiv_cyclicNormalForm
    [IsAlgClosed K] (e : RatFunc K ≃ₐ[K] RatFunc K) :
    e = AlgEquiv.refl ∨
      (∃ (h : RatFunc K ≃ₐ[K] RatFunc K) (u : Kˣ) (N : ℕ),
        2 ≤ N ∧ orderOf u = N ∧
          h.symm * e * h = ratFuncUnitScaleEquiv u) ∨
      (∃ (h : RatFunc K ≃ₐ[K] RatFunc K) (u : Kˣ),
        orderOf u = 0 ∧
          h.symm * e * h = ratFuncUnitScaleEquiv u) ∨
      (∃ h : RatFunc K ≃ₐ[K] RatFunc K,
        h.symm * e * h = ratFuncTranslationEquiv 1) := by
  by_cases he : e = AlgEquiv.refl
  · exact Or.inl he
  · right
    rcases ratFuncAlgEquiv_normalForm e he with hscale | htranslation
    · obtain ⟨h, u, hu⟩ := hscale
      have huOne : u ≠ 1 := by
        intro hu1
        apply he
        calc
          e = h * (h.symm * e * h) * h.symm := by
            change e = h * (h⁻¹ * e * h) * h⁻¹
            group
          _ = h * ratFuncUnitScaleEquiv u * h.symm := by rw [hu]
          _ = h * AlgEquiv.refl * h.symm := by
            rw [hu1, ratFuncUnitScaleEquiv_one]
          _ = AlgEquiv.refl := by
            change h * 1 * h⁻¹ = 1
            group
      by_cases horder : orderOf u = 0
      · exact Or.inr (Or.inl ⟨h, u, horder, hu⟩)
      · left
        have horderOne : orderOf u ≠ 1 := by
          intro h
          exact huOne (orderOf_eq_one_iff.mp h)
        refine ⟨h, u, orderOf u, ?_, rfl, hu⟩
        have hpos : 0 < orderOf u := Nat.pos_of_ne_zero horder
        omega
    · exact Or.inr (Or.inr htranslation)

end

end GaloisForLFunctions.HTGeometry
