import GaloisForLFunctions.RHTower.EulerCutoffConstraintAlgebra

/-!
# Hasse detection by cofinal Euler cutoff quotients

The Euler coordinate algebra embeds in the product of all finite cutoff quotients.  Consequently,
its global elements are exactly their realized cutoff profiles, and equality or vanishing can be
checked at every finite cutoff.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The Euler coordinate algebra is algebra-equivalent to the cofinal quotient profiles it
realizes. -/
noncomputable def eulerCofinalQuotientHasseEquivRange :
    AddMonoidAlgebra ℂ ℂ ≃ₐ[ℂ] AlgHom.range eulerCofinalQuotientMap :=
  AlgEquiv.ofBijective (AlgHom.rangeRestrict eulerCofinalQuotientMap)
    ⟨fun _ _ h => eulerCofinalQuotientMap_injective (congrArg Subtype.val h),
      AlgHom.rangeRestrict_surjective _⟩

/-- The realized-profile equivalence evaluates by the simultaneous finite-cutoff map. -/
@[simp] theorem eulerCofinalQuotientHasseEquivRange_apply
    (a : AddMonoidAlgebra ℂ ℂ) :
    (eulerCofinalQuotientHasseEquivRange a).1 = eulerCofinalQuotientMap a := by
  rfl

/-- Two global Euler coordinate-algebra elements agree exactly when they agree in every finite
cutoff quotient. -/
theorem eulerCofinalQuotient_congr_hasse_iff
    (a b : AddMonoidAlgebra ℂ ℂ) :
    (∀ N : ℕ, eulerCofinalQuotientMap a N = eulerCofinalQuotientMap b N) ↔ a = b := by
  constructor
  · intro h
    apply eulerCofinalQuotientMap_injective
    funext N
    exact h N
  · rintro rfl N
    rfl

/-- A global Euler coordinate-algebra element vanishes exactly when every finite-cutoff image
vanishes. -/
theorem eulerCofinalQuotient_eq_zero_hasse_iff
    (a : AddMonoidAlgebra ℂ ℂ) :
    (∀ N : ℕ, eulerCofinalQuotientMap a N = 0) ↔ a = 0 := by
  rw [← eulerCofinalQuotient_congr_hasse_iff a 0]
  simp

end


end GaloisForLFunctions.RHTower
