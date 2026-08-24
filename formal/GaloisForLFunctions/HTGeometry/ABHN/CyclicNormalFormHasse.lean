import GaloisForLFunctions.HTGeometry.ABHN.CyclicCompanionHasse

/-!
# Bounded normal-form Hasse coordinates for compatible cyclic algebras

A compatible raw cyclic algebra has one coefficient in its defining field at each exponent below
the cyclic degree.  Existing companion faithfulness makes those bounded coordinates unique.  This
file exposes the resulting additive equivalence, unique-coordinate existence, coefficientwise
congruence, zero detection, and finite detecting witnesses.

This complements matrix-entry Hasse separation: companion entries are external representation
coordinates, while these are intrinsic cyclic-algebra coefficients.  Neither is yet the local
Brauer invariant required by full ABHN reciprocity.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry.ABHN
namespace CyclicCompanionDatum

universe u

variable {L : Type u} [Field L]

/-- Additive equivalence between bounded coefficient packets and a compatible cyclic algebra. -/
noncomputable def normalFormEquiv (D : CyclicCompanionDatum L) :
    (Fin (D.predDegree + 1) → L) ≃+
      CyclicAlgebra D.automorphism (D.predDegree + 1) D.parameter :=
  cyclicCompanionNormalFormAddEquiv D.automorphism D.predDegree D.parameter
    D.order_eq_one D.parameter_fixed

/-- Unique bounded coefficient profile of a compatible cyclic-algebra element. -/
noncomputable def normalFormCoordinates (D : CyclicCompanionDatum L)
    (x : CyclicAlgebra D.automorphism (D.predDegree + 1) D.parameter) :
    Fin (D.predDegree + 1) → L :=
  D.normalFormEquiv.symm x

/-- Reconstruct an element from its unique bounded coefficient profile. -/
theorem normalForm_reconstruct (D : CyclicCompanionDatum L)
    (x : CyclicAlgebra D.automorphism (D.predDegree + 1) D.parameter) :
    cyclicCompanionNormalForm D.automorphism D.predDegree D.parameter
      (D.normalFormCoordinates x) = x := by
  change D.normalFormEquiv (D.normalFormEquiv.symm x) = x
  exact D.normalFormEquiv.apply_symm_apply x

/-- Every compatible cyclic-algebra element has one unique bounded local coefficient packet. -/
theorem normalForm_hasse_existsUnique (D : CyclicCompanionDatum L)
    (x : CyclicAlgebra D.automorphism (D.predDegree + 1) D.parameter) :
    ∃! f : Fin (D.predDegree + 1) → L,
      cyclicCompanionNormalForm D.automorphism D.predDegree D.parameter f = x := by
  refine ⟨D.normalFormCoordinates x, D.normalForm_reconstruct x, ?_⟩
  intro f hf
  change D.normalFormEquiv f = x at hf
  have h := congrArg D.normalFormEquiv.symm hf
  simpa [normalFormCoordinates] using h

/-- Cyclic-algebra elements agree exactly when every bounded normal-form coefficient agrees. -/
theorem congr_normalFormCoordinate_hasse_iff (D : CyclicCompanionDatum L)
    (x y : CyclicAlgebra D.automorphism (D.predDegree + 1) D.parameter) :
    x = y ↔ ∀ i, D.normalFormCoordinates x i = D.normalFormCoordinates y i := by
  constructor
  · rintro rfl
    exact fun _ ↦ rfl
  · intro h
    apply D.normalFormEquiv.symm.injective
    funext i
    exact h i

/-- A cyclic-algebra element is zero exactly when all normal-form coefficients vanish. -/
theorem eq_zero_normalFormCoordinate_hasse_iff (D : CyclicCompanionDatum L)
    (x : CyclicAlgebra D.automorphism (D.predDegree + 1) D.parameter) :
    x = 0 ↔ ∀ i, D.normalFormCoordinates x i = 0 := by
  rw [D.congr_normalFormCoordinate_hasse_iff]
  simp [normalFormCoordinates]

/-- Every nonzero compatible cyclic-algebra element has a nonzero bounded coefficient. -/
theorem exists_normalFormCoordinate_ne_zero_of_ne_zero
    (D : CyclicCompanionDatum L)
    (x : CyclicAlgebra D.automorphism (D.predDegree + 1) D.parameter)
    (hx : x ≠ 0) :
    ∃ i, D.normalFormCoordinates x i ≠ 0 := by
  by_contra h
  push Not at h
  exact hx ((D.eq_zero_normalFormCoordinate_hasse_iff x).2 h)

end CyclicCompanionDatum
end GaloisForLFunctions.HTGeometry.ABHN
