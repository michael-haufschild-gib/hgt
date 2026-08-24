import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraCompanionRepresentation

/-!
# Matrix-entry Hasse principle for compatible cyclic algebras

Compatibility of a cyclic automorphism and its fixed parameter is packaged as intrinsic data.
The resulting cyclic algebra embeds faithfully into its weighted companion matrix ring.  Hence
equality and vanishing are detected entrywise, every nonzero algebra element has one detecting
matrix coordinate, and the algebra is ring-equivalent to the companion matrices it realizes.

This is direct cyclic-algebra infrastructure for ABHN-style arguments.  It is a faithful splitting
representation, not a local Brauer invariant or global reciprocity theorem.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

universe u

/-- Intrinsic data for a compatible all-degree cyclic companion representation. -/
structure CyclicCompanionDatum (L : Type u) [Field L] where
  automorphism : L ≃+* L
  predDegree : ℕ
  parameter : L
  order_eq_one : automorphism ^ (predDegree + 1) = 1
  parameter_fixed : automorphism parameter = parameter

namespace CyclicCompanionDatum

variable {L : Type u} [Field L]

/-- Faithful weighted companion representation attached to compatible cyclic data. -/
noncomputable def representation (D : CyclicCompanionDatum L) :
    CyclicAlgebra D.automorphism (D.predDegree + 1) D.parameter →+*
      Matrix (Fin (D.predDegree + 1)) (Fin (D.predDegree + 1)) L :=
  cyclicCompanionRepresentation D.automorphism D.predDegree D.parameter
    D.order_eq_one D.parameter_fixed

/-- Packaged cyclic companion representation is injective. -/
theorem representation_injective (D : CyclicCompanionDatum L) :
    Function.Injective D.representation :=
  cyclicCompanionRepresentation_injective D.automorphism D.predDegree D.parameter
    D.order_eq_one D.parameter_fixed

/-- A compatible cyclic algebra is ring-equivalent to its realized companion matrices. -/
noncomputable def representationEquivRange (D : CyclicCompanionDatum L) :
    CyclicAlgebra D.automorphism (D.predDegree + 1) D.parameter ≃+*
      RingHom.range D.representation :=
  RingEquiv.ofBijective (RingHom.rangeRestrict D.representation)
    ⟨fun _ _ h ↦ D.representation_injective (congrArg Subtype.val h),
      RingHom.rangeRestrict_surjective _⟩

/-- Matrix-entry Hasse congruence for compatible cyclic algebras. -/
theorem congr_companionEntry_hasse_iff
    (D : CyclicCompanionDatum L)
    (x y : CyclicAlgebra D.automorphism (D.predDegree + 1) D.parameter) :
    x = y ↔ ∀ i j, D.representation x i j = D.representation y i j := by
  constructor
  · rintro rfl
    exact fun _ _ ↦ rfl
  · intro h
    apply D.representation_injective
    ext i j
    exact h i j

/-- A cyclic-algebra element vanishes exactly when every companion entry vanishes. -/
theorem eq_zero_companionEntry_hasse_iff
    (D : CyclicCompanionDatum L)
    (x : CyclicAlgebra D.automorphism (D.predDegree + 1) D.parameter) :
    x = 0 ↔ ∀ i j, D.representation x i j = 0 := by
  rw [D.congr_companionEntry_hasse_iff]
  simp

/-- Every nonzero cyclic-algebra element is detected by one companion-matrix entry. -/
theorem exists_companionEntry_ne_zero_of_ne_zero
    (D : CyclicCompanionDatum L)
    (x : CyclicAlgebra D.automorphism (D.predDegree + 1) D.parameter)
    (hx : x ≠ 0) :
    ∃ i j, D.representation x i j ≠ 0 := by
  by_contra h
  push Not at h
  exact hx ((D.eq_zero_companionEntry_hasse_iff x).2 h)

end CyclicCompanionDatum

end

end GaloisForLFunctions.HTGeometry.ABHN
