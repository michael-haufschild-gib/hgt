import GaloisForLFunctions.HTGeometry.SmallestNeighbourhoodSections
import GaloisForLFunctions.HTGeometry.SpecDimOneLocalDomain
import GaloisForLFunctions.HTGeometry.SpecStalkLocalization

/-!
# The three section rings of a one-dimensional local domain

For a local domain `𝒪` which is not a field and in which every nonzero prime is maximal, the
spectrum has the three open sets `∅`, `{η}` and `⊤`.  The sections of the structure sheaf are the
zero ring, the fraction field and `𝒪` itself: the generic point is its own smallest open
neighbourhood, so its sections are its stalk.
-/

namespace HTGeometry

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry PrimeSpectrum IsLocalRing

universe u

variable (R : CommRingCat.{u}) [IsDomain R] [IsLocalRing R]
variable (hdim : ∀ P : Ideal R, P.IsPrime → P = ⊥ ∨ P = maximalIdeal R)
variable (hfield : ¬ IsField R)

/-- The open subset of the spectrum consisting of the generic point. -/
def specGenericOpen : (Spec R).Opens := ⟨{specGeneric R}, isOpen_specGeneric hdim hfield⟩

theorem mem_specGenericOpen : specGeneric (R : Type u) ∈ specGenericOpen R hdim hfield := rfl

theorem specGenericOpen_le (W : (Spec R).Opens) (hW : specGeneric (R : Type u) ∈ W) :
    specGenericOpen R hdim hfield ≤ W := by
  intro q hq
  have hq' : q = specGeneric (R : Type u) := hq
  rw [hq']
  exact hW

/-- The germ at the generic point on the sections over the open point is an isomorphism. -/
instance isIso_germ_specGenericOpen :
    IsIso ((Spec R).presheaf.germ (specGenericOpen R hdim hfield) (specGeneric (R : Type u))
      (mem_specGenericOpen R hdim hfield)) :=
  isIso_germ_of_isMin _ _ _ _ (specGenericOpen_le R hdim hfield)

/-- **The sections of the structure sheaf over the open generic point are the fraction field.** -/
noncomputable def specGenericSectionsEquiv :
    FractionRing (R : Type u) ≃+*
      ((Spec R).presheaf.obj (op (specGenericOpen R hdim hfield)) : Type u) :=
  (specGenericStalkEquiv R (specGeneric (R : Type u)) rfl).trans
    (asIso ((Spec R).presheaf.germ (specGenericOpen R hdim hfield) (specGeneric (R : Type u))
      (mem_specGenericOpen R hdim hfield))).symm.commRingCatIsoToRingEquiv

/-- **The sections of the structure sheaf over the whole spectrum are the ring itself.** -/
noncomputable def specTopSectionsEquiv :
    (R : Type u) ≃+* ((Spec R).presheaf.obj (op ⊤) : Type u) :=
  (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv

/-- **The sections of the structure sheaf over the empty open set form the zero ring.** -/
instance specEmptySections_subsingleton :
    Subsingleton ((Spec R).presheaf.obj (op ⊥) : Type u) :=
  inferInstanceAs (Subsingleton (Γ(Spec R, ⊥) : Type u))

/-- The only open subsets of the spectrum are `∅`, the generic point and the whole space. -/
theorem specOpens_cases (U : (Spec R).Opens) :
    U = ⊥ ∨ U = specGenericOpen R hdim hfield ∨ U = ⊤ := by
  rcases spec_isOpen_cases hdim U.2 with h | h | h
  · exact Or.inl (Opens.ext h)
  · exact Or.inr (Or.inl (Opens.ext h))
  · exact Or.inr (Or.inr (Opens.ext h))

include hdim hfield in
theorem specClosed_mem_iff (U : (Spec R).Opens) :
    specClosed (R : Type u) ∈ U ↔ U = ⊤ := by
  constructor
  · intro hU
    rcases specOpens_cases R hdim hfield U with h | h | h
    · rw [h] at hU; exact hU.elim
    · rw [h] at hU
      have : specClosed (R : Type u) = specGeneric (R : Type u) := hU
      exact absurd this.symm (specGeneric_ne_specClosed hfield)
    · exact h
  · intro h; rw [h]; trivial

include hdim hfield in
theorem specGeneric_mem_iff (U : (Spec R).Opens) :
    specGeneric (R : Type u) ∈ U ↔ U ≠ ⊥ := by
  constructor
  · intro hU h
    rw [h] at hU
    exact hU.elim
  · intro h
    rcases specOpens_cases R hdim hfield U with h0 | h0 | h0
    · exact absurd h0 h
    · rw [h0]; exact mem_specGenericOpen R hdim hfield
    · rw [h0]; trivial

end HTGeometry
