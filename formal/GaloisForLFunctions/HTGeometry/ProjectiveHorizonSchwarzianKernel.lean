import GaloisForLFunctions.HTGeometry.ProjectiveHorizonSchwarzianMeet

/-!
# The Schwarzian field lies in the common kernel of the chart currents

The locus where a derivation vanishes is an intermediate field, so it is enough that the currents
annihilate the generators.  They annihilate every jet of the Schwarzian, hence the whole
differential field it generates.

This is the easy inclusion of the depth-one meet; the reverse one is the coordinate argument.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential

variable {C : Type*} [Field C] [CharZero C]

omit [CharZero C] in
/-- A derivation annihilating every jet of the Schwarzian annihilates the differential field it
generates. -/
theorem schwarzianDifferentialField_le_ker
    (D : Derivation C (FreeScalarJetField C) (FreeScalarJetField C))
    (hD : ∀ k : ℕ, D (differentialJet k (freeJetSchwarzian C)) = 0) :
    schwarzianDifferentialField C ≤ derivationEqualizer D 0 := by
  rw [schwarzianDifferentialField]
  refine adjoin_le_derivationEqualizer ?_
  rintro _ ⟨k, rfl⟩
  rw [hD k, Derivation.zero_apply]

omit [CharZero C] in
/-- **The translation current annihilates the Schwarzian field.** -/
theorem freeCoordinateDerivation_zero_eq_zero_of_mem_schwarzianDifferentialField
    {f : FreeScalarJetField C} (hf : f ∈ schwarzianDifferentialField C) :
    freeCoordinateDerivation C ℕ 0 f = 0 := by
  have h := schwarzianDifferentialField_le_ker (freeCoordinateDerivation C ℕ 0)
    freeCoordinateDerivation_zero_schwarzianJet hf
  rw [mem_derivationEqualizer_iff, Derivation.zero_apply] at h
  exact h

/-- **The inversion current annihilates the Schwarzian field.** -/
theorem freeJetFZero_eq_zero_of_mem_schwarzianDifferentialField
    {f : FreeScalarJetField C} (hf : f ∈ schwarzianDifferentialField C) :
    freeJetFZero C f = 0 := by
  have h := schwarzianDifferentialField_le_ker (freeJetFZero C) freeJetFZero_schwarzianJet hf
  rw [mem_derivationEqualizer_iff, Derivation.zero_apply] at h
  exact h

/-- **The scaling current annihilates the Schwarzian field.** -/
theorem jetH_eq_zero_of_mem_schwarzianDifferentialField
    {f : FreeScalarJetField C} (hf : f ∈ schwarzianDifferentialField C) :
    jetH C f = 0 := by
  have h := schwarzianDifferentialField_le_ker (jetH C) jetH_schwarzianJet hf
  rw [mem_derivationEqualizer_iff, Derivation.zero_apply] at h
  exact h

end

end GaloisForLFunctions.HTGeometry
