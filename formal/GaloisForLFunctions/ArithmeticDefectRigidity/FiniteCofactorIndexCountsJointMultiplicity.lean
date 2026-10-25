import GaloisForLFunctions.HTGeometry.FiniteCommutingAlgebraActionsHaveJointCharacters
import GaloisForLFunctions.ArithmeticOrientationTheory.NormalizedBohrCharacters
import GaloisForLFunctions.ArithmeticDefectRigidity.TheClosedCofactorAnnihilatorHasNoCountableIndex

/-!
# Finite cofactor index counts joint spectral multiplicity

The finite actual module hull is its joint generalized character locus.
After removing the redundant zero Bohr coordinate, the annihilator quotient
index is the sum of positive joint-space dimensions. Infinite index is continuum.
-/

section

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit

open ArithmeticOrientationTheory WienerAlgebraAt HTGeometry

/-- The actual Wiener action with continuity forgotten only in its target. -/
def algebraRepresentation {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) :
    WienerAlgebraAt (1 / 2) →ₐ[ℂ] Module.End ℂ (Hilbert L) where
  toFun a := (wienerRepresentation L a).toLinearMap
  map_zero' := by rw [map_zero]; rfl
  map_one' := by rw [map_one]; rfl
  map_add' a b := by rw [map_add]; rfl
  map_mul' a b := by rw [map_mul]; rfl
  commutes' z := by rw [(wienerRepresentation L).commutes]; rfl

theorem algebraRepresentation_eq_zero_iff {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) (a : WienerAlgebraAt (1 / 2)) :
    algebraRepresentation L a = 0 ↔ a ∈ annihilator L := by
  change (wienerRepresentation L a).toLinearMap = 0 ↔ wienerRepresentation L a = 0
  constructor
  · intro h
    ext x
    exact LinearMap.congr_fun h x
  · intro h
    rw [h]
    rfl

/-- Joint generalized eigenspace associated to a Bohr character of the actual module. -/
def jointBohrSpace {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (ω : BohrPoint) : Submodule ℂ (Hilbert L) :=
  algebraJointSpace (algebraRepresentation L) (fun a => ArithmeticOrientationTheory.bohrEval (1 / 2) a.toFn ω)

/-- In finite dimension the actual module hull is exactly the nonzero joint spectral locus. -/
theorem mem_moduleHull_iff_jointBohrSpace_ne_bot {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) [FiniteDimensional ℂ (Hilbert L)] (ω : BohrPoint) :
    ω ∈ moduleHull L ↔ jointBohrSpace L ω ≠ ⊥ := by
  constructor
  · intro hω
    obtain ⟨χ, hχ⟩ := character_eq_some_algebraJointCharacter (algebraRepresentation L)
      (ArithmeticOrientationTheory.WienerAlgebraAt.bohrCharacter (1 / 2) ω) (fun a ha => hω a
        ((algebraRepresentation_eq_zero_iff L a).mp ha))
    have heq : (fun a : WienerAlgebraAt (1 / 2) => ArithmeticOrientationTheory.bohrEval (1 / 2) a.toFn ω) = χ.val :=
      funext hχ
    change algebraJointSpace (algebraRepresentation L) _ ≠ ⊥
    rw [heq]
    exact χ.property
  · intro hω a ha
    exact algebraJointCharacter_eq_zero_of_map_eq_zero (algebraRepresentation L)
      (fun a => ArithmeticOrientationTheory.bohrEval (1 / 2) a.toFn ω) hω
      ((algebraRepresentation_eq_zero_iff L a).mpr ha)

/-- The module hull with its redundant zero coordinate removed. -/
abbrev NormalizedModuleHull {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) :=
  {ω : NormalizedBohrPoint // ω.val ∈ moduleHull L}

/-- Nonzero joint characters are exactly normalized points of the finite actual module hull. -/
def jointCharacterEquivNormalizedHull {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) [FiniteDimensional ℂ (Hilbert L)] :
    {χ : WienerAlgebraAt (1 / 2) → ℂ // algebraJointSpace (algebraRepresentation L) χ ≠ ⊥} ≃
      NormalizedModuleHull L where
  toFun χ :=
    ⟨normalizedBohrPointOfCharacter
      (algebraJointCharacter (algebraRepresentation L) χ.val χ.property), by
      intro a ha
      rw [normalizedBohrPointOfCharacter_eval]
      exact algebraJointCharacter_eq_zero_of_map_eq_zero (algebraRepresentation L)
        χ.val χ.property ((algebraRepresentation_eq_zero_iff L a).mpr ha)⟩
  invFun ω := ⟨fun a => ArithmeticOrientationTheory.bohrEval (1 / 2) a.toFn ω.val.val,
    (mem_moduleHull_iff_jointBohrSpace_ne_bot L ω.val.val).mp ω.property⟩
  left_inv χ := by
    apply Subtype.ext
    funext a
    exact normalizedBohrPointOfCharacter_eval
      (algebraJointCharacter (algebraRepresentation L) χ.val χ.property) a
  right_inv ω := by
    apply Subtype.ext
    apply normalizedBohrPoint_eq_of_character_eq (σ := (1 / 2 : ℝ))
    intro a
    rw [normalizedBohrPointOfCharacter_eval]
    rfl

/-- The normalized hull of every finite actual module is finite. -/
@[reducible]
def normalizedModuleHullFintype {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) [FiniteDimensional ℂ (Hilbert L)] :
    Fintype (NormalizedModuleHull L) := by
  letI := algebraJointCharacterFintype (algebraRepresentation L)
  exact Fintype.ofEquiv _ (jointCharacterEquivNormalizedHull L)

/-- The actual finite quotient index counts joint sector dimensions, including multiplicities. -/
theorem finrank_quotient_eq_sum_jointCharacter {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) [FiniteDimensional ℂ (Hilbert L)] :
    letI := algebraJointCharacterFintype (algebraRepresentation L)
    Module.finrank ℂ (WienerAlgebraAt (1 / 2) ⧸ annihilator L) =
      ∑ χ : {χ : WienerAlgebraAt (1 / 2) → ℂ //
        algebraJointSpace (algebraRepresentation L) χ ≠ ⊥},
        Module.finrank ℂ (algebraJointSpace (algebraRepresentation L) χ.val) := by
  rw [finrank_quotient_eq_of_finite]
  exact finrank_eq_sum_algebraJointSpace (algebraRepresentation L)

theorem jointBohrSpace_jointCharacterEquivNormalizedHull {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) [FiniteDimensional ℂ (Hilbert L)]
    (χ : {χ : WienerAlgebraAt (1 / 2) → ℂ //
      algebraJointSpace (algebraRepresentation L) χ ≠ ⊥}) :
    jointBohrSpace L (jointCharacterEquivNormalizedHull L χ).val.val =
      algebraJointSpace (algebraRepresentation L) χ.val := by
  unfold jointBohrSpace
  congr 1
  funext a
  exact normalizedBohrPointOfCharacter_eval
    (algebraJointCharacter (algebraRepresentation L) χ.val χ.property) a

/-- The finite index is the sum of generalized multiplicities over distinct normalized hull points. -/
theorem finrank_quotient_eq_sum_normalizedModuleHull {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) [FiniteDimensional ℂ (Hilbert L)] :
    letI := normalizedModuleHullFintype L
    Module.finrank ℂ (WienerAlgebraAt (1 / 2) ⧸ annihilator L) =
      ∑ ω : NormalizedModuleHull L, Module.finrank ℂ (jointBohrSpace L ω.val.val) := by
  classical
  letI := algebraJointCharacterFintype (algebraRepresentation L)
  letI := normalizedModuleHullFintype L
  rw [finrank_quotient_eq_sum_jointCharacter]
  apply Fintype.sum_equiv (jointCharacterEquivNormalizedHull L)
  intro χ
  rw [jointBohrSpace_jointCharacterEquivNormalizedHull]

/-- Every point counted by the finite module index has positive generalized multiplicity. -/
theorem jointBohrSpace_finrank_pos {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) [FiniteDimensional ℂ (Hilbert L)]
    (ω : NormalizedModuleHull L) : 0 < Module.finrank ℂ (jointBohrSpace L ω.val.val) := by
  letI : Nontrivial (jointBohrSpace L ω.val.val) :=
    Submodule.nontrivial_iff_ne_bot.mpr
      ((mem_moduleHull_iff_jointBohrSpace_ne_bot L ω.val.val).mp ω.property)
  exact Module.finrank_pos

/-- Every actual limit has a finite joint-multiplicity index or exactly continuum Hamel index. -/
theorem finite_joint_index_or_continuum {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) :
    (∃ h : FiniteDimensional ℂ (Hilbert L),
      letI := h
      letI := normalizedModuleHullFintype L
      Module.finrank ℂ (WienerAlgebraAt (1 / 2) ⧸ annihilator L) =
        ∑ ω : NormalizedModuleHull L, Module.finrank ℂ (jointBohrSpace L ω.val.val)) ∨
      Module.rank ℂ (WienerAlgebraAt (1 / 2) ⧸ annihilator L) = Cardinal.continuum := by
  by_cases h : FiniteDimensional ℂ (Hilbert L)
  · letI := h
    exact Or.inl ⟨h, finrank_quotient_eq_sum_normalizedModuleHull L⟩
  · exact Or.inr (annihilator_quotient_rank_eq_continuum_of_infinite L h)

end GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.mem_moduleHull_iff_jointBohrSpace_ne_bot
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.jointCharacterEquivNormalizedHull
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.finrank_quotient_eq_sum_jointCharacter
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.normalizedModuleHullFintype
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.finrank_quotient_eq_sum_normalizedModuleHull
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.jointBohrSpace_finrank_pos
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.finite_joint_index_or_continuum
end
end
