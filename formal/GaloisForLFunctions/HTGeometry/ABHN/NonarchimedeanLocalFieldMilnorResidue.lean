/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanLocalFieldValuationSequence
import GaloisForLFunctions.HTGeometry.MilnorKResidueUniformizer
import GaloisForLFunctions.HTGeometry.MilnorKFiniteDegreeOne

/-!
# Tame Milnor residue for nonarchimedean local fields

Every nonarchimedean local field has a uniformizer and its residue units lift to valuation-zero
units.  Thus the degree-two tame Milnor symbol is onto the residue-unit group, giving its explicit
first-isomorphism quotient.  This is the `K₂` input to local Brauer theory, but does not assert a
`K₂`--Brauer comparison or a local invariant isomorphism.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped ValuativeRel WithZeroMulInt

universe u

/-- Milnor `K`-theory of the finite residue field of a nonarchimedean local field vanishes in
every degree at least two. -/
theorem nonarchimedeanLocalField_residueMilnorKDeg_eq_zero
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ)
    (x : MilnorKDeg
      (IsLocalRing.ResidueField (nonarchimedeanLocalFieldIntValuation K).valuationSubring)
        (2 + n)) : x = 0 := by
  letI : Fintype (IsLocalRing.ResidueField
      (nonarchimedeanLocalFieldIntValuation K).valuationSubring) := Fintype.ofFinite _
  exact milnorKDeg_eq_zero_of_finite n x

/-- Every higher Milnor `K`-group of the finite residue field of a nonarchimedean local field is
trivial. -/
theorem nonarchimedeanLocalField_residueMilnorKDeg_subsingleton
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) :
    Subsingleton (MilnorKDeg
      (IsLocalRing.ResidueField (nonarchimedeanLocalFieldIntValuation K).valuationSubring)
        (2 + n)) where
  allEq x y := (nonarchimedeanLocalField_residueMilnorKDeg_eq_zero K n x).trans
    (nonarchimedeanLocalField_residueMilnorKDeg_eq_zero K n y).symm

/-- Every residue-field unit lifts to a valuation-zero unit of a nonarchimedean local field. -/
theorem nonarchimedeanLocalField_residueUnit_surjective
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (y : (IsLocalRing.ResidueField
      (nonarchimedeanLocalFieldIntValuation K).valuationSubring)ˣ) :
    ∃ a : Kˣ, (nonarchimedeanLocalFieldResidueData K).val' a = 0 ∧
      (nonarchimedeanLocalFieldResidueData K).residueUnit a = y := by
  let v := nonarchimedeanLocalFieldIntValuation K
  let A := v.valuationSubring
  obtain ⟨x, hx⟩ := IsLocalRing.residue_surjective (y : IsLocalRing.ResidueField A)
  have hres0 : IsLocalRing.residue A x ≠ 0 := by
    rw [hx]
    exact y.ne_zero
  obtain ⟨u, hu⟩ := (IsLocalRing.residue_ne_zero_iff_isUnit x).mp hres0
  let a : Kˣ := Units.map A.subtype.toMonoidHom u
  have haVal : v (a : K) = 1 := by
    change v (algebraMap A K (u : A)) = 1
    exact (Valuation.integer.integers v).valuation_unit u
  have haKer : a ∈ (tameValHom v).ker :=
    (tameValHom_mem_ker_iff v a).2 haVal
  refine ⟨a, ?_, ?_⟩
  · exact (nonarchimedeanLocalFieldResidueData K).val'_eq_zero_iff.2 haKer
  · apply Units.ext
    rw [ResidueData.residueUnit_of_mem_ker _ haKer]
    change IsLocalRing.residue A ((u : Aˣ) : A) = (y : IsLocalRing.ResidueField A)
    rw [hu, hx]

/-- The degree-two tame symbol of a nonarchimedean local field is surjective. -/
theorem nonarchimedeanLocalField_tameHom_surjective
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    Function.Surjective (nonarchimedeanLocalFieldResidueData K).tameHom := by
  intro y
  obtain ⟨a, ha, hay⟩ := nonarchimedeanLocalField_residueUnit_surjective K y.toMul
  have haKer : a ∈ (nonarchimedeanLocalFieldResidueData K).val.ker :=
    (nonarchimedeanLocalFieldResidueData K).val'_eq_zero_iff.1 ha
  refine ⟨milnorClassDeg K 2 ⟨[a, (nonarchimedeanLocalFieldResidueData K).unif], rfl⟩, ?_⟩
  rw [TameData.tameHom_symbol, TameData.tame_of_mem_ker_left
    (nonarchimedeanLocalFieldResidueData K).toTameData haKer]
  apply Additive.toMul.injective
  change (nonarchimedeanLocalFieldResidueData K).res ⟨a, haKer⟩ ^
    (nonarchimedeanLocalFieldResidueData K).val'
      (nonarchimedeanLocalFieldResidueData K).unif = y.toMul
  rw [(nonarchimedeanLocalFieldResidueData K).val'_unif, zpow_one]
  rw [← (nonarchimedeanLocalFieldResidueData K).residueUnit_of_mem_ker haKer, hay]

/-- The degree-two tame residue written in the standard Milnor form
`K₂ᴹ(K) → K₁ᴹ(k)`. -/
noncomputable def nonarchimedeanLocalFieldTameMilnorResidue
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    MilnorKDeg K 2 →+ MilnorKDeg
      (IsLocalRing.ResidueField (nonarchimedeanLocalFieldIntValuation K).valuationSubring) 1 :=
  (milnorDegOneEquiv _).symm.toAddMonoidHom.comp
    (nonarchimedeanLocalFieldResidueData K).tameHom

/-- The local degree-two tame residue onto `K₁ᴹ` of the residue field is surjective. -/
theorem nonarchimedeanLocalField_tameMilnorResidue_surjective
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    Function.Surjective (nonarchimedeanLocalFieldTameMilnorResidue K) := by
  intro y
  obtain ⟨x, hx⟩ := nonarchimedeanLocalField_tameHom_surjective K
    (milnorDegOneEquiv _ y)
  refine ⟨x, ?_⟩
  change (milnorDegOneEquiv _).symm
      ((nonarchimedeanLocalFieldResidueData K).tameHom x) = y
  rw [hx]
  exact (milnorDegOneEquiv _).symm_apply_apply y

/-- The tame quotient of local Milnor `K₂` is the first Milnor `K`-group of its residue field. -/
noncomputable def nonarchimedeanLocalFieldTameMilnorResidueQuotientKerEquiv
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    MilnorKDeg K 2 ⧸ (nonarchimedeanLocalFieldTameMilnorResidue K).ker ≃+
      MilnorKDeg
        (IsLocalRing.ResidueField (nonarchimedeanLocalFieldIntValuation K).valuationSubring) 1 :=
  QuotientAddGroup.quotientKerEquivOfSurjective
    (nonarchimedeanLocalFieldTameMilnorResidue K)
    (nonarchimedeanLocalField_tameMilnorResidue_surjective K)

/-- The local `K₂ᴹ` quotient by the standard tame residue kernel is finite. -/
noncomputable instance nonarchimedeanLocalFieldTameMilnorResidueQuotientFinite
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    Finite (MilnorKDeg K 2 ⧸ (nonarchimedeanLocalFieldTameMilnorResidue K).ker) :=
  Finite.of_equiv
    (MilnorKDeg
      (IsLocalRing.ResidueField (nonarchimedeanLocalFieldIntValuation K).valuationSubring) 1)
    (nonarchimedeanLocalFieldTameMilnorResidueQuotientKerEquiv K).toEquiv.symm

/-- The local `K₂ᴹ` quotient by the standard tame residue kernel is cyclic. -/
theorem nonarchimedeanLocalFieldTameMilnorResidueQuotient_isAddCyclic
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    IsAddCyclic (MilnorKDeg K 2 ⧸ (nonarchimedeanLocalFieldTameMilnorResidue K).ker) :=
  (nonarchimedeanLocalFieldTameMilnorResidueQuotientKerEquiv K).isAddCyclic.mpr
    (finiteMilnorKDegOne_isAddCyclic _)

/-- The tame quotient of local Milnor `K₂` is the residue-unit group. -/
noncomputable def nonarchimedeanLocalFieldTameHomQuotientKerEquiv
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    MilnorKDeg K 2 ⧸ (nonarchimedeanLocalFieldResidueData K).tameHom.ker ≃+
      Additive (IsLocalRing.ResidueField
        (nonarchimedeanLocalFieldIntValuation K).valuationSubring)ˣ :=
  QuotientAddGroup.quotientKerEquivOfSurjective (nonarchimedeanLocalFieldResidueData K).tameHom
    (nonarchimedeanLocalField_tameHom_surjective K)

/-- The tame quotient of local Milnor `K₂` is finite. -/
noncomputable instance nonarchimedeanLocalFieldTameHomQuotientFinite
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    Finite (MilnorKDeg K 2 ⧸ (nonarchimedeanLocalFieldResidueData K).tameHom.ker) :=
  Finite.of_equiv
    (Additive (IsLocalRing.ResidueField
      (nonarchimedeanLocalFieldIntValuation K).valuationSubring)ˣ)
    (nonarchimedeanLocalFieldTameHomQuotientKerEquiv K).toEquiv.symm

/-- The tame quotient of local Milnor `K₂` is cyclic, as is the unit group of its finite
residue field. -/
theorem nonarchimedeanLocalFieldTameHomQuotient_isAddCyclic
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    IsAddCyclic (MilnorKDeg K 2 ⧸ (nonarchimedeanLocalFieldResidueData K).tameHom.ker) :=
  (nonarchimedeanLocalFieldTameHomQuotientKerEquiv K).isAddCyclic.mpr inferInstance

end GaloisForLFunctions.HTGeometry.ABHN
