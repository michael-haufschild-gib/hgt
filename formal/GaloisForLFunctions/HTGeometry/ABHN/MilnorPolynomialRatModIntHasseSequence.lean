/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.MilnorPolynomialHeterogeneousRatModIntReciprocity
import GaloisForLFunctions.HTGeometry.MilnorPolynomialGlobalReciprocityQuotient

/-!
# A finite-layer ABHN sequence for polynomial Milnor residues

For a finite field `F`, the projective-line Milnor residue sequence in degrees two and one admits
a faithful finite-layer realization in `ℚ/ℤ`.  Its all-place obstruction is surjective onto the
finite subgroup realized by `K₁ᴹ(F)`, and a finite-and-infinite local profile is globally realized
exactly when the product of its local phases is one.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open Polynomial

noncomputable section

variable {F : Type*} [Field F] [Finite F]

local instance milnorPolynomialRatModIntHasseDecidableEqMonicIrred :
    DecidableEq (MonicIrred F) := Classical.decEq _

local instance milnorPolynomialRatModIntHasseDecidableEqResidue (q : MonicIrred F) :
    DecidableEq (MilnorKDeg (polyResidueField q.2.1) 1) := Classical.decEq _

/-- The all-place Bass--Tate sum, embedded faithfully in `ℚ/ℤ`. -/
noncomputable def milnorPolynomialKOneGlobalRatModIntSumAddHom :
    MilnorPolynomialTotalResidueTarget (F := F) 1 × MilnorKDeg F 1 →+ RatModInt :=
  (finiteMilnorKOneStdRatModIntInvariant F).comp
    (milnorPolynomialGlobalSum (F := F) 1)

/-- The `ℚ/ℤ` all-place sum is exact after the global `K₂ᴹ(F(t))` residue map. -/
theorem milnorPolynomialKTwoAllResidue_globalRatModIntSum_exact :
    Function.Exact (milnorPolynomialAllResidue (F := F) 1)
      (milnorPolynomialKOneGlobalRatModIntSumAddHom (F := F)) := by
  rw [AddMonoidHom.exact_iff]
  rw [milnorPolynomialAllResidue_range_eq_globalSum_ker]
  ext z
  change finiteMilnorKOneStdRatModIntInvariant F
      (milnorPolynomialGlobalSum (F := F) 1 z) = 0 ↔
    milnorPolynomialGlobalSum (F := F) 1 z = 0
  exact finiteMilnorKOneStdRatModIntInvariant_eq_zero_iff F _

/-- Restrict the all-place invariant to the finite subgroup of `ℚ/ℤ` actually realized by
`K₁ᴹ(F)`. -/
noncomputable def milnorPolynomialKOneGlobalRatModIntSumToRange :
    MilnorPolynomialTotalResidueTarget (F := F) 1 × MilnorKDeg F 1 →+
      (finiteMilnorKOneStdRatModIntInvariant F).range :=
  (milnorPolynomialKOneGlobalRatModIntSumAddHom (F := F)).codRestrict _ (by
    intro z
    exact ⟨milnorPolynomialGlobalSum (F := F) 1 z, rfl⟩)

/-- The realized finite `ℚ/ℤ` invariant is globally surjective through the infinity place. -/
theorem milnorPolynomialKOneGlobalRatModIntSumToRange_surjective :
    Function.Surjective (milnorPolynomialKOneGlobalRatModIntSumToRange (F := F)) := by
  intro r
  obtain ⟨x, hx⟩ := r.property
  obtain ⟨z, hz⟩ := milnorPolynomialGlobalSum_surjective (F := F) 1 x
  refine ⟨z, Subtype.ext ?_⟩
  change finiteMilnorKOneStdRatModIntInvariant F
    (milnorPolynomialGlobalSum (F := F) 1 z) = r.1
  rw [hz]
  exact hx

/-- The global residue map and realized finite invariant form an exact pair. -/
theorem milnorPolynomialKTwoAllResidue_globalRatModIntSumToRange_exact :
    Function.Exact (milnorPolynomialAllResidue (F := F) 1)
      (milnorPolynomialKOneGlobalRatModIntSumToRange (F := F)) := by
  intro z
  constructor
  · intro hz
    apply (milnorPolynomialKTwoAllResidue_globalRatModIntSum_exact (F := F) z).mp
    exact congrArg Subtype.val hz
  · intro hz
    apply Subtype.ext
    exact (milnorPolynomialKTwoAllResidue_globalRatModIntSum_exact (F := F) z).mpr hz

/-- `ℚ/ℤ`-valued projective-line Hasse exact sequence in Milnor degrees two and one. -/
theorem milnorPolynomialKTwoRatModIntProjectiveLine_exact :
    Function.Injective (milnorKDegMap (ratFuncConstHom (F := F)) 2) ∧
      Function.Exact (milnorKDegMap (ratFuncConstHom (F := F)) 2)
        (milnorPolynomialAllResidue (F := F) 1) ∧
      Function.Exact (milnorPolynomialAllResidue (F := F) 1)
        (milnorPolynomialKOneGlobalRatModIntSumToRange (F := F)) ∧
      Function.Surjective (milnorPolynomialKOneGlobalRatModIntSumToRange (F := F)) := by
  exact ⟨milnorKDegMap_ratFuncConstHom_injective 2,
    milnorPolynomialConst_allResidue_exact (F := F) 1,
    milnorPolynomialKTwoAllResidue_globalRatModIntSumToRange_exact (F := F),
    milnorPolynomialKOneGlobalRatModIntSumToRange_surjective (F := F)⟩

/-- Local profiles modulo globally realized residues equal the finite subgroup of `ℚ/ℤ` detected
by the all-place obstruction. -/
noncomputable def milnorPolynomialKOneLocalProfileQuotientEquivRatModIntRange :
    (MilnorPolynomialTotalResidueTarget (F := F) 1 × MilnorKDeg F 1) ⧸
        (milnorPolynomialAllResidue (F := F) 1).range ≃+
      (finiteMilnorKOneStdRatModIntInvariant F).range := by
  have hker : (milnorPolynomialKOneGlobalRatModIntSumToRange (F := F)).ker =
      (milnorPolynomialAllResidue (F := F) 1).range := by
    have hexact :=
      milnorPolynomialKTwoAllResidue_globalRatModIntSumToRange_exact (F := F)
    rw [AddMonoidHom.exact_iff] at hexact
    exact hexact
  exact (QuotientAddGroup.quotientAddEquivOfEq hker.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      (milnorPolynomialKOneGlobalRatModIntSumToRange (F := F))
      (milnorPolynomialKOneGlobalRatModIntSumToRange_surjective (F := F)))

/-- Canonical circle character measuring the obstruction for arbitrary all-place local data. -/
noncomputable def milnorPolynomialKOneAllPlaceStdAddChar :
    AddChar (MilnorPolynomialTotalResidueTarget (F := F) 1 × MilnorKDeg F 1) ℂ :=
  ratModIntStdAddChar.compAddMonoidHom
    (milnorPolynomialKOneGlobalRatModIntSumAddHom (F := F))

/-- The all-place obstruction character is the product of finite norm phases and the infinity
phase. -/
theorem milnorPolynomialKOneAllPlaceStdAddChar_eq_product
    (z : MilnorPolynomialTotalResidueTarget (F := F) 1 × MilnorKDeg F 1) :
    milnorPolynomialKOneAllPlaceStdAddChar (F := F) z =
      z.1.prod (fun q x => ratModIntStdAddChar
        (milnorPolynomialKOneNormRatModIntInvariantAt (F := F) q x)) *
      ratModIntStdAddChar (finiteMilnorKOneStdRatModIntInvariant F z.2) := by
  rw [← heterogeneousRatModIntProfileStdAddChar_eq_dfinsupp_prod]
  change ratModIntStdAddChar
      (finiteMilnorKOneStdRatModIntInvariant F
        (milnorPolynomialGlobalSum (F := F) 1 z)) =
    ratModIntStdAddChar
        (milnorPolynomialKOneNormRatModIntInvariantSumAddHom (F := F) z.1) *
      ratModIntStdAddChar (finiteMilnorKOneStdRatModIntInvariant F z.2)
  rw [milnorPolynomialKOneNormRatModIntInvariantSumAddHom_eq]
  change ratModIntStdAddChar
      (finiteMilnorKOneStdRatModIntInvariant F
        (milnorPolynomialTotalNorm (F := F) 1 z.1 + z.2)) = _
  rw [map_add, ratModIntStdAddChar.map_add_eq_mul]
  rfl

/-- Hasse realization criterion: arbitrary finite-and-infinite local data come from one global
`K₂ᴹ(F(t))` class exactly when their local phases satisfy product-one reciprocity. -/
theorem milnorPolynomialKTwo_localProfile_mem_globalRange_iff_character_product_one
    (z : MilnorPolynomialTotalResidueTarget (F := F) 1 × MilnorKDeg F 1) :
    z ∈ (milnorPolynomialAllResidue (F := F) 1).range ↔
      z.1.prod (fun q x => ratModIntStdAddChar
        (milnorPolynomialKOneNormRatModIntInvariantAt (F := F) q x)) *
      ratModIntStdAddChar (finiteMilnorKOneStdRatModIntInvariant F z.2) = 1 := by
  rw [milnorPolynomialAllResidue_range_eq_globalSum_ker]
  change milnorPolynomialGlobalSum (F := F) 1 z = 0 ↔ _
  rw [← milnorPolynomialKOneAllPlaceStdAddChar_eq_product]
  change milnorPolynomialGlobalSum (F := F) 1 z = 0 ↔
    ratModIntStdAddChar
      (finiteMilnorKOneStdRatModIntInvariant F
        (milnorPolynomialGlobalSum (F := F) 1 z)) = 1
  rw [ratModIntStdAddChar_eq_one_iff_eq_zero,
    finiteMilnorKOneStdRatModIntInvariant_eq_zero_iff]

end

end GaloisForLFunctions.HTGeometry.ABHN
