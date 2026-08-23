/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.MilnorPolynomialRatModIntHasseSequence
import GaloisForLFunctions.HTGeometry.ABHN.RationalFunctionCompletedTameHasseExactness

/-!
# A finite-layer ABHN sequence for completed tame local data

Actual completed finite-place tame quotients, together with the infinity coordinate, admit a
faithful finite-layer obstruction in `ℚ/ℤ`.  The sequence is exact and surjective onto the finite
subgroup realized by `K₁ᴹ(F)`.  An arbitrary completed local profile is globally realizable exactly
when its transported finite-place phases and infinity phase multiply to one.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open IsDedekindDomain
open scoped Polynomial WithZero WithZeroMulInt

universe u

noncomputable section

local instance completedTameRatModIntHasseDecidableEqMonicIrred
    {F : Type*} [Field F] : DecidableEq (MonicIrred F) := Classical.decEq _

local instance completedTameRatModIntHasseDecidableEqResidue
    {F : Type*} [Field F] (q : MonicIrred F) :
    DecidableEq (MilnorKDeg (polyResidueField q.2.1) 1) := Classical.decEq _

/-- Completed all-place tame sum embedded faithfully in `ℚ/ℤ`. -/
noncomputable def rationalFunctionCompletedTameGlobalRatModIntSumAddHom
    (F : Type u) [Field F] [Finite F] :
    RationalFunctionCompletedTameAllLocalData F →+ RatModInt :=
  (finiteMilnorKOneStdRatModIntInvariant F).comp
    (rationalFunctionCompletedTameGlobalSum F)

/-- Actual completed tame residues are exact with the `ℚ/ℤ` all-place obstruction. -/
theorem rationalFunctionCompletedTameAllResidue_globalRatModIntSum_exact
    (F : Type u) [Field F] [Finite F] :
    Function.Exact (rationalFunctionCompletedTameAllResidue F)
      (rationalFunctionCompletedTameGlobalRatModIntSumAddHom F) := by
  rw [AddMonoidHom.exact_iff]
  rw [rationalFunctionCompletedTameAllResidue_range_eq_globalSum_ker]
  ext z
  change finiteMilnorKOneStdRatModIntInvariant F
      (rationalFunctionCompletedTameGlobalSum F z) = 0 ↔
    rationalFunctionCompletedTameGlobalSum F z = 0
  exact finiteMilnorKOneStdRatModIntInvariant_eq_zero_iff F _

/-- Restrict the completed all-place obstruction to its realized finite subgroup of `ℚ/ℤ`. -/
noncomputable def rationalFunctionCompletedTameGlobalRatModIntSumToRange
    (F : Type u) [Field F] [Finite F] :
    RationalFunctionCompletedTameAllLocalData F →+
      (finiteMilnorKOneStdRatModIntInvariant F).range :=
  (rationalFunctionCompletedTameGlobalRatModIntSumAddHom F).codRestrict _ (by
    intro z
    exact ⟨rationalFunctionCompletedTameGlobalSum F z, rfl⟩)

/-- Every realized finite `ℚ/ℤ` obstruction occurs on completed local tame data. -/
theorem rationalFunctionCompletedTameGlobalRatModIntSumToRange_surjective
    (F : Type u) [Field F] [Finite F] :
    Function.Surjective (rationalFunctionCompletedTameGlobalRatModIntSumToRange F) := by
  intro r
  obtain ⟨x, hx⟩ := r.property
  obtain ⟨z, hz⟩ := rationalFunctionCompletedTameGlobalSum_surjective F x
  refine ⟨z, Subtype.ext ?_⟩
  change finiteMilnorKOneStdRatModIntInvariant F
    (rationalFunctionCompletedTameGlobalSum F z) = r.1
  rw [hz]
  exact hx

/-- Completed tame residues and the realized finite invariant form an exact pair. -/
theorem rationalFunctionCompletedTameAllResidue_globalRatModIntSumToRange_exact
    (F : Type u) [Field F] [Finite F] :
    Function.Exact (rationalFunctionCompletedTameAllResidue F)
      (rationalFunctionCompletedTameGlobalRatModIntSumToRange F) := by
  intro z
  constructor
  · intro hz
    apply (rationalFunctionCompletedTameAllResidue_globalRatModIntSum_exact F z).mp
    exact congrArg Subtype.val hz
  · intro hz
    apply Subtype.ext
    exact (rationalFunctionCompletedTameAllResidue_globalRatModIntSum_exact F z).mpr hz

/-- Finite-layer ABHN exact sequence with actual completed tame local terms. -/
theorem rationalFunctionCompletedTameRatModIntProjectiveLine_exact
    (F : Type u) [Field F] [Finite F] :
    Function.Injective (milnorKDegMap (ratFuncConstHom (F := F)) 2) ∧
      Function.Exact (milnorKDegMap (ratFuncConstHom (F := F)) 2)
        (rationalFunctionCompletedTameAllResidue F) ∧
      Function.Exact (rationalFunctionCompletedTameAllResidue F)
        (rationalFunctionCompletedTameGlobalRatModIntSumToRange F) ∧
      Function.Surjective
        (rationalFunctionCompletedTameGlobalRatModIntSumToRange F) := by
  exact ⟨milnorKDegMap_ratFuncConstHom_injective 2,
    (rationalFunctionCompletedTameProjectiveLine_exact F).2.1,
    rationalFunctionCompletedTameAllResidue_globalRatModIntSumToRange_exact F,
    rationalFunctionCompletedTameGlobalRatModIntSumToRange_surjective F⟩

/-- Completed local profiles modulo global residues equal the finite `ℚ/ℤ` obstruction group. -/
noncomputable def rationalFunctionCompletedTameLocalProfileQuotientEquivRatModIntRange
    (F : Type u) [Field F] [Finite F] :
    RationalFunctionCompletedTameAllLocalData F ⧸
        (rationalFunctionCompletedTameAllResidue F).range ≃+
      (finiteMilnorKOneStdRatModIntInvariant F).range := by
  have hker : (rationalFunctionCompletedTameGlobalRatModIntSumToRange F).ker =
      (rationalFunctionCompletedTameAllResidue F).range := by
    have hexact :=
      rationalFunctionCompletedTameAllResidue_globalRatModIntSumToRange_exact F
    rw [AddMonoidHom.exact_iff] at hexact
    exact hexact
  exact (QuotientAddGroup.quotientAddEquivOfEq hker.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      (rationalFunctionCompletedTameGlobalRatModIntSumToRange F)
      (rationalFunctionCompletedTameGlobalRatModIntSumToRange_surjective F))

/-- Circle character of the completed all-place obstruction. -/
noncomputable def rationalFunctionCompletedTameAllPlaceStdAddChar
    (F : Type u) [Field F] [Finite F] :
    AddChar (RationalFunctionCompletedTameAllLocalData F) ℂ :=
  ratModIntStdAddChar.compAddMonoidHom
    (rationalFunctionCompletedTameGlobalRatModIntSumAddHom F)

/-- The completed all-place obstruction character is the finite norm-phase product times the
infinity phase. -/
theorem rationalFunctionCompletedTameAllPlaceStdAddChar_eq_product
    (F : Type u) [Field F] [Finite F]
    (z : RationalFunctionCompletedTameAllLocalData F) :
    rationalFunctionCompletedTameAllPlaceStdAddChar F z =
      (rationalFunctionCompletedTameAllLocalDataEquiv F z).1.prod
          (fun q x => ratModIntStdAddChar
            (milnorPolynomialKOneNormRatModIntInvariantAt (F := F) q x)) *
        ratModIntStdAddChar (finiteMilnorKOneStdRatModIntInvariant F
          (rationalFunctionCompletedTameAllLocalDataEquiv F z).2) := by
  change milnorPolynomialKOneAllPlaceStdAddChar (F := F)
      (rationalFunctionCompletedTameAllLocalDataEquiv F z) = _
  exact milnorPolynomialKOneAllPlaceStdAddChar_eq_product (F := F)
    (rationalFunctionCompletedTameAllLocalDataEquiv F z)

/-- Completed-local Hasse criterion: arbitrary local tame data are globally realized exactly
when their transported finite phases and infinity phase multiply to one. -/
theorem rationalFunctionCompletedTame_localProfile_mem_globalRange_iff_character_product_one
    (F : Type u) [Field F] [Finite F]
    (z : RationalFunctionCompletedTameAllLocalData F) :
    z ∈ (rationalFunctionCompletedTameAllResidue F).range ↔
      (rationalFunctionCompletedTameAllLocalDataEquiv F z).1.prod
          (fun q x => ratModIntStdAddChar
            (milnorPolynomialKOneNormRatModIntInvariantAt (F := F) q x)) *
        ratModIntStdAddChar (finiteMilnorKOneStdRatModIntInvariant F
          (rationalFunctionCompletedTameAllLocalDataEquiv F z).2) = 1 := by
  rw [rationalFunctionCompletedTameAllResidue_range_eq_globalSum_ker]
  change rationalFunctionCompletedTameGlobalSum F z = 0 ↔ _
  rw [← rationalFunctionCompletedTameAllPlaceStdAddChar_eq_product]
  change rationalFunctionCompletedTameGlobalSum F z = 0 ↔
    ratModIntStdAddChar
      (finiteMilnorKOneStdRatModIntInvariant F
        (rationalFunctionCompletedTameGlobalSum F z)) = 1
  rw [ratModIntStdAddChar_eq_one_iff_eq_zero,
    finiteMilnorKOneStdRatModIntInvariant_eq_zero_iff]

end
end GaloisForLFunctions.HTGeometry.ABHN
