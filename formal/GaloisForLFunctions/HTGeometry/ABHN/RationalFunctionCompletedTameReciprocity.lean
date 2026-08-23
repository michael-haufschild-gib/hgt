/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.RationalFunctionAdicNormTameRatModIntInvariant
import GaloisForLFunctions.HTGeometry.DFinsuppAddMonoidHomSum

/-!
# Projective-line reciprocity through completed local tame phases

Surjectivity of the concrete adic tame residue gives a local `K₂ᴹ` representative for every
global finite-place residue class.  The norm-normalized phase of that representative is exactly the
finite term in projective-line reciprocity.  Therefore the existing global theorem can be restated
as a literal product formula over completed local fields.

This is a closed tame-Milnor Hasse principle:

* finite completed local phases multiply to one exactly when the infinity residue vanishes;
* every finite residue profile has a unique global class after adjoining its forced infinity term,
  and its completed-local phases satisfy reciprocity.

The local section is choice-dependent, but its phase is not: the phase factors through the specified
residue class.  No Milnor--Brauer comparison is asserted.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open IsDedekindDomain
open scoped Polynomial WithZero WithZeroMulInt

universe u

noncomputable section

local instance completedGlobalReciprocityDecidableEqMonicIrred
    {F : Type*} [Field F] : DecidableEq (MonicIrred F) := Classical.decEq _

local instance completedGlobalReciprocityDecidableEqResidueMilnorKDeg
    {F : Type*} [Field F] (q : MonicIrred F) (n : ℕ) :
    DecidableEq (MilnorKDeg (polyResidueField q.2.1) n) := Classical.decEq _

/-- Choose a completed local `K₂ᴹ` class having the transported prescribed tame residue. -/
noncomputable def rationalFunctionFiniteAdicTameResidueSection
    (F : Type u) [Field F] [Finite F] (q : MonicIrred F) :
    MilnorKDeg (polyResidueField q.2.1) 1 →
      MilnorKDeg ((polyPlace q.2.1).adicCompletion (RatFunc F)) 2 :=
  fun x ↦ Classical.choose
    (rationalFunctionFiniteAdicTameMilnorResidue_surjective F (polyPlace q.2.1)
      (rationalFunctionAdicCompletion_valuationResidueMilnorKDegAddEquiv
        F (polyPlace q.2.1) 1 x))

/-- The chosen completed local class has exactly the transported prescribed tame residue. -/
theorem rationalFunctionFiniteAdicTameResidueSection_spec
    (F : Type u) [Field F] [Finite F] (q : MonicIrred F)
    (x : MilnorKDeg (polyResidueField q.2.1) 1) :
    rationalFunctionFiniteAdicTameMilnorResidue F (polyPlace q.2.1)
        (rationalFunctionFiniteAdicTameResidueSection F q x) =
      rationalFunctionAdicCompletion_valuationResidueMilnorKDegAddEquiv
        F (polyPlace q.2.1) 1 x :=
  Classical.choose_spec
    (rationalFunctionFiniteAdicTameMilnorResidue_surjective F (polyPlace q.2.1)
      (rationalFunctionAdicCompletion_valuationResidueMilnorKDegAddEquiv
        F (polyPlace q.2.1) 1 x))

/-- The completed local phase of the section is the global finite norm phase. -/
theorem rationalFunctionFiniteAdicNormTameStdAddChar_section
    (F : Type u) [Field F] [Finite F] (q : MonicIrred F)
    (x : MilnorKDeg (polyResidueField q.2.1) 1) :
    rationalFunctionFiniteAdicNormTameStdAddChar F q
        (rationalFunctionFiniteAdicTameResidueSection F q x) =
      finiteMilnorKOneStdAddChar F (milnorNormAt q 1 x) := by
  rw [rationalFunctionFiniteAdicNormTameStdAddChar_apply,
    rationalFunctionFiniteAdicTameResidueSection_spec,
    AddEquiv.symm_apply_apply]

/-- The completed local additive invariant of the section is exactly the Bass--Tate norm of the
prescribed global-place residue. -/
theorem rationalFunctionFiniteAdicNormTameMilnorInvariant_section
    (F : Type u) [Field F] [Finite F] (q : MonicIrred F)
    (x : MilnorKDeg (polyResidueField q.2.1) 1) :
    rationalFunctionFiniteAdicNormTameMilnorInvariant F q
        (rationalFunctionFiniteAdicTameResidueSection F q x) =
      milnorNormAt q 1 x := by
  change milnorNormAt q 1
    ((rationalFunctionAdicCompletion_valuationResidueMilnorKDegAddEquiv
      F (polyPlace q.2.1) 1).symm
        (rationalFunctionFiniteAdicTameMilnorResidue F (polyPlace q.2.1)
          (rationalFunctionFiniteAdicTameResidueSection F q x))) = _
  rw [rationalFunctionFiniteAdicTameResidueSection_spec,
    AddEquiv.symm_apply_apply]

/-- The completed local `ℚ/ℤ` invariant of the section is the finite-field invariant of the
Bass--Tate norm. -/
theorem rationalFunctionFiniteAdicNormTameRatModIntInvariant_section
    (F : Type u) [Field F] [Finite F] (q : MonicIrred F)
    (x : MilnorKDeg (polyResidueField q.2.1) 1) :
    rationalFunctionFiniteAdicNormTameRatModIntInvariant F q
        (rationalFunctionFiniteAdicTameResidueSection F q x) =
      finiteMilnorKOneStdRatModIntInvariant F (milnorNormAt q 1 x) := by
  change finiteMilnorKOneStdRatModIntInvariant F
      (rationalFunctionFiniteAdicNormTameMilnorInvariant F q
        (rationalFunctionFiniteAdicTameResidueSection F q x)) = _
  rw [rationalFunctionFiniteAdicNormTameMilnorInvariant_section]

/-- **Additive completed-local reciprocity.**  The sum of the norm-tame invariants of completed
local representatives cancels the residue at infinity.  This has the exact additive shape of the
ABHN invariant-sum law, with `K₁ᴹ(F)` in place of `ℚ/ℤ`. -/
theorem milnorPolynomialKTwo_completedFiniteTameInvariant_sum_add_residueInfty_eq_zero
    (F : Type u) [Field F] [Finite F] (y : MilnorKDeg (RatFunc F) 2) :
    (milnorPolynomialTotalResidue (F := F) 1 y).sum
        (fun q x ↦ rationalFunctionFiniteAdicNormTameMilnorInvariant F q
          (rationalFunctionFiniteAdicTameResidueSection F q x)) +
      milnorResidueInfty 1 y = 0 := by
  have h := milnorPolynomialTotalResidue_reciprocity (F := F) 1 y
  change (milnorPolynomialTotalResidue (F := F) 1 y).sum
      (fun q x ↦ milnorNormAt q 1 x) + milnorResidueInfty 1 y = 0 at h
  simpa only [rationalFunctionFiniteAdicNormTameMilnorInvariant_section] using h

/-- **`ℚ/ℤ`-valued completed-local reciprocity.**  Completed finite-place norm-tame invariants and
the infinity invariant sum to zero in the ABHN target. -/
theorem milnorPolynomialKTwo_completedFiniteTameRatModIntInvariant_sum_eq_zero
    (F : Type u) [Field F] [Finite F] (y : MilnorKDeg (RatFunc F) 2) :
    (milnorPolynomialTotalResidue (F := F) 1 y).sum
        (fun q x ↦ rationalFunctionFiniteAdicNormTameRatModIntInvariant F q
          (rationalFunctionFiniteAdicTameResidueSection F q x)) +
      finiteMilnorKOneStdRatModIntInvariant F (milnorResidueInfty 1 y) = 0 := by
  have hK := milnorPolynomialTotalResidue_reciprocity (F := F) 1 y
  change (milnorPolynomialTotalResidue (F := F) 1 y).sum
      (fun q x ↦ milnorNormAt q 1 x) + milnorResidueInfty 1 y = 0 at hK
  have h := congrArg (finiteMilnorKOneStdRatModIntInvariant F) hK
  rw [map_zero, map_add] at h
  rw [addMonoidHom_map_dfinsupp_sum
    (fun q ↦ milnorNormAt q 1) (finiteMilnorKOneStdRatModIntInvariant F)] at h
  simpa only [rationalFunctionFiniteAdicNormTameRatModIntInvariant_section] using h

/-- **Completed-local tame character Hasse test for `K₂ᴹ(F(t))`.**  The product of phases of
completed local representatives is one exactly when the residue at infinity is zero. -/
theorem milnorPolynomialKTwo_completedFiniteTameCharacter_product_eq_one_iff_residueInfty_eq_zero
    (F : Type u) [Field F] [Finite F] (y : MilnorKDeg (RatFunc F) 2) :
    (milnorPolynomialTotalResidue (F := F) 1 y).prod
        (fun q x ↦ rationalFunctionFiniteAdicNormTameStdAddChar F q
          (rationalFunctionFiniteAdicTameResidueSection F q x)) = 1 ↔
      milnorResidueInfty 1 y = 0 := by
  simpa only [rationalFunctionFiniteAdicNormTameStdAddChar_section] using
    milnorPolynomialKTwo_finiteCharacter_product_eq_one_iff_residueInfty_eq_zero
      (F := F) y

/-- **Completed-local tame reciprocity and realization.**  Every prescribed finite residue profile
has a unique global `K₂ᴹ(F(t))` realization after adjoining its forced infinity residue, and the
completed-local phases of that class obey the global product formula. -/
theorem finiteField_milnorKTwo_existsUnique_with_completedFiniteTameCharacter_product
    (F : Type u) [Field F] [Finite F]
    (z : MilnorPolynomialTotalResidueTarget (F := F) 1) :
    ∃! y : MilnorKDeg (RatFunc F) 2,
      milnorPolynomialAllResidue (F := F) 1 y =
        (z, -milnorPolynomialTotalNorm (F := F) 1 z) ∧
      (milnorPolynomialTotalResidue (F := F) 1 y).prod
          (fun q x ↦ rationalFunctionFiniteAdicNormTameStdAddChar F q
            (rationalFunctionFiniteAdicTameResidueSection F q x)) *
        finiteMilnorKOneStdAddChar F (milnorResidueInfty 1 y) = 1 := by
  simpa only [rationalFunctionFiniteAdicNormTameStdAddChar_section] using
    finiteField_milnorKTwo_existsUnique_with_finiteResidues_character_product
      (F := F) z

/-- **Additive completed-local realization.**  Every finite residue profile has a unique global
class with its forced infinity residue, and the sum of its completed local norm-tame invariants
cancels that infinity term. -/
theorem finiteField_milnorKTwo_existsUnique_with_completedFiniteTameInvariant_sum
    (F : Type u) [Field F] [Finite F]
    (z : MilnorPolynomialTotalResidueTarget (F := F) 1) :
    ∃! y : MilnorKDeg (RatFunc F) 2,
      milnorPolynomialAllResidue (F := F) 1 y =
        (z, -milnorPolynomialTotalNorm (F := F) 1 z) ∧
      (milnorPolynomialTotalResidue (F := F) 1 y).sum
          (fun q x ↦ rationalFunctionFiniteAdicNormTameMilnorInvariant F q
            (rationalFunctionFiniteAdicTameResidueSection F q x)) +
        milnorResidueInfty 1 y = 0 := by
  obtain ⟨y, hy, hyuniq⟩ :=
    finiteField_rationalFunctionMilnorKTwo_existsUnique_with_finiteResidues (F := F) z
  refine ⟨y, ⟨hy, ?_⟩, ?_⟩
  · exact milnorPolynomialKTwo_completedFiniteTameInvariant_sum_add_residueInfty_eq_zero F y
  · intro y' hy'
    exact hyuniq y' hy'.1

/-- **`ℚ/ℤ`-valued completed-local realization.**  Every finite residue profile has a unique
global realization with its forced infinity residue, and its completed local invariants satisfy
the ABHN-shaped additive reciprocity law. -/
theorem finiteField_milnorKTwo_existsUnique_with_completedFiniteTameRatModIntInvariant_sum
    (F : Type u) [Field F] [Finite F]
    (z : MilnorPolynomialTotalResidueTarget (F := F) 1) :
    ∃! y : MilnorKDeg (RatFunc F) 2,
      milnorPolynomialAllResidue (F := F) 1 y =
        (z, -milnorPolynomialTotalNorm (F := F) 1 z) ∧
      (milnorPolynomialTotalResidue (F := F) 1 y).sum
          (fun q x ↦ rationalFunctionFiniteAdicNormTameRatModIntInvariant F q
            (rationalFunctionFiniteAdicTameResidueSection F q x)) +
        finiteMilnorKOneStdRatModIntInvariant F (milnorResidueInfty 1 y) = 0 := by
  obtain ⟨y, hy, hyuniq⟩ :=
    finiteField_rationalFunctionMilnorKTwo_existsUnique_with_finiteResidues (F := F) z
  refine ⟨y, ⟨hy, ?_⟩, ?_⟩
  · exact milnorPolynomialKTwo_completedFiniteTameRatModIntInvariant_sum_eq_zero F y
  · intro y' hy'
    exact hyuniq y' hy'.1

end

end GaloisForLFunctions.HTGeometry.ABHN
