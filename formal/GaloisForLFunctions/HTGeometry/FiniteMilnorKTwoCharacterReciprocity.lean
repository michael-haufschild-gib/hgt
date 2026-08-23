/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.MilnorPolynomialCharacterReciprocity
import GaloisForLFunctions.HTGeometry.ABHN.RatModIntCircleCharacter
import GaloisForLFunctions.HTGeometry.ABHN.TameMilnorInvariant

/-!
# Canonical finite-field character form of projective-line `K₂` reciprocity

For a finite constant field `F`, the already formalized cyclic group `K₁ᴹ(F)` has a canonical
faithful circle character through `ℚ/ℤ`.  Applying it to the proven degree-two projective-line
Milnor reciprocity law yields an exact finite-place test: the product of finite norm phases is
one precisely when the obligatory residue at infinity vanishes.

This is a closed Hasse-reciprocity statement for Milnor `K₂`; it makes no norm-residue or
Milnor--Brauer identification.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {F : Type*} [Field F] [Finite F]

local instance finiteMilnorKTwoCharacterDecidableEqMonicIrred : DecidableEq (MonicIrred F) :=
  Classical.decEq _

local instance finiteMilnorKTwoCharacterDecidableEqResidueMilnorKDeg
    (q : MonicIrred F) (n : ℕ) :
    DecidableEq (MilnorKDeg (polyResidueField q.2.1) n) := Classical.decEq _

/-- The canonical faithful circle character of the finite cyclic group `K₁ᴹ(F)`. -/
noncomputable def finiteMilnorKOneStdAddChar (F : Type*) [Field F] [Finite F] :
    AddChar (MilnorKDeg F 1) ℂ :=
  ABHN.ratModIntStdAddChar.compAddMonoidHom
    (ABHN.finiteAddCyclicRatModIntAddHom _ (finiteMilnorKDegOne_isAddCyclic F))

/-- The canonical finite-field `K₁ᴹ` phase detects its class faithfully. -/
theorem finiteMilnorKOneStdAddChar_injective (F : Type*) [Field F] [Finite F] :
    Function.Injective (finiteMilnorKOneStdAddChar F) := by
  exact ABHN.ratModIntStdAddChar_injective.comp
    (ABHN.finiteAddCyclicRatModIntAddHom_injective _ (finiteMilnorKDegOne_isAddCyclic F))

/-- The canonical finite-field `K₁ᴹ` phase is one exactly at the trivial class. -/
theorem finiteMilnorKOneStdAddChar_eq_one_iff_eq_zero
    (F : Type*) [Field F] [Finite F] (x : MilnorKDeg F 1) :
    finiteMilnorKOneStdAddChar F x = 1 ↔ x = 0 := by
  constructor
  · intro hx
    apply finiteMilnorKOneStdAddChar_injective F
    rw [hx]
    exact (finiteMilnorKOneStdAddChar F).map_zero_eq_one.symm
  · intro hx
    rw [hx]
    exact (finiteMilnorKOneStdAddChar F).map_zero_eq_one

/-- **Finite-field character Hasse test for `K₂ᴹ(F(t))`.** The product of the canonical
characters of all finite norm residues equals one exactly when the residue at infinity is zero.
Thus finite local data have no residual global obstruction precisely when their forced infinity
correction vanishes. -/
theorem milnorPolynomialKTwo_finiteCharacter_product_eq_one_iff_residueInfty_eq_zero
    (y : MilnorKDeg (RatFunc F) 2) :
    (milnorPolynomialTotalResidue (F := F) 1 y).prod
        (fun q x ↦ finiteMilnorKOneStdAddChar F (milnorNormAt q 1 x)) = 1 ↔
      milnorResidueInfty 1 y = 0 := by
  constructor
  · intro hfinite
    have hproduct := milnorPolynomialTotalResidue_character_product_one (F := F) 1
      (finiteMilnorKOneStdAddChar F) y
    rw [hfinite, one_mul] at hproduct
    exact (finiteMilnorKOneStdAddChar_eq_one_iff_eq_zero F _).mp hproduct
  · intro hinfty
    have hproduct := milnorPolynomialTotalResidue_character_product_one (F := F) 1
      (finiteMilnorKOneStdAddChar F) y
    rw [hinfty, (finiteMilnorKOneStdAddChar F).map_zero_eq_one, mul_one] at hproduct
    exact hproduct

end

end GaloisForLFunctions.HTGeometry
