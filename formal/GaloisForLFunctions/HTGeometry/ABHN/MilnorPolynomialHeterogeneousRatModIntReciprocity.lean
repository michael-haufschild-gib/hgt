/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HeterogeneousRatModIntReciprocity
import GaloisForLFunctions.HTGeometry.FiniteMilnorKOneRatModIntInvariant
import GaloisForLFunctions.HTGeometry.MilnorPolynomialGlobalReciprocity

/-!
# Heterogeneous Q/Z reciprocity for polynomial Milnor residues

Finite places of `F(t)` have different residue fields.  Each degree-one residue is first carried
by its Bass--Tate norm to `K₁ᴹ(F)`, then by the faithful finite-field invariant to `ℚ/ℤ`.
The resulting dependent finite-support profile has an exact zero-sum kernel.  For every global
`K₂ᴹ(F(t))` class, its finite invariant sum cancels the infinity invariant, both additively and as
a product of circle phases.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open Polynomial

noncomputable section

variable {F : Type*} [Field F] [Finite F]

local instance milnorPolynomialNormRatModIntDecidableEqMonicIrred :
    DecidableEq (MonicIrred F) := Classical.decEq _

local instance milnorPolynomialNormRatModIntDecidableEqResidue (q : MonicIrred F) :
    DecidableEq (MilnorKDeg (polyResidueField q.2.1) 1) := Classical.decEq _

/-- Norm-weighted `ℚ/ℤ` invariant at one polynomial place. -/
noncomputable def milnorPolynomialKOneNormRatModIntInvariantAt (q : MonicIrred F) :
    MilnorKDeg (polyResidueField q.2.1) 1 →+ RatModInt :=
  (finiteMilnorKOneStdRatModIntInvariant F).comp (milnorNormAt q 1)

/-- Sum all norm-weighted finite-place `K₁ᴹ` invariants in `ℚ/ℤ`. -/
noncomputable def milnorPolynomialKOneNormRatModIntInvariantSumAddHom :
    MilnorPolynomialTotalResidueTarget (F := F) 1 →+ RatModInt :=
  heterogeneousRatModIntProfileInvariantSumAddHom
    (fun q : MonicIrred F => MilnorKDeg (polyResidueField q.2.1) 1)
    (milnorPolynomialKOneNormRatModIntInvariantAt (F := F))

/-- Heterogeneous finite-place summation is the finite-field invariant after the Bass--Tate total
norm. -/
theorem milnorPolynomialKOneNormRatModIntInvariantSumAddHom_eq :
    milnorPolynomialKOneNormRatModIntInvariantSumAddHom (F := F) =
      (finiteMilnorKOneStdRatModIntInvariant F).comp
        (milnorPolynomialTotalNorm (F := F) 1) := by
  apply AddMonoidHom.ext
  intro z
  rw [milnorPolynomialKOneNormRatModIntInvariantSumAddHom,
    heterogeneousRatModIntProfileInvariantSumAddHom, DFinsupp.sumAddHom_apply]
  change z.sum (fun q x => finiteMilnorKOneStdRatModIntInvariant F (milnorNormAt q 1 x)) =
    finiteMilnorKOneStdRatModIntInvariant F
      (milnorPolynomialTotalNorm (F := F) 1 z)
  change z.sum (fun q x => finiteMilnorKOneStdRatModIntInvariant F (milnorNormAt q 1 x)) =
    finiteMilnorKOneStdRatModIntInvariant F (z.sum fun q x => milnorNormAt q 1 x)
  exact (addMonoidHom_map_dfinsupp_sum
    (fun q => milnorNormAt q 1) (finiteMilnorKOneStdRatModIntInvariant F) z).symm

/-- Finite-place norm phases multiply to one exactly when their `ℚ/ℤ` sum vanishes. -/
theorem milnorPolynomialKOneNormRatModIntProfile_product_eq_one_iff_sum_eq_zero
    (z : MilnorPolynomialTotalResidueTarget (F := F) 1) :
    z.prod (fun q x => ratModIntStdAddChar
        (milnorPolynomialKOneNormRatModIntInvariantAt (F := F) q x)) = 1 ↔
      milnorPolynomialKOneNormRatModIntInvariantSumAddHom (F := F) z = 0 :=
  heterogeneousRatModIntProfile_product_eq_one_iff_sum_eq_zero
    (fun q : MonicIrred F => MilnorKDeg (polyResidueField q.2.1) 1)
    (milnorPolynomialKOneNormRatModIntInvariantAt (F := F)) z

/-- Polynomial-place norm reciprocity is exact at the finite local-profile term. -/
theorem milnorPolynomialKOneNormRatModIntInvariantSum_exact :
    Function.Exact
      (milnorPolynomialKOneNormRatModIntInvariantSumAddHom (F := F)).ker.subtype
      (milnorPolynomialKOneNormRatModIntInvariantSumAddHom (F := F)) :=
  heterogeneousRatModIntProfileInvariantSum_exact
    (fun q : MonicIrred F => MilnorKDeg (polyResidueField q.2.1) 1)
    (milnorPolynomialKOneNormRatModIntInvariantAt (F := F))

/-- Polynomial-place profiles modulo reciprocity recover their realized subgroup of `ℚ/ℤ`. -/
noncomputable def milnorPolynomialKOneNormRatModIntInvariantSumQuotientEquivRange :
    MilnorPolynomialTotalResidueTarget (F := F) 1 ⧸
        (milnorPolynomialKOneNormRatModIntInvariantSumAddHom (F := F)).ker ≃+
      (milnorPolynomialKOneNormRatModIntInvariantSumAddHom (F := F)).range :=
  heterogeneousRatModIntProfileInvariantSumQuotientEquivRange
    (fun q : MonicIrred F => MilnorKDeg (polyResidueField q.2.1) 1)
    (milnorPolynomialKOneNormRatModIntInvariantAt (F := F))

/-- Additive all-place reciprocity for `K₂ᴹ(F(t))` in the ABHN target `ℚ/ℤ`. -/
theorem milnorPolynomialKTwo_normRatModIntInvariant_sum_add_infty_eq_zero
    (y : MilnorKDeg (RatFunc F) 2) :
    milnorPolynomialKOneNormRatModIntInvariantSumAddHom (F := F)
        (milnorPolynomialTotalResidue (F := F) 1 y) +
      finiteMilnorKOneStdRatModIntInvariant F (milnorResidueInfty 1 y) = 0 := by
  rw [milnorPolynomialKOneNormRatModIntInvariantSumAddHom_eq]
  change finiteMilnorKOneStdRatModIntInvariant F
      (milnorPolynomialTotalNorm (F := F) 1
        (milnorPolynomialTotalResidue (F := F) 1 y)) +
    finiteMilnorKOneStdRatModIntInvariant F (milnorResidueInfty 1 y) = 0
  rw [← map_add, milnorPolynomialTotalResidue_reciprocity, map_zero]

/-- Character form of all-place polynomial Milnor reciprocity in `ℚ/ℤ`: finite norm phases and
the infinity phase multiply to one. -/
theorem milnorPolynomialKTwo_normRatModIntInvariant_character_product_one
    (y : MilnorKDeg (RatFunc F) 2) :
    (milnorPolynomialTotalResidue (F := F) 1 y).prod
        (fun q x => ratModIntStdAddChar
          (milnorPolynomialKOneNormRatModIntInvariantAt (F := F) q x)) *
      ratModIntStdAddChar
        (finiteMilnorKOneStdRatModIntInvariant F (milnorResidueInfty 1 y)) = 1 := by
  rw [← heterogeneousRatModIntProfileStdAddChar_eq_dfinsupp_prod]
  change ratModIntStdAddChar
      (milnorPolynomialKOneNormRatModIntInvariantSumAddHom (F := F)
        (milnorPolynomialTotalResidue (F := F) 1 y)) *
    ratModIntStdAddChar
      (finiteMilnorKOneStdRatModIntInvariant F (milnorResidueInfty 1 y)) = 1
  rw [← ratModIntStdAddChar.map_add_eq_mul,
    milnorPolynomialKTwo_normRatModIntInvariant_sum_add_infty_eq_zero]
  exact ratModIntStdAddChar.map_zero_eq_one

end

end GaloisForLFunctions.HTGeometry.ABHN
