/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.MilnorPolynomialGlobalReciprocity
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Character form of Milnor polynomial reciprocity

The projective-line Milnor residue sequence has a literal all-place additive reciprocity law.
Pushing it through any complex additive character converts that law into a product-one relation:
the finite Bass--Tate norm character values, together with the character of the infinite residue,
multiply to one.

This is a genuine global-reciprocity instance that shares the multiplicative shape of ABHN.  It
does not supply the norm-residue comparison needed to identify it with Brauer invariants.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

variable {F : Type*} [Field F]

local instance milnorPolynomialCharacterReciprocityDecidableEqMonicIrred :
    DecidableEq (MonicIrred F) := Classical.decEq _

local instance milnorPolynomialCharacterReciprocityDecidableEqResidueMilnorKDeg
    (q : MonicIrred F) (n : ℕ) :
    DecidableEq (MilnorKDeg (polyResidueField q.2.1) n) := Classical.decEq _

/-- Apply a complex additive character after taking the finite Bass--Tate norm sum. -/
noncomputable def milnorPolynomialTotalNormAddChar (n : ℕ) (ψ : AddChar (MilnorKDeg F n) ℂ) :
    AddChar (MilnorPolynomialTotalResidueTarget (F := F) n) ℂ :=
  ψ.compAddMonoidHom (milnorPolynomialTotalNorm (F := F) n)

/-- The character of the finite norm sum is the product of the local norm character values. -/
theorem milnorPolynomialTotalNormAddChar_eq_dfinsupp_prod
    (n : ℕ) (ψ : AddChar (MilnorKDeg F n) ℂ)
    (z : MilnorPolynomialTotalResidueTarget (F := F) n) :
    milnorPolynomialTotalNormAddChar (F := F) n ψ z =
      z.prod fun q x ↦ ψ (milnorNormAt q n x) := by
  classical
  induction z using DFinsupp.induction with
  | h0 =>
      simp [milnorPolynomialTotalNormAddChar, milnorPolynomialTotalNorm, DFinsupp.prod]
  | @ha q b f hqzero hb hih =>
      rw [(milnorPolynomialTotalNormAddChar (F := F) n ψ).map_add_eq_mul,
        hih, DFinsupp.prod_add_index]
      · rw [milnorPolynomialTotalNormAddChar, AddChar.compAddMonoidHom_apply,
          milnorPolynomialTotalNorm_single, DFinsupp.prod_single_index]
        rw [(milnorNormAt q n).map_zero]
        exact ψ.map_zero_eq_one
      · intro q
        rw [(milnorNormAt q n).map_zero]
        exact ψ.map_zero_eq_one
      · intro q a b
        rw [(milnorNormAt q n).map_add]
        exact ψ.map_add_eq_mul ((milnorNormAt q n) a) ((milnorNormAt q n) b)

/-- The character form of projective-line reciprocity: finite norm character values times the
infinite residue character value equal one. -/
theorem milnorPolynomialTotalResidue_character_product_one
    (n : ℕ) (ψ : AddChar (MilnorKDeg F n) ℂ)
    (y : MilnorKDeg (RatFunc F) n.succ) :
    (milnorPolynomialTotalResidue (F := F) n y).prod
        (fun q x ↦ ψ (milnorNormAt q n x)) * ψ (milnorResidueInfty n y) = 1 := by
  rw [← milnorPolynomialTotalNormAddChar_eq_dfinsupp_prod]
  change ψ (milnorPolynomialTotalNorm (F := F) n
    (milnorPolynomialTotalResidue (F := F) n y)) * ψ (milnorResidueInfty n y) = 1
  rw [← ψ.map_add_eq_mul, milnorPolynomialTotalResidue_reciprocity]
  exact ψ.map_zero_eq_one

end

end GaloisForLFunctions.HTGeometry
