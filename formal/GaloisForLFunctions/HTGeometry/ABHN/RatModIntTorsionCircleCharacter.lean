/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.FiniteTorsionInvariantSum
import GaloisForLFunctions.HTGeometry.ABHN.RatModIntCircleCharacter

/-!
# Compatibility of finite and global `ℚ/ℤ` characters

At a finite torsion level, local-invariant constructions use the standard character of `ℤ/nℤ`.
The global ABHN target uses the canonical circle character of `ℚ/ℤ`.  This file proves that these
are exactly the same character after the canonical inclusion `ℤ/nℤ ≃ ℚ/ℤ[n] ↪ ℚ/ℤ`.  Thus the
finite product-one laws already formalized for cyclic local data are literal restrictions of the
global character form of reciprocity.

No local Brauer comparison or class-field-theoretic reciprocity map is assumed.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

/-- The global `ℚ/ℤ` circle character agrees with the standard `ℤ/nℤ` character after the
canonical finite-level invariant map. -/
theorem ratModIntStdAddChar_zmodRatModIntAddHom
    (n : ℕ) (hn : n ≠ 0) (x : ZMod n) :
    ratModIntStdAddChar (zmodRatModIntAddHom n hn x) =
      @ZMod.stdAddChar n ⟨hn⟩ x := by
  letI : NeZero n := ⟨hn⟩
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  rw [zmodRatModIntAddHom, ZMod.lift_coe]
  change ratModIntStdAddChar
      (QuotientAddGroup.mk ((z : ℚ) / (n : ℚ)) : RatModInt) =
    @ZMod.stdAddChar n ⟨hn⟩ (z : ZMod n)
  change (↑(AddCircle.toCircle
      (ratModIntToUnitAddCircle (QuotientAddGroup.mk ((z : ℚ) / (n : ℚ))))) : ℂ) = _
  rw [ratModIntToUnitAddCircle_apply, AddCircle.toCircle_apply_mk,
    Circle.coe_exp, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  field_simp

/-- Restricting the global character to `ℚ/ℤ[n]` recovers its existing finite torsion character. -/
theorem ratModIntStdAddChar_subtype_eq_ratModIntNTorsionStdAddChar
    (n : ℕ) (hn : n ≠ 0) (x : ratModIntNTorsion n) :
    ratModIntStdAddChar (x : RatModInt) = ratModIntNTorsionStdAddChar n hn x := by
  let z : ZMod n := (zmodRatModIntAddEquivNTorsion n hn).symm x
  have hz : zmodRatModIntAddHom n hn z = (x : RatModInt) := by
    exact congrArg Subtype.val
      ((zmodRatModIntAddEquivNTorsion n hn).apply_symm_apply x)
  calc
    ratModIntStdAddChar (x : RatModInt) = ratModIntStdAddChar
        (zmodRatModIntAddHom n hn z) := by rw [hz]
    _ = @ZMod.stdAddChar n ⟨hn⟩ z := ratModIntStdAddChar_zmodRatModIntAddHom n hn z
    _ = ratModIntNTorsionStdAddChar n hn x := by
      change @ZMod.stdAddChar n ⟨hn⟩ z =
        @ZMod.stdAddChar n ⟨hn⟩ ((zmodRatModIntAddEquivNTorsion n hn).symm x)
      rfl

/-- The local product using the global character equals the existing finite-level character
product on every finite torsion profile. -/
theorem finsuppRatModIntNTorsion_global_character_product_eq_finite
    {ι : Type*} (n : ℕ) (hn : n ≠ 0) (f : ι →₀ ratModIntNTorsion n) :
    f.prod (fun _ x ↦ ratModIntStdAddChar (x : RatModInt)) =
      f.prod (fun _ x ↦ ratModIntNTorsionStdAddChar n hn x) := by
  apply Finsupp.prod_congr
  intro i hi
  exact ratModIntStdAddChar_subtype_eq_ratModIntNTorsionStdAddChar n hn (f i)

/-- Finite-level additive reciprocity is the product-one law for the restriction of the one
global `ℚ/ℤ` character. -/
theorem finsuppRatModIntNTorsion_global_character_product_eq_one_iff_sum_eq_zero
    {ι : Type*} (n : ℕ) (hn : n ≠ 0) (f : ι →₀ ratModIntNTorsion n) :
    f.prod (fun _ x ↦ ratModIntStdAddChar (x : RatModInt)) = 1 ↔
      finsuppRatModIntNTorsionSumAddHom ι n f = 0 := by
  rw [finsuppRatModIntNTorsion_global_character_product_eq_finite n hn f,
    finsuppRatModIntNTorsionStdAddChar_product_eq_one_iff_sum_eq_zero ι n hn f]

end

end GaloisForLFunctions.HTGeometry.ABHN
