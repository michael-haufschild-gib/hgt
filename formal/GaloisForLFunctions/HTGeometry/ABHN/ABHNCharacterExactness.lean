/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.ABHNExactnessTransport
import GaloisForLFunctions.HTGeometry.ABHN.RatModIntCircleCharacter

/-!
# Character form of ABHN exactness

The canonical circle character of `ℚ/ℤ` converts the zero condition in an ABHN exact sequence
into a product-one condition.  Thus every realization statement governed by the ABHN exactness
contract has an equivalent character criterion.  The final two results instantiate this for the
project's raw number-field and rational-function-field finite-support targets.

This is an exactness transport result.  It neither assumes nor constructs local Brauer invariant
isomorphisms.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

/-- In any ABHN exact sequence, a local profile is globally realizable exactly when its canonical
`ℚ/ℤ` character is one. -/
theorem ABHNExactness.localInvariant_character_eq_one_iff_exists_global
    {G L : Type*} (globalToLocal : G → L) (localInvariant : L → RatModInt)
    (h : ABHNExactness G L globalToLocal localInvariant) (y : L) :
    ratModIntStdAddChar (localInvariant y) = 1 ↔ ∃ x, globalToLocal x = y := by
  rw [ratModIntStdAddChar_eq_one_iff_eq_zero]
  exact h.exact_globalToLocal_localInvariant y

/-- A number-field finite-support invariant profile has product-one character exactly when it is
a zero-sum profile, hence comes from the left term of the raw ABHN target sequence. -/
theorem numberFieldFinsuppRatModInt_character_product_eq_one_iff_exists_zeroSumProfile
    (K : Type*) [Field K] [NumberField K] (y : NumberFieldPlace K →₀ RatModInt) :
    y.prod (fun _ q ↦ ratModIntStdAddChar q) = 1 ↔
      ∃ x : (finsuppRatModIntSumAddHom (NumberFieldPlace K)).ker, x.1 = y := by
  rw [finsuppRatModIntStdAddChar_product_eq_one_iff_sum_eq_zero]
  exact finsuppRatModIntSum_zeroSum_exact (NumberFieldPlace K) y

/-- A rational-function-field finite-support invariant profile has product-one character exactly
when it is a zero-sum profile, hence comes from the left term of the raw ABHN target sequence. -/
theorem rationalFunctionFinsuppRatModInt_character_product_eq_one_iff_exists_zeroSumProfile
    (F : Type*) [Field F] [Finite F] (y : RationalFunctionPlace F →₀ RatModInt) :
    y.prod (fun _ q ↦ ratModIntStdAddChar q) = 1 ↔
      ∃ x : (finsuppRatModIntSumAddHom (RationalFunctionPlace F)).ker, x.1 = y := by
  rw [finsuppRatModIntStdAddChar_product_eq_one_iff_sum_eq_zero]
  exact finsuppRatModIntSum_zeroSum_exact (RationalFunctionPlace F) y

end GaloisForLFunctions.HTGeometry.ABHN
