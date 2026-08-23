/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.RestrictedInvariantSumQuotient

/-!
# The global circle character of `ℚ/ℤ`

The quotient `ℚ/ℤ` embeds additively in the real unit circle.  Composing with its exponential
character gives a faithful complex additive character.  Consequently, the additive global
reciprocity condition that a finite invariant profile sums to zero is exactly the multiplicative
condition that its local character values have product one.

This is a target-side reformulation of ABHN.  It neither constructs local Brauer invariants nor
identifies this character with a local epsilon factor.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u

/-- The additive map from rational numbers to the real circle of period one. -/
noncomputable def ratToUnitAddCircle : ℚ →+ AddCircle (1 : ℝ) :=
  (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))).comp
    (Rat.castHom ℝ).toAddMonoidHom

/-- The canonical additive embedding of `ℚ/ℤ` in the real circle of period one. -/
noncomputable def ratModIntToUnitAddCircle : RatModInt →+ AddCircle (1 : ℝ) :=
  QuotientAddGroup.lift (AddSubgroup.zmultiples (1 : ℚ)) ratToUnitAddCircle (by
    rintro q ⟨z, hz⟩
    change ((Rat.castHom ℝ) q : AddCircle (1 : ℝ)) = 0
    rw [← hz, map_zsmul, map_one]
    rw [AddCircle.coe_zsmul, AddCircle.coe_period, zsmul_zero])

/-- The circle embedding takes the class of a rational to its real class modulo one. -/
theorem ratModIntToUnitAddCircle_apply (q : ℚ) :
    ratModIntToUnitAddCircle (QuotientAddGroup.mk q : RatModInt) = (q : ℝ) := by
  rw [ratModIntToUnitAddCircle, QuotientAddGroup.lift_mk]
  rfl

/-- The circle embedding of `ℚ/ℤ` is faithful. -/
theorem ratModIntToUnitAddCircle_injective :
    Function.Injective ratModIntToUnitAddCircle := by
  intro a b
  refine QuotientAddGroup.induction_on a ?_
  intro a
  refine QuotientAddGroup.induction_on b ?_
  intro b hab
  rw [ratModIntToUnitAddCircle_apply, ratModIntToUnitAddCircle_apply] at hab
  have hzero : (((↑(a - b) : ℝ) : AddCircle (1 : ℝ))) = 0 := by
    rw [Rat.cast_sub, AddCircle.coe_sub, sub_eq_zero]
    exact hab
  obtain ⟨z, hz⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hzero
  rw [QuotientAddGroup.eq]
  refine ⟨-z, ?_⟩
  apply (Rat.cast_injective : Function.Injective (Rat.cast : ℚ → ℝ))
  change (((-z) • (1 : ℚ) : ℚ) : ℝ) = ((-a + b : ℚ) : ℝ)
  have htarget : (-z) • (1 : ℝ) = ((-a + b : ℚ) : ℝ) := by
    simpa [sub_eq_add_neg, add_comm] using congrArg (-·) hz
  calc
    (((-z) • (1 : ℚ) : ℚ) : ℝ) = (-z) • (1 : ℝ) := by
      convert (Rat.castHom ℝ).toAddMonoidHom.map_zsmul (-z) (1 : ℚ) using 1 <;> simp
    _ = ((-a + b : ℚ) : ℝ) := htarget

/-- The canonical faithful complex additive character of `ℚ/ℤ`. -/
noncomputable def ratModIntStdAddChar : AddChar RatModInt ℂ :=
  Circle.coeHom.compAddChar
    (AddCircle.toCircle_addChar.compAddMonoidHom ratModIntToUnitAddCircle)

/-- The standard global `ℚ/ℤ` character is faithful. -/
theorem ratModIntStdAddChar_injective : Function.Injective ratModIntStdAddChar := by
  exact Subtype.coe_injective.comp
    ((AddCircle.injective_toCircle one_ne_zero).comp ratModIntToUnitAddCircle_injective)

/-- The global character detects precisely the zero class of `ℚ/ℤ`. -/
theorem ratModIntStdAddChar_eq_one_iff_eq_zero (x : RatModInt) :
    ratModIntStdAddChar x = 1 ↔ x = 0 := by
  constructor
  · intro hx
    apply ratModIntStdAddChar_injective
    rw [hx]
    exact ratModIntStdAddChar.map_zero_eq_one.symm
  · intro hx
    rw [hx]
    exact ratModIntStdAddChar.map_zero_eq_one

/-- Apply the global `ℚ/ℤ` character after summing a finite local invariant profile. -/
noncomputable def finsuppRatModIntStdAddChar (ι : Type u) : AddChar (ι →₀ RatModInt) ℂ :=
  ratModIntStdAddChar.compAddMonoidHom (finsuppRatModIntSumAddHom ι)

/-- The global character of a profile is the product of its local character values. -/
theorem finsuppRatModIntStdAddChar_eq_finsupp_prod
    (ι : Type u) (f : ι →₀ RatModInt) :
    finsuppRatModIntStdAddChar ι f = f.prod fun _ x ↦ ratModIntStdAddChar x := by
  classical
  induction f using Finsupp.induction with
  | zero =>
      simp [finsuppRatModIntStdAddChar, finsuppRatModIntSumAddHom]
  | single_add i x f hif hx ih =>
      rw [(finsuppRatModIntStdAddChar ι).map_add_eq_mul, ih, Finsupp.prod_add_index']
      · rw [finsuppRatModIntStdAddChar, AddChar.compAddMonoidHom_apply,
          finsuppRatModIntSumAddHom_apply_single, Finsupp.prod_single_index]
        exact ratModIntStdAddChar.map_zero_eq_one
      · intro _
        exact ratModIntStdAddChar.map_zero_eq_one
      · intro _ a b
        exact ratModIntStdAddChar.map_add_eq_mul a b

/-- A finite `ℚ/ℤ` profile has product-one character precisely when its invariant sum is zero. -/
theorem finsuppRatModIntStdAddChar_product_eq_one_iff_sum_eq_zero
    (ι : Type u) (f : ι →₀ RatModInt) :
    f.prod (fun _ x ↦ ratModIntStdAddChar x) = 1 ↔
      finsuppRatModIntSumAddHom ι f = 0 := by
  rw [← finsuppRatModIntStdAddChar_eq_finsupp_prod]
  constructor
  · intro hf
    apply ratModIntStdAddChar_injective
    simpa [finsuppRatModIntStdAddChar] using hf
  · intro hf
    rw [finsuppRatModIntStdAddChar, AddChar.compAddMonoidHom_apply, hf]
    exact ratModIntStdAddChar.map_zero_eq_one

/-- Number-field global reciprocity is exactly the product-one law for the canonical local
`ℚ/ℤ` character values. -/
theorem numberFieldGlobalReciprocity_iff_character_product_one
    (K : Type*) [Field K] [NumberField K]
    (globalToLocal : BrauerGroup K →+ RestrictedLocalBrauerClasses K)
    (invariant : ∀ v : NumberFieldPlace K, BrauerGroup (completion K v) →+ RatModInt) :
    NumberFieldGlobalReciprocity K globalToLocal invariant ↔ ∀ x,
      (numberFieldLocalInvariantFinsupp K invariant (globalToLocal x)).prod
        (fun _ q ↦ ratModIntStdAddChar q) = 1 := by
  constructor
  · intro h x
    rw [finsuppRatModIntStdAddChar_product_eq_one_iff_sum_eq_zero]
    exact h x
  · intro h x
    have hx := h x
    rw [finsuppRatModIntStdAddChar_product_eq_one_iff_sum_eq_zero] at hx
    exact hx

/-- Function-field global reciprocity is exactly the product-one law for the canonical local
`ℚ/ℤ` character values. -/
theorem rationalFunctionGlobalReciprocity_iff_character_product_one
    (F : Type*) [Field F] [Finite F]
    (globalToLocal : BrauerGroup (RatFunc F) →+ RationalFunctionRestrictedLocalBrauerClasses F)
    (invariant : ∀ v : RationalFunctionPlace F,
      BrauerGroup (rationalFunctionCompletion F v) →+ RatModInt) :
    RationalFunctionGlobalReciprocity F globalToLocal invariant ↔ ∀ x,
      (rationalFunctionLocalInvariantFinsupp F invariant (globalToLocal x)).prod
        (fun _ q ↦ ratModIntStdAddChar q) = 1 := by
  constructor
  · intro h x
    rw [finsuppRatModIntStdAddChar_product_eq_one_iff_sum_eq_zero]
    exact h x
  · intro h x
    have hx := h x
    rw [finsuppRatModIntStdAddChar_product_eq_one_iff_sum_eq_zero] at hx
    exact hx

end GaloisForLFunctions.HTGeometry.ABHN
