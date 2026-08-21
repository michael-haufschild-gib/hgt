/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.RestrictedInvariantSumSplit

/-!
# One-place sections of the restricted ABHN invariant target

Each local Brauer group embeds additively into the restricted product by putting its class at one
place and the split class elsewhere.  Consequently, once one local invariant is surjective, the
finite invariant sum on the restricted local term is surjective.  This is target-side ABHN
infrastructure; the unformalized local class-field-theory theorem is precisely what will supply
the required local surjectivity at a nonarchimedean place.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u

noncomputable section

/-- Put a number-field local Brauer class at one place and use the split class elsewhere. -/
noncomputable def numberFieldRestrictedLocalBrauerSingle
    (K : Type u) [Field K] [NumberField K] (v : NumberFieldPlace K) :
    BrauerGroup (completion K v) → RestrictedLocalBrauerClasses K := by
  classical
  intro a
  refine ⟨(Pi.single v a : localBrauerClasses K), ?_⟩
  apply (Set.finite_singleton v).subset
  intro w hw
  change (Pi.single v a : localBrauerClasses K) w ≠ brauerSplitClass (completion K w) at hw
  by_contra hwv
  rw [Pi.single_eq_of_ne hwv] at hw
  apply hw
  change (0 : BrauerGroup (completion K w)) = 0
  rfl

/-- The one-place number-field section is additive. -/
noncomputable def numberFieldRestrictedLocalBrauerSingleAddHom
    (K : Type u) [Field K] [NumberField K] (v : NumberFieldPlace K) :
    BrauerGroup (completion K v) →+ RestrictedLocalBrauerClasses K := by
  classical
  refine
    { toFun := numberFieldRestrictedLocalBrauerSingle K v
      map_zero' := ?_
      map_add' := ?_ }
  · apply RestrictedLocalBrauerClasses.ext
    funext w
    change (Pi.single v (0 : BrauerGroup (completion K v)) : localBrauerClasses K) w = 0
    rw [Pi.single_zero]
    rfl
  · intro a b
    apply RestrictedLocalBrauerClasses.ext
    exact Pi.single_add (f := fun w : NumberFieldPlace K => BrauerGroup (completion K w)) v a b

/-- Evaluation at the selected place recovers the inserted number-field local class. -/
theorem numberFieldRestrictedLocalBrauerSingle_apply
    (K : Type u) [Field K] [NumberField K] (v : NumberFieldPlace K)
    (a : BrauerGroup (completion K v)) :
    (numberFieldRestrictedLocalBrauerSingle K v a).toLocalBrauerClasses v = a := by
  classical
  change (Pi.single v a : localBrauerClasses K) v = a
  exact Pi.single_eq_same (M := fun w : NumberFieldPlace K => BrauerGroup (completion K w)) v a

/-- The additive number-field one-place section is injective. -/
theorem numberFieldRestrictedLocalBrauerSingleAddHom_injective
    (K : Type u) [Field K] [NumberField K] (v : NumberFieldPlace K) :
    Function.Injective (numberFieldRestrictedLocalBrauerSingleAddHom K v) := by
  intro a b h
  have hlocal := congrArg (fun x : RestrictedLocalBrauerClasses K => x.toLocalBrauerClasses v) h
  change (numberFieldRestrictedLocalBrauerSingle K v a).toLocalBrauerClasses v =
    (numberFieldRestrictedLocalBrauerSingle K v b).toLocalBrauerClasses v at hlocal
  simpa only [numberFieldRestrictedLocalBrauerSingle_apply] using hlocal

/-- The local-invariant finite-support profile of a one-place family is the corresponding
one-place `ℚ/ℤ` profile. -/
theorem numberFieldLocalInvariantFinsupp_single
    (K : Type u) [Field K] [NumberField K]
    (invariant : ∀ v : NumberFieldPlace K, BrauerGroup (completion K v) →+ RatModInt)
    (v : NumberFieldPlace K) (a : BrauerGroup (completion K v)) :
    numberFieldLocalInvariantFinsupp K invariant
      (numberFieldRestrictedLocalBrauerSingle K v a) = Finsupp.single v (invariant v a) := by
  classical
  ext w
  rw [numberFieldLocalInvariantFinsupp_apply]
  change invariant w ((Pi.single v a : localBrauerClasses K) w) =
    Finsupp.single v (invariant v a) w
  by_cases hwv : w = v
  · subst w
    rw [Pi.single_eq_same, Finsupp.single_eq_same]
  · rw [Pi.single_eq_of_ne hwv]
    simp [Ne.symm hwv]

/-- Summing a one-place number-field invariant profile recovers its local invariant. -/
theorem numberFieldRestrictedInvariantSum_single
    (K : Type u) [Field K] [NumberField K]
    (invariant : ∀ v : NumberFieldPlace K, BrauerGroup (completion K v) →+ RatModInt)
    (v : NumberFieldPlace K) (a : BrauerGroup (completion K v)) :
    numberFieldRestrictedInvariantSum K invariant
      (numberFieldRestrictedLocalBrauerSingle K v a) = invariant v a := by
  change finsuppRatModIntSumAddHom (NumberFieldPlace K)
    (numberFieldLocalInvariantFinsupp K invariant
      (numberFieldRestrictedLocalBrauerSingle K v a)) = invariant v a
  rw [numberFieldLocalInvariantFinsupp_single]
  exact finsuppRatModIntSum_single v (invariant v a)

/-- The number-field invariant sum composed with a one-place section is the selected local
invariant. -/
theorem numberFieldRestrictedInvariantSum_comp_single
    (K : Type u) [Field K] [NumberField K]
    (invariant : ∀ v : NumberFieldPlace K, BrauerGroup (completion K v) →+ RatModInt)
    (v : NumberFieldPlace K) :
    (numberFieldRestrictedInvariantSum K invariant).comp
      (numberFieldRestrictedLocalBrauerSingleAddHom K v) = invariant v := by
  ext a
  exact numberFieldRestrictedInvariantSum_single K invariant v a

/-- Surjectivity of one number-field local invariant implies surjectivity of the restricted
global invariant sum. -/
theorem numberFieldRestrictedInvariantSum_surjective_of_surjective_at
    (K : Type u) [Field K] [NumberField K]
    (invariant : ∀ v : NumberFieldPlace K, BrauerGroup (completion K v) →+ RatModInt)
    (v : NumberFieldPlace K) (hv : Function.Surjective (invariant v)) :
    Function.Surjective (numberFieldRestrictedInvariantSum K invariant) := by
  intro q
  obtain ⟨a, ha⟩ := hv q
  exact ⟨numberFieldRestrictedLocalBrauerSingle K v a,
    (numberFieldRestrictedInvariantSum_single K invariant v a).trans ha⟩

/-- Put a rational-function-field local Brauer class at one place and use the split class
elsewhere. -/
noncomputable def rationalFunctionRestrictedLocalBrauerSingle
    (F : Type u) [Field F] [Finite F] (v : RationalFunctionPlace F) :
    BrauerGroup (rationalFunctionCompletion F v) →
      RationalFunctionRestrictedLocalBrauerClasses F := by
  classical
  intro a
  refine ⟨(Pi.single v a : rationalFunctionLocalBrauerClasses F), ?_⟩
  apply (Set.finite_singleton v).subset
  intro w hw
  change (Pi.single v a : rationalFunctionLocalBrauerClasses F) w ≠
    brauerSplitClass (rationalFunctionCompletion F w) at hw
  by_contra hwv
  rw [Pi.single_eq_of_ne hwv] at hw
  apply hw
  change (0 : BrauerGroup (rationalFunctionCompletion F w)) = 0
  rfl

/-- The one-place rational-function-field section is additive. -/
noncomputable def rationalFunctionRestrictedLocalBrauerSingleAddHom
    (F : Type u) [Field F] [Finite F] (v : RationalFunctionPlace F) :
    BrauerGroup (rationalFunctionCompletion F v) →+
      RationalFunctionRestrictedLocalBrauerClasses F := by
  classical
  refine
    { toFun := rationalFunctionRestrictedLocalBrauerSingle F v
      map_zero' := ?_
      map_add' := ?_ }
  · apply RationalFunctionRestrictedLocalBrauerClasses.ext
    funext w
    change (Pi.single v (0 : BrauerGroup (rationalFunctionCompletion F v)) :
      rationalFunctionLocalBrauerClasses F) w = 0
    rw [Pi.single_zero]
    rfl
  · intro a b
    apply RationalFunctionRestrictedLocalBrauerClasses.ext
    exact Pi.single_add (f := fun w : RationalFunctionPlace F =>
      BrauerGroup (rationalFunctionCompletion F w)) v a b

/-- Evaluation at the selected place recovers the inserted rational-function-field local class. -/
theorem rationalFunctionRestrictedLocalBrauerSingle_apply
    (F : Type u) [Field F] [Finite F] (v : RationalFunctionPlace F)
    (a : BrauerGroup (rationalFunctionCompletion F v)) :
    (rationalFunctionRestrictedLocalBrauerSingle F v a).toLocalBrauerClasses v = a := by
  classical
  change (Pi.single v a : rationalFunctionLocalBrauerClasses F) v = a
  exact Pi.single_eq_same (M := fun w : RationalFunctionPlace F =>
    BrauerGroup (rationalFunctionCompletion F w)) v a

/-- The additive rational-function-field one-place section is injective. -/
theorem rationalFunctionRestrictedLocalBrauerSingleAddHom_injective
    (F : Type u) [Field F] [Finite F] (v : RationalFunctionPlace F) :
    Function.Injective (rationalFunctionRestrictedLocalBrauerSingleAddHom F v) := by
  intro a b h
  have hlocal := congrArg
    (fun x : RationalFunctionRestrictedLocalBrauerClasses F => x.toLocalBrauerClasses v) h
  change (rationalFunctionRestrictedLocalBrauerSingle F v a).toLocalBrauerClasses v =
    (rationalFunctionRestrictedLocalBrauerSingle F v b).toLocalBrauerClasses v at hlocal
  simpa only [rationalFunctionRestrictedLocalBrauerSingle_apply] using hlocal

/-- The local-invariant finite-support profile of a one-place rational-function-field family is
the corresponding one-place `ℚ/ℤ` profile. -/
theorem rationalFunctionLocalInvariantFinsupp_single
    (F : Type u) [Field F] [Finite F]
    (invariant : ∀ v : RationalFunctionPlace F,
      BrauerGroup (rationalFunctionCompletion F v) →+ RatModInt)
    (v : RationalFunctionPlace F) (a : BrauerGroup (rationalFunctionCompletion F v)) :
    rationalFunctionLocalInvariantFinsupp F invariant
      (rationalFunctionRestrictedLocalBrauerSingle F v a) =
        Finsupp.single v (invariant v a) := by
  classical
  ext w
  rw [rationalFunctionLocalInvariantFinsupp_apply]
  change invariant w ((Pi.single v a : rationalFunctionLocalBrauerClasses F) w) =
    Finsupp.single v (invariant v a) w
  by_cases hwv : w = v
  · subst w
    rw [Pi.single_eq_same, Finsupp.single_eq_same]
  · rw [Pi.single_eq_of_ne hwv]
    simp [Ne.symm hwv]

/-- Summing a one-place rational-function-field invariant profile recovers its local invariant.
-/
theorem rationalFunctionRestrictedInvariantSum_single
    (F : Type u) [Field F] [Finite F]
    (invariant : ∀ v : RationalFunctionPlace F,
      BrauerGroup (rationalFunctionCompletion F v) →+ RatModInt)
    (v : RationalFunctionPlace F) (a : BrauerGroup (rationalFunctionCompletion F v)) :
    rationalFunctionRestrictedInvariantSum F invariant
      (rationalFunctionRestrictedLocalBrauerSingle F v a) = invariant v a := by
  change finsuppRatModIntSumAddHom (RationalFunctionPlace F)
    (rationalFunctionLocalInvariantFinsupp F invariant
      (rationalFunctionRestrictedLocalBrauerSingle F v a)) = invariant v a
  rw [rationalFunctionLocalInvariantFinsupp_single]
  exact finsuppRatModIntSum_single v (invariant v a)

/-- The rational-function-field invariant sum composed with a one-place section is the selected
local invariant. -/
theorem rationalFunctionRestrictedInvariantSum_comp_single
    (F : Type u) [Field F] [Finite F]
    (invariant : ∀ v : RationalFunctionPlace F,
      BrauerGroup (rationalFunctionCompletion F v) →+ RatModInt)
    (v : RationalFunctionPlace F) :
    (rationalFunctionRestrictedInvariantSum F invariant).comp
      (rationalFunctionRestrictedLocalBrauerSingleAddHom F v) = invariant v := by
  ext a
  exact rationalFunctionRestrictedInvariantSum_single F invariant v a

/-- Surjectivity of one rational-function-field local invariant implies surjectivity of the
restricted global invariant sum. -/
theorem rationalFunctionRestrictedInvariantSum_surjective_of_surjective_at
    (F : Type u) [Field F] [Finite F]
    (invariant : ∀ v : RationalFunctionPlace F,
      BrauerGroup (rationalFunctionCompletion F v) →+ RatModInt)
    (v : RationalFunctionPlace F) (hv : Function.Surjective (invariant v)) :
    Function.Surjective (rationalFunctionRestrictedInvariantSum F invariant) := by
  intro q
  obtain ⟨a, ha⟩ := hv q
  exact ⟨rationalFunctionRestrictedLocalBrauerSingle F v a,
    (rationalFunctionRestrictedInvariantSum_single F invariant v a).trans ha⟩

end

end GaloisForLFunctions.HTGeometry.ABHN
