import GaloisForLFunctions.HTGeometry.ABHN.RestrictedInvariantSum
import GaloisForLFunctions.HTGeometry.ABHN.FinsuppReciprocitySupportCardinality

/-!
# Support rigidity for restricted local Brauer invariants

For restricted local Brauer families over number fields or rational function fields, faithful
local invariants and a zero global invariant sum force every nonzero family to occupy at least two
places. Every specified nonsplit coordinate has a distinct nonsplit partner.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u

noncomputable local instance {K : Type*} [Field K] [NumberField K] :
    DecidableEq (NumberFieldPlace K) := Classical.decEq _

noncomputable local instance {F : Type*} [Field F] [Finite F] :
    DecidableEq (RationalFunctionPlace F) := Classical.decEq _

/-- Pointwise injective number-field local invariants give an injective restricted profile map. -/
theorem numberFieldLocalInvariantFinsuppAddHom_injective
    (K : Type u) [Field K] [NumberField K]
    (invariant : ∀ v : NumberFieldPlace K, BrauerGroup (completion K v) →+ RatModInt)
    (hinvariant : ∀ v, Function.Injective (invariant v)) :
    Function.Injective (numberFieldLocalInvariantFinsuppAddHom K invariant) := by
  intro x y hxy
  apply RestrictedLocalBrauerClasses.ext
  funext v
  apply hinvariant v
  have hv := Finsupp.ext_iff.mp hxy v
  simpa [numberFieldLocalInvariantFinsuppAddHom,
    numberFieldLocalInvariantFinsupp_apply] using hv

/-- A nonzero reciprocal number-field local Brauer family has invariant support at two or more
places. -/
theorem numberFieldLocalInvariantFinsupp_two_le_support_card_of_reciprocity
    (K : Type u) [Field K] [NumberField K]
    (invariant : ∀ v : NumberFieldPlace K, BrauerGroup (completion K v) →+ RatModInt)
    (hinvariant : ∀ v, Function.Injective (invariant v))
    (x : RestrictedLocalBrauerClasses K)
    (hrec : numberFieldRestrictedInvariantSum K invariant x = 0)
    (hne : x ≠ 0) :
    2 ≤ (numberFieldLocalInvariantFinsupp K invariant x).support.card := by
  have hprofile : numberFieldLocalInvariantFinsupp K invariant x ≠ 0 := by
    intro hzero
    apply hne
    apply numberFieldLocalInvariantFinsuppAddHom_injective K invariant hinvariant
    rw [map_zero]
    exact hzero
  exact finsupp_two_le_support_card_of_sum_eq_zero
    (numberFieldLocalInvariantFinsupp K invariant x) hrec hprofile

/-- A nonzero reciprocal number-field local Brauer family has two distinct nonsplit places. -/
theorem numberFieldRestrictedLocalBrauer_exists_two_nonSplit_places_of_reciprocity
    (K : Type u) [Field K] [NumberField K]
    (invariant : ∀ v : NumberFieldPlace K, BrauerGroup (completion K v) →+ RatModInt)
    (hinvariant : ∀ v, Function.Injective (invariant v))
    (x : RestrictedLocalBrauerClasses K)
    (hrec : numberFieldRestrictedInvariantSum K invariant x = 0)
    (hne : x ≠ 0) :
    ∃ v w, v ≠ w ∧ x.toLocalBrauerClasses v ≠ 0 ∧
      x.toLocalBrauerClasses w ≠ 0 := by
  have hprofile : numberFieldLocalInvariantFinsupp K invariant x ≠ 0 := by
    intro hzero
    apply hne
    apply numberFieldLocalInvariantFinsuppAddHom_injective K invariant hinvariant
    rw [map_zero]
    exact hzero
  obtain ⟨v, w, hvw, hv, hw⟩ := finsupp_exists_two_nonzero_places_of_sum_eq_zero
    (numberFieldLocalInvariantFinsupp K invariant x) hrec hprofile
  refine ⟨v, w, hvw, ?_, ?_⟩
  · intro hvzero
    apply hv
    rw [numberFieldLocalInvariantFinsupp_apply, hvzero, map_zero]
  · intro hwzero
    apply hw
    rw [numberFieldLocalInvariantFinsupp_apply, hwzero, map_zero]

/-- Every specified nonsplit coordinate of a reciprocal number-field local Brauer family has a
distinct nonsplit partner. -/
theorem numberFieldRestrictedLocalBrauer_nonSplit_place_has_partner_of_reciprocity
    (K : Type u) [Field K] [NumberField K]
    (invariant : ∀ v : NumberFieldPlace K, BrauerGroup (completion K v) →+ RatModInt)
    (hinvariant : ∀ v, Function.Injective (invariant v))
    (x : RestrictedLocalBrauerClasses K)
    (hrec : numberFieldRestrictedInvariantSum K invariant x = 0)
    (v : NumberFieldPlace K) (hv : x.toLocalBrauerClasses v ≠ 0) :
    ∃ w, w ≠ v ∧ x.toLocalBrauerClasses w ≠ 0 := by
  have hvi : numberFieldLocalInvariantFinsupp K invariant x v ≠ 0 := by
    rw [numberFieldLocalInvariantFinsupp_apply]
    intro hzero
    apply hv
    apply hinvariant v
    simpa using hzero
  obtain ⟨w, hwv, hw⟩ := finsupp_exists_other_nonzero_place_of_sum_eq_zero
    (numberFieldLocalInvariantFinsupp K invariant x) hrec hvi
  refine ⟨w, hwv, ?_⟩
  intro hwzero
  apply hw
  rw [numberFieldLocalInvariantFinsupp_apply, hwzero, map_zero]

/-- Pointwise injective function-field local invariants give an injective restricted profile
map. -/
theorem rationalFunctionLocalInvariantFinsuppAddHom_injective
    (F : Type u) [Field F] [Finite F]
    (invariant : ∀ v : RationalFunctionPlace F,
      BrauerGroup (rationalFunctionCompletion F v) →+ RatModInt)
    (hinvariant : ∀ v, Function.Injective (invariant v)) :
    Function.Injective (rationalFunctionLocalInvariantFinsuppAddHom F invariant) := by
  intro x y hxy
  apply RationalFunctionRestrictedLocalBrauerClasses.ext
  funext v
  apply hinvariant v
  have hv := Finsupp.ext_iff.mp hxy v
  simpa [rationalFunctionLocalInvariantFinsuppAddHom,
    rationalFunctionLocalInvariantFinsupp_apply] using hv

/-- A nonzero reciprocal rational-function local Brauer family has invariant support at two or
more places. -/
theorem rationalFunctionLocalInvariantFinsupp_two_le_support_card_of_reciprocity
    (F : Type u) [Field F] [Finite F]
    (invariant : ∀ v : RationalFunctionPlace F,
      BrauerGroup (rationalFunctionCompletion F v) →+ RatModInt)
    (hinvariant : ∀ v, Function.Injective (invariant v))
    (x : RationalFunctionRestrictedLocalBrauerClasses F)
    (hrec : rationalFunctionRestrictedInvariantSum F invariant x = 0)
    (hne : x ≠ 0) :
    2 ≤ (rationalFunctionLocalInvariantFinsupp F invariant x).support.card := by
  have hprofile : rationalFunctionLocalInvariantFinsupp F invariant x ≠ 0 := by
    intro hzero
    apply hne
    apply rationalFunctionLocalInvariantFinsuppAddHom_injective F invariant hinvariant
    rw [map_zero]
    exact hzero
  exact finsupp_two_le_support_card_of_sum_eq_zero
    (rationalFunctionLocalInvariantFinsupp F invariant x) hrec hprofile

/-- A nonzero reciprocal rational-function local Brauer family has two distinct nonsplit
places. -/
theorem rationalFunctionRestrictedLocalBrauer_exists_two_nonSplit_places_of_reciprocity
    (F : Type u) [Field F] [Finite F]
    (invariant : ∀ v : RationalFunctionPlace F,
      BrauerGroup (rationalFunctionCompletion F v) →+ RatModInt)
    (hinvariant : ∀ v, Function.Injective (invariant v))
    (x : RationalFunctionRestrictedLocalBrauerClasses F)
    (hrec : rationalFunctionRestrictedInvariantSum F invariant x = 0)
    (hne : x ≠ 0) :
    ∃ v w, v ≠ w ∧ x.toLocalBrauerClasses v ≠ 0 ∧
      x.toLocalBrauerClasses w ≠ 0 := by
  have hprofile : rationalFunctionLocalInvariantFinsupp F invariant x ≠ 0 := by
    intro hzero
    apply hne
    apply rationalFunctionLocalInvariantFinsuppAddHom_injective F invariant hinvariant
    rw [map_zero]
    exact hzero
  obtain ⟨v, w, hvw, hv, hw⟩ := finsupp_exists_two_nonzero_places_of_sum_eq_zero
    (rationalFunctionLocalInvariantFinsupp F invariant x) hrec hprofile
  refine ⟨v, w, hvw, ?_, ?_⟩
  · intro hvzero
    apply hv
    rw [rationalFunctionLocalInvariantFinsupp_apply, hvzero, map_zero]
  · intro hwzero
    apply hw
    rw [rationalFunctionLocalInvariantFinsupp_apply, hwzero, map_zero]

/-- Every specified nonsplit coordinate of a reciprocal rational-function local Brauer family
has a distinct nonsplit partner. -/
theorem rationalFunctionRestrictedLocalBrauer_nonSplit_place_has_partner_of_reciprocity
    (F : Type u) [Field F] [Finite F]
    (invariant : ∀ v : RationalFunctionPlace F,
      BrauerGroup (rationalFunctionCompletion F v) →+ RatModInt)
    (hinvariant : ∀ v, Function.Injective (invariant v))
    (x : RationalFunctionRestrictedLocalBrauerClasses F)
    (hrec : rationalFunctionRestrictedInvariantSum F invariant x = 0)
    (v : RationalFunctionPlace F) (hv : x.toLocalBrauerClasses v ≠ 0) :
    ∃ w, w ≠ v ∧ x.toLocalBrauerClasses w ≠ 0 := by
  have hvi : rationalFunctionLocalInvariantFinsupp F invariant x v ≠ 0 := by
    rw [rationalFunctionLocalInvariantFinsupp_apply]
    intro hzero
    apply hv
    apply hinvariant v
    simpa using hzero
  obtain ⟨w, hwv, hw⟩ := finsupp_exists_other_nonzero_place_of_sum_eq_zero
    (rationalFunctionLocalInvariantFinsupp F invariant x) hrec hvi
  refine ⟨w, hwv, ?_⟩
  intro hwzero
  apply hw
  rw [rationalFunctionLocalInvariantFinsupp_apply, hwzero, map_zero]

/-- Global number-field reciprocity forces any locally nonzero global class to have two distinct
nonsplit localizations. -/
theorem numberFieldGlobalReciprocity_exists_two_nonSplit_places
    (K : Type u) [Field K] [NumberField K]
    (globalToLocal : BrauerGroup.{u, u} K →+ RestrictedLocalBrauerClasses K)
    (invariant : ∀ v : NumberFieldPlace K, BrauerGroup (completion K v) →+ RatModInt)
    (hrec : NumberFieldGlobalReciprocity K globalToLocal invariant)
    (hinvariant : ∀ v, Function.Injective (invariant v))
    (x : BrauerGroup.{u, u} K) (hne : globalToLocal x ≠ 0) :
    ∃ v w, v ≠ w ∧ (globalToLocal x).toLocalBrauerClasses v ≠ 0 ∧
      (globalToLocal x).toLocalBrauerClasses w ≠ 0 :=
  numberFieldRestrictedLocalBrauer_exists_two_nonSplit_places_of_reciprocity
    K invariant hinvariant (globalToLocal x) (hrec x) hne

/-- With faithful global localization, every nonzero number-field Brauer class has two distinct
nonsplit localizations under global reciprocity. -/
theorem numberFieldGlobalReciprocity_injective_exists_two_nonSplit_places
    (K : Type u) [Field K] [NumberField K]
    (globalToLocal : BrauerGroup.{u, u} K →+ RestrictedLocalBrauerClasses K)
    (invariant : ∀ v : NumberFieldPlace K, BrauerGroup (completion K v) →+ RatModInt)
    (hrec : NumberFieldGlobalReciprocity K globalToLocal invariant)
    (hglobal : Function.Injective globalToLocal)
    (hinvariant : ∀ v, Function.Injective (invariant v))
    (x : BrauerGroup.{u, u} K) (hne : x ≠ 0) :
    ∃ v w, v ≠ w ∧ (globalToLocal x).toLocalBrauerClasses v ≠ 0 ∧
      (globalToLocal x).toLocalBrauerClasses w ≠ 0 := by
  apply numberFieldGlobalReciprocity_exists_two_nonSplit_places
    K globalToLocal invariant hrec hinvariant x
  intro hzero
  apply hne
  apply hglobal
  rw [map_zero]
  exact hzero

/-- Global function-field reciprocity forces any locally nonzero global class to have two
distinct nonsplit localizations. -/
theorem rationalFunctionGlobalReciprocity_exists_two_nonSplit_places
    (F : Type u) [Field F] [Finite F]
    (globalToLocal : BrauerGroup.{u, u} (RatFunc F) →+
      RationalFunctionRestrictedLocalBrauerClasses F)
    (invariant : ∀ v : RationalFunctionPlace F,
      BrauerGroup (rationalFunctionCompletion F v) →+ RatModInt)
    (hrec : RationalFunctionGlobalReciprocity F globalToLocal invariant)
    (hinvariant : ∀ v, Function.Injective (invariant v))
    (x : BrauerGroup.{u, u} (RatFunc F)) (hne : globalToLocal x ≠ 0) :
    ∃ v w, v ≠ w ∧ (globalToLocal x).toLocalBrauerClasses v ≠ 0 ∧
      (globalToLocal x).toLocalBrauerClasses w ≠ 0 :=
  rationalFunctionRestrictedLocalBrauer_exists_two_nonSplit_places_of_reciprocity
    F invariant hinvariant (globalToLocal x) (hrec x) hne

/-- With faithful global localization, every nonzero function-field Brauer class has two distinct
nonsplit localizations under global reciprocity. -/
theorem rationalFunctionGlobalReciprocity_injective_exists_two_nonSplit_places
    (F : Type u) [Field F] [Finite F]
    (globalToLocal : BrauerGroup.{u, u} (RatFunc F) →+
      RationalFunctionRestrictedLocalBrauerClasses F)
    (invariant : ∀ v : RationalFunctionPlace F,
      BrauerGroup (rationalFunctionCompletion F v) →+ RatModInt)
    (hrec : RationalFunctionGlobalReciprocity F globalToLocal invariant)
    (hglobal : Function.Injective globalToLocal)
    (hinvariant : ∀ v, Function.Injective (invariant v))
    (x : BrauerGroup.{u, u} (RatFunc F)) (hne : x ≠ 0) :
    ∃ v w, v ≠ w ∧ (globalToLocal x).toLocalBrauerClasses v ≠ 0 ∧
      (globalToLocal x).toLocalBrauerClasses w ≠ 0 := by
  apply rationalFunctionGlobalReciprocity_exists_two_nonSplit_places
    F globalToLocal invariant hrec hinvariant x
  intro hzero
  apply hne
  apply hglobal
  rw [map_zero]
  exact hzero

end GaloisForLFunctions.HTGeometry.ABHN
