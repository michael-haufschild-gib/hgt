/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.RestrictedInvariantSurjectivity

/-!
# Restricted local Brauer groups as dependent finite-support sums

The restricted local terms used by ABHN are definitionally families with finite nonsplit support.
This file identifies them additively with the canonical dependent finitely supported families of
their local Brauer groups.  Under these equivalences, one-place sections are literal
`DFinsupp.single` terms and placewise equality is a Hasse criterion.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u

/-! ## Number fields -/

/-- Coordinate map from restricted number-field local Brauer classes to dependent finite-support
families. -/
noncomputable def numberFieldRestrictedLocalBrauerToDFinsuppAddHom
    (K : Type u) [Field K] [NumberField K] :
    RestrictedLocalBrauerClasses K →+
      (Π₀ v : NumberFieldPlace K, BrauerGroup (completion K v)) := by
  classical
  refine
    { toFun := fun x =>
        { toFun := x.toLocalBrauerClasses
          support' := Trunc.mk ⟨x.finite_nonSplit_support.toFinset.1, fun v => by
            by_cases hv : x.toLocalBrauerClasses v = 0
            · exact Or.inr hv
            · exact Or.inl (by
                have hv' : v ∈ {w | x.toLocalBrauerClasses w ≠
                    brauerSplitClass (completion K w)} := by
                  change x.toLocalBrauerClasses v ≠ 0
                  exact hv
                have hvfin : v ∈ x.finite_nonSplit_support.toFinset := by
                  simpa only [Set.Finite.mem_toFinset] using hv'
                exact hvfin)⟩ }
      map_zero' := ?_
      map_add' := ?_ }
  · apply DFinsupp.ext
    intro v
    rfl
  · intro x y
    apply DFinsupp.ext
    intro v
    rfl

/-- Restricted number-field local Brauer coordinates are faithful. -/
theorem numberFieldRestrictedLocalBrauerToDFinsuppAddHom_injective
    (K : Type u) [Field K] [NumberField K] :
    Function.Injective (numberFieldRestrictedLocalBrauerToDFinsuppAddHom K) := by
  intro x y hxy
  apply RestrictedLocalBrauerClasses.ext
  funext v
  exact DFunLike.congr_fun hxy v

/-- Every dependent finite-support family of number-field local Brauer classes is a restricted
local family. -/
theorem numberFieldRestrictedLocalBrauerToDFinsuppAddHom_surjective
    (K : Type u) [Field K] [NumberField K] :
    Function.Surjective (numberFieldRestrictedLocalBrauerToDFinsuppAddHom K) := by
  classical
  intro x
  let y : RestrictedLocalBrauerClasses K :=
    { toLocalBrauerClasses := fun v => x v
      finite_nonSplit_support := by
        change {v | x v ≠ 0}.Finite
        have heq : (↑x.support : Set (NumberFieldPlace K)) = {v | x v ≠ 0} := by
          ext v
          change v ∈ x.support ↔ x v ≠ 0
          exact DFinsupp.mem_support_iff
        rw [← heq]
        exact x.support.finite_toSet }
  refine ⟨y, ?_⟩
  apply DFinsupp.ext
  intro v
  rfl

/-- The number-field restricted local Brauer group is the dependent direct sum of its local
Brauer groups. -/
noncomputable def numberFieldRestrictedLocalBrauerDFinsuppEquiv
    (K : Type u) [Field K] [NumberField K] :
    RestrictedLocalBrauerClasses K ≃+
      (Π₀ v : NumberFieldPlace K, BrauerGroup (completion K v)) :=
  AddEquiv.ofBijective (numberFieldRestrictedLocalBrauerToDFinsuppAddHom K)
    ⟨numberFieldRestrictedLocalBrauerToDFinsuppAddHom_injective K,
      numberFieldRestrictedLocalBrauerToDFinsuppAddHom_surjective K⟩

/-- The dependent-direct-sum equivalence evaluates by the original local coordinate. -/
@[simp] theorem numberFieldRestrictedLocalBrauerDFinsuppEquiv_apply
    (K : Type u) [Field K] [NumberField K]
    (x : RestrictedLocalBrauerClasses K) (v : NumberFieldPlace K) :
    numberFieldRestrictedLocalBrauerDFinsuppEquiv K x v =
      x.toLocalBrauerClasses v := rfl

/-- Canonical one-place dependent family for number-field local Brauer classes. -/
noncomputable def numberFieldLocalBrauerDFinsuppSingle
    (K : Type u) [Field K] [NumberField K]
    (v : NumberFieldPlace K) (a : BrauerGroup (completion K v)) :
    (Π₀ w : NumberFieldPlace K, BrauerGroup (completion K w)) := by
  classical
  exact DFinsupp.single v a

/-- A restricted one-place section is literally a dependent finitely supported singleton. -/
theorem numberFieldRestrictedLocalBrauerDFinsuppEquiv_single
    (K : Type u) [Field K] [NumberField K]
    (v : NumberFieldPlace K) (a : BrauerGroup (completion K v)) :
    numberFieldRestrictedLocalBrauerDFinsuppEquiv K
        (numberFieldRestrictedLocalBrauerSingle K v a) =
      numberFieldLocalBrauerDFinsuppSingle K v a := by
  classical
  apply DFinsupp.ext
  intro w
  change (Pi.single v a : localBrauerClasses K) w =
    numberFieldLocalBrauerDFinsuppSingle K v a w
  by_cases hwv : w = v
  · subst w
    rw [Pi.single_eq_same]
    simp [numberFieldLocalBrauerDFinsuppSingle]
  · rw [Pi.single_eq_of_ne hwv]
    simp [numberFieldLocalBrauerDFinsuppSingle, DFinsupp.single_apply, Ne.symm hwv]

/-- Number-field restricted local Brauer classes agree globally exactly when they agree at every
place. -/
theorem numberFieldRestrictedLocalBrauer_congr_hasse_iff
    (K : Type u) [Field K] [NumberField K]
    (x y : RestrictedLocalBrauerClasses K) :
    x = y ↔ ∀ v, x.toLocalBrauerClasses v = y.toLocalBrauerClasses v := by
  constructor
  · intro h
    subst y
    exact fun _ => rfl
  · intro h
    apply RestrictedLocalBrauerClasses.ext
    funext v
    exact h v

/-- A number-field restricted local Brauer family is zero exactly when every local class is
split. -/
theorem numberFieldRestrictedLocalBrauer_eq_zero_hasse_iff
    (K : Type u) [Field K] [NumberField K]
    (x : RestrictedLocalBrauerClasses K) :
    x = 0 ↔ ∀ v,
      x.toLocalBrauerClasses v = brauerSplitClass (completion K v) := by
  constructor
  · intro h
    subst x
    exact fun _ => rfl
  · intro h
    apply RestrictedLocalBrauerClasses.ext
    funext v
    exact h v

/-- The nonsplit support is exactly the nonzero support of the dependent finite-support
coordinates. -/
theorem numberFieldRestrictedLocalBrauer_nonSplitSupport_eq_dfinsuppSupportSet
    (K : Type u) [Field K] [NumberField K]
    (x : RestrictedLocalBrauerClasses K) :
    {v | numberFieldRestrictedLocalBrauerDFinsuppEquiv K x v ≠ 0} =
      {v | x.toLocalBrauerClasses v ≠ brauerSplitClass (completion K v)} := rfl

/-! ## Rational function fields -/

/-- Coordinate map from restricted rational-function local Brauer classes to dependent
finite-support families. -/
noncomputable def rationalFunctionRestrictedLocalBrauerToDFinsuppAddHom
    (F : Type u) [Field F] [Finite F] :
    RationalFunctionRestrictedLocalBrauerClasses F →+
      (Π₀ v : RationalFunctionPlace F,
        BrauerGroup (rationalFunctionCompletion F v)) := by
  classical
  refine
    { toFun := fun x =>
        { toFun := x.toLocalBrauerClasses
          support' := Trunc.mk ⟨x.finite_nonSplit_support.toFinset.1, fun v => by
            by_cases hv : x.toLocalBrauerClasses v = 0
            · exact Or.inr hv
            · exact Or.inl (by
                have hv' : v ∈ {w | x.toLocalBrauerClasses w ≠
                    brauerSplitClass (rationalFunctionCompletion F w)} := by
                  change x.toLocalBrauerClasses v ≠ 0
                  exact hv
                have hvfin : v ∈ x.finite_nonSplit_support.toFinset := by
                  simpa only [Set.Finite.mem_toFinset] using hv'
                exact hvfin)⟩ }
      map_zero' := ?_
      map_add' := ?_ }
  · apply DFinsupp.ext
    intro v
    rfl
  · intro x y
    apply DFinsupp.ext
    intro v
    rfl

/-- Restricted rational-function local Brauer coordinates are faithful. -/
theorem rationalFunctionRestrictedLocalBrauerToDFinsuppAddHom_injective
    (F : Type u) [Field F] [Finite F] :
    Function.Injective (rationalFunctionRestrictedLocalBrauerToDFinsuppAddHom F) := by
  intro x y hxy
  apply RationalFunctionRestrictedLocalBrauerClasses.ext
  funext v
  exact DFunLike.congr_fun hxy v

/-- Every dependent finite-support family of rational-function local Brauer classes is a
restricted local family. -/
theorem rationalFunctionRestrictedLocalBrauerToDFinsuppAddHom_surjective
    (F : Type u) [Field F] [Finite F] :
    Function.Surjective (rationalFunctionRestrictedLocalBrauerToDFinsuppAddHom F) := by
  classical
  intro x
  let y : RationalFunctionRestrictedLocalBrauerClasses F :=
    { toLocalBrauerClasses := fun v => x v
      finite_nonSplit_support := by
        change {v | x v ≠ 0}.Finite
        have heq : (↑x.support : Set (RationalFunctionPlace F)) =
            {v | x v ≠ 0} := by
          ext v
          change v ∈ x.support ↔ x v ≠ 0
          exact DFinsupp.mem_support_iff
        rw [← heq]
        exact x.support.finite_toSet }
  refine ⟨y, ?_⟩
  apply DFinsupp.ext
  intro v
  rfl

/-- The rational-function restricted local Brauer group is the dependent direct sum of its local
Brauer groups. -/
noncomputable def rationalFunctionRestrictedLocalBrauerDFinsuppEquiv
    (F : Type u) [Field F] [Finite F] :
    RationalFunctionRestrictedLocalBrauerClasses F ≃+
      (Π₀ v : RationalFunctionPlace F,
        BrauerGroup (rationalFunctionCompletion F v)) :=
  AddEquiv.ofBijective (rationalFunctionRestrictedLocalBrauerToDFinsuppAddHom F)
    ⟨rationalFunctionRestrictedLocalBrauerToDFinsuppAddHom_injective F,
      rationalFunctionRestrictedLocalBrauerToDFinsuppAddHom_surjective F⟩

/-- The rational-function dependent-direct-sum equivalence evaluates by the original local
coordinate. -/
@[simp] theorem rationalFunctionRestrictedLocalBrauerDFinsuppEquiv_apply
    (F : Type u) [Field F] [Finite F]
    (x : RationalFunctionRestrictedLocalBrauerClasses F) (v : RationalFunctionPlace F) :
    rationalFunctionRestrictedLocalBrauerDFinsuppEquiv F x v =
      x.toLocalBrauerClasses v := rfl

/-- Canonical one-place dependent family for rational-function local Brauer classes. -/
noncomputable def rationalFunctionLocalBrauerDFinsuppSingle
    (F : Type u) [Field F] [Finite F]
    (v : RationalFunctionPlace F) (a : BrauerGroup (rationalFunctionCompletion F v)) :
    (Π₀ w : RationalFunctionPlace F,
      BrauerGroup (rationalFunctionCompletion F w)) := by
  classical
  exact DFinsupp.single v a

/-- A rational-function restricted one-place section is literally a dependent finitely supported
singleton. -/
theorem rationalFunctionRestrictedLocalBrauerDFinsuppEquiv_single
    (F : Type u) [Field F] [Finite F]
    (v : RationalFunctionPlace F) (a : BrauerGroup (rationalFunctionCompletion F v)) :
    rationalFunctionRestrictedLocalBrauerDFinsuppEquiv F
        (rationalFunctionRestrictedLocalBrauerSingle F v a) =
      rationalFunctionLocalBrauerDFinsuppSingle F v a := by
  classical
  apply DFinsupp.ext
  intro w
  change (Pi.single v a : rationalFunctionLocalBrauerClasses F) w =
    rationalFunctionLocalBrauerDFinsuppSingle F v a w
  by_cases hwv : w = v
  · subst w
    rw [Pi.single_eq_same]
    simp [rationalFunctionLocalBrauerDFinsuppSingle]
  · rw [Pi.single_eq_of_ne hwv]
    simp [rationalFunctionLocalBrauerDFinsuppSingle, DFinsupp.single_apply, Ne.symm hwv]

/-- Rational-function restricted local Brauer classes agree globally exactly when they agree at
every place. -/
theorem rationalFunctionRestrictedLocalBrauer_congr_hasse_iff
    (F : Type u) [Field F] [Finite F]
    (x y : RationalFunctionRestrictedLocalBrauerClasses F) :
    x = y ↔ ∀ v, x.toLocalBrauerClasses v = y.toLocalBrauerClasses v := by
  constructor
  · intro h
    subst y
    exact fun _ => rfl
  · intro h
    apply RationalFunctionRestrictedLocalBrauerClasses.ext
    funext v
    exact h v

/-- A rational-function restricted local Brauer family is zero exactly when every local class is
split. -/
theorem rationalFunctionRestrictedLocalBrauer_eq_zero_hasse_iff
    (F : Type u) [Field F] [Finite F]
    (x : RationalFunctionRestrictedLocalBrauerClasses F) :
    x = 0 ↔ ∀ v,
      x.toLocalBrauerClasses v = brauerSplitClass (rationalFunctionCompletion F v) := by
  constructor
  · intro h
    subst x
    exact fun _ => rfl
  · intro h
    apply RationalFunctionRestrictedLocalBrauerClasses.ext
    funext v
    exact h v

/-- Rational-function nonsplit support is exactly the nonzero support of the dependent
finite-support coordinates. -/
theorem rationalFunctionRestrictedLocalBrauer_nonSplitSupport_eq_dfinsuppSupportSet
    (F : Type u) [Field F] [Finite F]
    (x : RationalFunctionRestrictedLocalBrauerClasses F) :
    {v | rationalFunctionRestrictedLocalBrauerDFinsuppEquiv F x v ≠ 0} =
      {v | x.toLocalBrauerClasses v ≠
        brauerSplitClass (rationalFunctionCompletion F v)} := rfl

end GaloisForLFunctions.HTGeometry.ABHN
