import GaloisForLFunctions.HTGeometry.ABHN.LocalScalarExtension
import GaloisForLFunctions.HTGeometry.ABHN.RestrictedBrauerGroup
import GaloisForLFunctions.HTGeometry.ABHN.RestrictedInvariantSum

/-!
# Restricted global-to-local Brauer maps

This module records the exact part of the ABHN localization map available before finite
ramification is proved: every global Brauer class whose localizations have established finite
nonsplit support maps into the restricted local Brauer group.  The missing finite-ramification
theorem is precisely the statement that these subgroups are the whole global Brauer groups.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

universe u

/-- Global Brauer classes over a number field whose scalar extensions have finite nonsplit local
support.  Finite ramification in ABHN identifies this subgroup with the full Brauer group. -/
noncomputable def numberFieldFiniteSupportBrauerSubgroup (K : Type u) [Field K] [NumberField K] :
    AddSubgroup (BrauerGroup.{u, u} K) where
  carrier := {x | HasFiniteNonSplitSupport K (numberFieldLocalBrauerMap K x)}
  zero_mem' := by
    change HasFiniteNonSplitSupport K ((numberFieldLocalBrauerAddHom K) 0)
    rw [(numberFieldLocalBrauerAddHom K).map_zero]
    exact (restrictedSplitClass K).finite_nonSplit_support
  add_mem' := by
    intro x y hx hy
    change HasFiniteNonSplitSupport K ((numberFieldLocalBrauerAddHom K) (x + y))
    rw [(numberFieldLocalBrauerAddHom K).map_add]
    exact hasFiniteNonSplitSupport_add K _ _ hx hy
  neg_mem' := by
    intro x hx
    change HasFiniteNonSplitSupport K ((numberFieldLocalBrauerAddHom K) (-x))
    rw [(numberFieldLocalBrauerAddHom K).map_neg]
    exact hasFiniteNonSplitSupport_neg K _ hx

/-- Number-field localization restricted to global classes with proved finite nonsplit support. -/
noncomputable def numberFieldRestrictedLocalBrauerAddHom (K : Type u) [Field K] [NumberField K] :
    numberFieldFiniteSupportBrauerSubgroup K →+ RestrictedLocalBrauerClasses K where
  toFun x := ⟨numberFieldLocalBrauerMap K x, x.property⟩
  map_zero' := by
    apply RestrictedLocalBrauerClasses.ext
    exact (numberFieldLocalBrauerAddHom K).map_zero
  map_add' x y := by
    apply RestrictedLocalBrauerClasses.ext
    exact (numberFieldLocalBrauerAddHom K).map_add x y

/-- The restricted localization map retains the original family of local Brauer classes. -/
theorem numberFieldRestrictedLocalBrauerAddHom_apply (K : Type u) [Field K] [NumberField K]
    (x : numberFieldFiniteSupportBrauerSubgroup K) :
    (numberFieldRestrictedLocalBrauerAddHom K x).toLocalBrauerClasses =
      numberFieldLocalBrauerMap K x := rfl

/-- The global invariant sum on the finite-support part of a number-field Brauer group. -/
noncomputable def numberFieldFiniteSupportGlobalInvariantSum
    (K : Type u) [Field K] [NumberField K]
    (invariant : ∀ v : NumberFieldPlace K, BrauerGroup (completion K v) →+ RatModInt) :
    numberFieldFiniteSupportBrauerSubgroup K →+ RatModInt :=
  (numberFieldRestrictedInvariantSum K invariant).comp (numberFieldRestrictedLocalBrauerAddHom K)

/-- Global Brauer classes over `F(t)` with established finite nonsplit local support.  For the
usual global-function-field ABHN theorem, finite ramification says this is the whole group. -/
noncomputable def rationalFunctionFiniteSupportBrauerSubgroup (F : Type u) [Field F] [Finite F] :
    AddSubgroup (BrauerGroup.{u, u} (RatFunc F)) where
  carrier := {x | RationalFunctionHasFiniteNonSplitSupport F (rationalFunctionLocalBrauerMap F x)}
  zero_mem' := by
    change RationalFunctionHasFiniteNonSplitSupport F ((rationalFunctionLocalBrauerAddHom F) 0)
    rw [(rationalFunctionLocalBrauerAddHom F).map_zero]
    exact (rationalFunctionRestrictedSplitClass F).finite_nonSplit_support
  add_mem' := by
    intro x y hx hy
    change RationalFunctionHasFiniteNonSplitSupport F ((rationalFunctionLocalBrauerAddHom F) (x + y))
    rw [(rationalFunctionLocalBrauerAddHom F).map_add]
    exact rationalFunctionHasFiniteNonSplitSupport_add F _ _ hx hy
  neg_mem' := by
    intro x hx
    change RationalFunctionHasFiniteNonSplitSupport F ((rationalFunctionLocalBrauerAddHom F) (-x))
    rw [(rationalFunctionLocalBrauerAddHom F).map_neg]
    exact rationalFunctionHasFiniteNonSplitSupport_neg F _ hx

/-- Rational-function-field localization restricted to global classes with proved finite
nonsplit support. -/
noncomputable def rationalFunctionRestrictedLocalBrauerAddHom
    (F : Type u) [Field F] [Finite F] :
    rationalFunctionFiniteSupportBrauerSubgroup F →+
      RationalFunctionRestrictedLocalBrauerClasses F where
  toFun x := ⟨rationalFunctionLocalBrauerMap F x, x.property⟩
  map_zero' := by
    apply RationalFunctionRestrictedLocalBrauerClasses.ext
    exact (rationalFunctionLocalBrauerAddHom F).map_zero
  map_add' x y := by
    apply RationalFunctionRestrictedLocalBrauerClasses.ext
    exact (rationalFunctionLocalBrauerAddHom F).map_add x y

/-- The restricted rational-function localization map retains the original local family. -/
theorem rationalFunctionRestrictedLocalBrauerAddHom_apply
    (F : Type u) [Field F] [Finite F] (x : rationalFunctionFiniteSupportBrauerSubgroup F) :
    (rationalFunctionRestrictedLocalBrauerAddHom F x).toLocalBrauerClasses =
      rationalFunctionLocalBrauerMap F x := rfl

/-- The global invariant sum on the finite-support part of a rational-function Brauer group. -/
noncomputable def rationalFunctionFiniteSupportGlobalInvariantSum
    (F : Type u) [Field F] [Finite F]
    (invariant : ∀ v : RationalFunctionPlace F,
      BrauerGroup (rationalFunctionCompletion F v) →+ RatModInt) :
    rationalFunctionFiniteSupportBrauerSubgroup F →+ RatModInt :=
  (rationalFunctionRestrictedInvariantSum F invariant).comp
    (rationalFunctionRestrictedLocalBrauerAddHom F)

end

end GaloisForLFunctions.HTGeometry.ABHN
