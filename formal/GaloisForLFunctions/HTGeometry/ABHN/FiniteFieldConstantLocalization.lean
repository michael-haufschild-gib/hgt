/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.RestrictedLocalization
import GaloisForLFunctions.HTGeometry.ABHN.FiniteFieldBrauer

/-!
# Localization of finite-field constant Brauer classes

A Brauer class over a finite field is split.  Its scalar extension to the rational function
field therefore has split localization at every global-function-field place.  This provides a
closed Hasse-style local profile and a concrete family in the restricted local Brauer group.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

universe u

/-- The localization of every finite-field constant Brauer class on `F(t)` is everywhere split. -/
theorem rationalFunctionLocalBrauerMap_constant_eq_split
    (F : Type u) [Field F] [Finite F] (x : BrauerGroup.{u, u} F) :
    rationalFunctionLocalBrauerMap F (scalarExtensionBrauerMap F (RatFunc F) x) =
      (rationalFunctionRestrictedSplitClass F).toLocalBrauerClasses := by
  rw [finiteField_scalarExtensionBrauerMap_eq_split F (RatFunc F) x]
  exact rationalFunctionLocalBrauerMap_split F

/-- A finite-field constant Brauer class on `F(t)` has finite nonsplit local support. -/
theorem rationalFunction_constantBrauer_mem_finiteSupport
    (F : Type u) [Field F] [Finite F] (x : BrauerGroup.{u, u} F) :
    scalarExtensionBrauerMap F (RatFunc F) x ∈ rationalFunctionFiniteSupportBrauerSubgroup F := by
  change RationalFunctionHasFiniteNonSplitSupport F
    (rationalFunctionLocalBrauerMap F (scalarExtensionBrauerMap F (RatFunc F) x))
  rw [rationalFunctionLocalBrauerMap_constant_eq_split]
  exact (rationalFunctionRestrictedSplitClass F).finite_nonSplit_support

/-- The restricted local family attached to a finite-field constant Brauer class on `F(t)`. -/
noncomputable def rationalFunctionConstantRestrictedLocalBrauer
    (F : Type u) [Field F] [Finite F] (x : BrauerGroup.{u, u} F) :
    RationalFunctionRestrictedLocalBrauerClasses F :=
  ⟨rationalFunctionLocalBrauerMap F (scalarExtensionBrauerMap F (RatFunc F) x),
    rationalFunction_constantBrauer_mem_finiteSupport F x⟩

/-- The restricted local family of every finite-field constant Brauer class is split. -/
theorem rationalFunctionConstantRestrictedLocalBrauer_eq_split
    (F : Type u) [Field F] [Finite F] (x : BrauerGroup.{u, u} F) :
    rationalFunctionConstantRestrictedLocalBrauer F x = rationalFunctionRestrictedSplitClass F := by
  apply RationalFunctionRestrictedLocalBrauerClasses.ext
  exact rationalFunctionLocalBrauerMap_constant_eq_split F x

end

end GaloisForLFunctions.HTGeometry.ABHN
