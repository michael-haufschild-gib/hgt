/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.FiniteFieldBrauer
import Mathlib.NumberTheory.LocalField.Basic

/-!
# Residue Brauer groups of nonarchimedean local fields

Every nonarchimedean local field has finite residue field.  Consequently its residue-field
Brauer group is trivial.  This is the residue term in the unramified local Brauer sequence;
it does not identify the Brauer group of the local field itself.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped ValuativeRel

universe u

/-- The residue Brauer group of every nonarchimedean local field is trivial. -/
theorem nonarchimedeanLocalField_residueBrauerGroup_subsingleton
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    Subsingleton (BrauerGroup.{u, u} 𝓀[K]) :=
  finiteField_brauerGroup_subsingleton _

/-- The residue Brauer invariant of a nonarchimedean local field is canonically zero. -/
noncomputable def nonarchimedeanLocalField_residueBrauerInvariantAddEquivBot
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    BrauerGroup.{u, u} 𝓀[K] ≃+ (⊥ : AddSubgroup RatModInt) :=
  finiteFieldBrauerInvariantAddEquivBot _

end GaloisForLFunctions.HTGeometry.ABHN
