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

universe u v

/-- The residue Brauer group of every nonarchimedean local field is trivial. -/
theorem nonarchimedeanLocalField_residueBrauerGroup_subsingleton
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    Subsingleton (BrauerGroup.{u, u} 𝓀[K]) :=
  finiteField_brauerGroup_subsingleton _

/-- Every additive observable of a nonarchimedean residue Brauer group vanishes.  In particular,
no nonzero local source term can factor through that residue Brauer group alone. -/
theorem nonarchimedeanLocalField_residueBrauerAddHom_eq_zero
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (A : Type v) [AddCommMonoid A] (f : BrauerGroup.{u, u} 𝓀[K] →+ A) :
    f = 0 := by
  letI : Subsingleton (BrauerGroup.{u, u} 𝓀[K]) :=
    nonarchimedeanLocalField_residueBrauerGroup_subsingleton K
  ext x
  rw [Subsingleton.elim x 0, f.map_zero]
  rfl

/-- A nonzero local source value cannot factor through the residue Brauer group of a
nonarchimedean local field. -/
theorem nonarchimedeanLocalField_residueBrauerAddHom_apply_ne_of_ne_zero
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (A : Type v) [AddCommMonoid A] (f : BrauerGroup.{u, u} 𝓀[K] →+ A)
    (x : BrauerGroup.{u, u} 𝓀[K]) (y : A) (hy : y ≠ 0) :
    f x ≠ y := by
  have hzero : f x = 0 := by
    rw [nonarchimedeanLocalField_residueBrauerAddHom_eq_zero K A f]
    rfl
  intro h
  apply hy
  calc
    y = f x := h.symm
    _ = 0 := hzero

/-- The residue Brauer invariant of a nonarchimedean local field is canonically zero. -/
noncomputable def nonarchimedeanLocalField_residueBrauerInvariantAddEquivBot
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    BrauerGroup.{u, u} 𝓀[K] ≃+ (⊥ : AddSubgroup RatModInt) :=
  finiteFieldBrauerInvariantAddEquivBot _

end GaloisForLFunctions.HTGeometry.ABHN
