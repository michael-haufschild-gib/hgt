/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.ConcreteTameMilnorInvariant
import GaloisForLFunctions.HTGeometry.ABHN.RatModIntCircleCharacter

/-!
# Circle characters for tame local Milnor invariants

The finite cyclic tame quotient of local Milnor `K₂` has a canonical faithful `ℚ/ℤ` invariant.
Composing it with the standard circle character gives a local unit-circle phase.  This module
proves that phase one, and equality of two phases, detect precisely the tame-residue kernel.
It applies the construction at finite number-field places, at all finite and infinite places of
`F(t)`, and at Laurent-series local fields.

This is a local tame Milnor invariant, not an identification with a local Brauer invariant.
The Milnor--Brauer and local-class-field-theory comparison remains a separate bridge.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

open IsDedekindDomain
open scoped LaurentSeries Polynomial ValuativeRel

universe u

/-- The faithful unit-circle phase of the finite tame quotient of a nonarchimedean local field. -/
noncomputable def nonarchimedeanLocalFieldTameMilnorQuotientStdAddChar
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    AddChar (MilnorKDeg K 2 ⧸ (nonarchimedeanLocalFieldTameMilnorResidue K).ker) ℂ :=
  ratModIntStdAddChar.compAddMonoidHom (nonarchimedeanLocalFieldTameMilnorInvariant K)

/-- The tame quotient phase is faithful. -/
theorem nonarchimedeanLocalFieldTameMilnorQuotientStdAddChar_injective
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    Function.Injective (nonarchimedeanLocalFieldTameMilnorQuotientStdAddChar K) :=
  ratModIntStdAddChar_injective.comp
    (nonarchimedeanLocalFieldTameMilnorInvariant_injective K)

/-- The raw local phase is the quotient phase after the tame quotient map. -/
noncomputable def nonarchimedeanLocalFieldTameMilnorStdAddChar
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : AddChar (MilnorKDeg K 2) ℂ :=
  ratModIntStdAddChar.compAddMonoidHom (nonarchimedeanLocalFieldTameMilnorInvariantRaw K)

/-- Evaluating the raw phase is evaluating the quotient phase on the quotient class. -/
theorem nonarchimedeanLocalFieldTameMilnorStdAddChar_eq_quotient_phase
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : MilnorKDeg K 2) :
    nonarchimedeanLocalFieldTameMilnorStdAddChar K x =
      nonarchimedeanLocalFieldTameMilnorQuotientStdAddChar K
        (QuotientAddGroup.mk x) := rfl

/-- The local tame phase is the global `ℚ/ℤ` circle character after the raw tame invariant. -/
theorem nonarchimedeanLocalFieldTameMilnorStdAddChar_eq_global_character
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : MilnorKDeg K 2) :
    nonarchimedeanLocalFieldTameMilnorStdAddChar K x =
      ratModIntStdAddChar (nonarchimedeanLocalFieldTameMilnorInvariantRaw K x) := rfl

/-- The local tame phase is one exactly on the zero-tame-residue kernel. -/
theorem nonarchimedeanLocalFieldTameMilnorStdAddChar_eq_one_iff_mem_tameKernel
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : MilnorKDeg K 2) :
    nonarchimedeanLocalFieldTameMilnorStdAddChar K x = 1 ↔
      x ∈ (nonarchimedeanLocalFieldTameMilnorResidue K).ker := by
  constructor
  · intro hx
    have hraw : nonarchimedeanLocalFieldTameMilnorInvariantRaw K x = 0 :=
      (ratModIntStdAddChar_eq_one_iff_eq_zero _).mp hx
    have hker : x ∈ (nonarchimedeanLocalFieldTameMilnorInvariantRaw K).ker := hraw
    rwa [nonarchimedeanLocalFieldTameMilnorInvariantRaw_ker K] at hker
  · intro hx
    have hker : x ∈ (nonarchimedeanLocalFieldTameMilnorInvariantRaw K).ker := by
      rwa [nonarchimedeanLocalFieldTameMilnorInvariantRaw_ker K]
    exact (ratModIntStdAddChar_eq_one_iff_eq_zero _).mpr hker

/-- Two raw tame phases agree exactly when their difference has zero tame residue. -/
theorem nonarchimedeanLocalFieldTameMilnorStdAddChar_eq_iff_sub_mem_tameKernel
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x y : MilnorKDeg K 2) :
    nonarchimedeanLocalFieldTameMilnorStdAddChar K x =
      nonarchimedeanLocalFieldTameMilnorStdAddChar K y ↔
      x - y ∈ (nonarchimedeanLocalFieldTameMilnorResidue K).ker := by
  constructor
  · intro hphase
    rw [← nonarchimedeanLocalFieldTameMilnorInvariantRaw_ker K]
    change nonarchimedeanLocalFieldTameMilnorInvariantRaw K (x - y) = 0
    rw [map_sub]
    apply sub_eq_zero.mpr
    apply ratModIntStdAddChar_injective
    exact hphase
  · intro hkernel
    change ratModIntStdAddChar (nonarchimedeanLocalFieldTameMilnorInvariantRaw K x) =
      ratModIntStdAddChar (nonarchimedeanLocalFieldTameMilnorInvariantRaw K y)
    have hraw : x - y ∈ (nonarchimedeanLocalFieldTameMilnorInvariantRaw K).ker := by
      rwa [nonarchimedeanLocalFieldTameMilnorInvariantRaw_ker K]
    have hinvariant : nonarchimedeanLocalFieldTameMilnorInvariantRaw K x =
        nonarchimedeanLocalFieldTameMilnorInvariantRaw K y := by
      apply sub_eq_zero.mp
      rw [← (nonarchimedeanLocalFieldTameMilnorInvariantRaw K).map_sub]
      exact hraw
    exact congrArg ratModIntStdAddChar hinvariant

/-- At a finite number-field place, phase one is exactly zero tame residue. -/
theorem numberFieldFinitePlace_tameMilnorStdAddChar_eq_one_iff_mem_tameKernel
    (K : Type u) [Field K] [NumberField K] (v : NumberField.FinitePlace K)
    (x : MilnorKDeg (completion K (.finite v)) 2) :
    nonarchimedeanLocalFieldTameMilnorStdAddChar (completion K (.finite v)) x = 1 ↔
      x ∈ (nonarchimedeanLocalFieldTameMilnorResidue (completion K (.finite v))).ker :=
  nonarchimedeanLocalFieldTameMilnorStdAddChar_eq_one_iff_mem_tameKernel
    (completion K (.finite v)) x

/-- At a finite place of `F(t)`, phase one is exactly zero tame residue. -/
theorem rationalFunctionFinitePlace_tameMilnorStdAddChar_eq_one_iff_mem_tameKernel
    (F : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X])
    (x : MilnorKDeg (rationalFunctionCompletion F (.finite v)) 2) :
    nonarchimedeanLocalFieldTameMilnorStdAddChar
      (rationalFunctionCompletion F (.finite v)) x = 1 ↔
      x ∈ (nonarchimedeanLocalFieldTameMilnorResidue
        (rationalFunctionCompletion F (.finite v))).ker :=
  nonarchimedeanLocalFieldTameMilnorStdAddChar_eq_one_iff_mem_tameKernel
    (rationalFunctionCompletion F (.finite v)) x

/-- At the infinite place of `F(t)`, phase one is exactly zero tame residue. -/
theorem rationalFunctionInfinitePlace_tameMilnorStdAddChar_eq_one_iff_mem_tameKernel
    (F : Type u) [Field F] [Finite F]
    (x : MilnorKDeg (rationalFunctionCompletion F .infinite) 2) :
    nonarchimedeanLocalFieldTameMilnorStdAddChar
      (rationalFunctionCompletion F .infinite) x = 1 ↔
      x ∈ (nonarchimedeanLocalFieldTameMilnorResidue
        (rationalFunctionCompletion F .infinite)).ker :=
  nonarchimedeanLocalFieldTameMilnorStdAddChar_eq_one_iff_mem_tameKernel
    (rationalFunctionCompletion F .infinite) x

/-- In the Laurent-series local model, phase one is exactly zero tame residue. -/
theorem laurentSeries_tameMilnorStdAddChar_eq_one_iff_mem_tameKernel
    (F : Type u) [Field F] [Finite F] (x : MilnorKDeg F⸨X⸩ 2) :
    nonarchimedeanLocalFieldTameMilnorStdAddChar F⸨X⸩ x = 1 ↔
      x ∈ (nonarchimedeanLocalFieldTameMilnorResidue F⸨X⸩).ker :=
  nonarchimedeanLocalFieldTameMilnorStdAddChar_eq_one_iff_mem_tameKernel F⸨X⸩ x

end

end GaloisForLFunctions.HTGeometry.ABHN
