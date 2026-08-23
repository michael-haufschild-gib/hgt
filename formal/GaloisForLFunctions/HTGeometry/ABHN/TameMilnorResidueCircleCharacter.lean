/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.FiniteMilnorKTwoCharacterReciprocity
import GaloisForLFunctions.HTGeometry.ABHN.ConcreteTameMilnorInvariant

/-!
# Residue-normalized circle characters for local tame Milnor `K₂`

The tame residue of a nonarchimedean local field lands in the first Milnor `K` group of its finite
residue field.  Applying that residue field's canonical finite-field character gives an intrinsic
local phase.  This character is faithful, but it is not automatically the norm-normalized character
used by global projective-line reciprocity: independent cyclic-coordinate choices need not commute
with finite-field norms.

`RationalFunctionAdicNormTameCharacter` constructs the globally normalized completed-local phase.
This module makes no Milnor--Brauer claim.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

open IsDedekindDomain
open scoped LaurentSeries Polynomial ValuativeRel

universe u

/-- The finite-field circle character of the degree-two tame residue. -/
noncomputable def nonarchimedeanLocalFieldTameResidueStdAddChar
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : AddChar (MilnorKDeg K 2) ℂ :=
  finiteMilnorKOneStdAddChar
    (IsLocalRing.ResidueField (nonarchimedeanLocalFieldIntValuation K).valuationSubring) |>.compAddMonoidHom
      (nonarchimedeanLocalFieldTameMilnorResidue K)

/-- The residue-normalized local phase is one exactly on the zero-tame-residue kernel. -/
theorem nonarchimedeanLocalFieldTameResidueStdAddChar_eq_one_iff_mem_tameKernel
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : MilnorKDeg K 2) :
    nonarchimedeanLocalFieldTameResidueStdAddChar K x = 1 ↔
      x ∈ (nonarchimedeanLocalFieldTameMilnorResidue K).ker := by
  change finiteMilnorKOneStdAddChar _ (nonarchimedeanLocalFieldTameMilnorResidue K x) = 1 ↔ _
  rw [finiteMilnorKOneStdAddChar_eq_one_iff_eq_zero]
  rfl

/-- Two residue-normalized local phases agree exactly when their difference has zero tame
residue. -/
theorem nonarchimedeanLocalFieldTameResidueStdAddChar_eq_iff_sub_mem_tameKernel
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x y : MilnorKDeg K 2) :
    nonarchimedeanLocalFieldTameResidueStdAddChar K x =
      nonarchimedeanLocalFieldTameResidueStdAddChar K y ↔
      x - y ∈ (nonarchimedeanLocalFieldTameMilnorResidue K).ker := by
  constructor
  · intro hphase
    change nonarchimedeanLocalFieldTameMilnorResidue K (x - y) = 0
    rw [map_sub]
    apply sub_eq_zero.mpr
    apply finiteMilnorKOneStdAddChar_injective
    exact hphase
  · intro hkernel
    change finiteMilnorKOneStdAddChar _ (nonarchimedeanLocalFieldTameMilnorResidue K x) =
      finiteMilnorKOneStdAddChar _ (nonarchimedeanLocalFieldTameMilnorResidue K y)
    have hresidue : nonarchimedeanLocalFieldTameMilnorResidue K x =
        nonarchimedeanLocalFieldTameMilnorResidue K y := by
      apply sub_eq_zero.mp
      rw [← (nonarchimedeanLocalFieldTameMilnorResidue K).map_sub]
      exact hkernel
    exact congrArg (finiteMilnorKOneStdAddChar _) hresidue

/-- At a finite number-field place, the residue-normalized phase is one exactly at zero tame
residue. -/
theorem numberFieldFinitePlace_tameResidueStdAddChar_eq_one_iff_mem_tameKernel
    (K : Type u) [Field K] [NumberField K] (v : NumberField.FinitePlace K)
    (x : MilnorKDeg (completion K (.finite v)) 2) :
    nonarchimedeanLocalFieldTameResidueStdAddChar (completion K (.finite v)) x = 1 ↔
      x ∈ (nonarchimedeanLocalFieldTameMilnorResidue (completion K (.finite v))).ker :=
  nonarchimedeanLocalFieldTameResidueStdAddChar_eq_one_iff_mem_tameKernel
    (completion K (.finite v)) x

/-- At a finite place of `F(t)`, the residue-normalized phase is one exactly at zero tame
residue. -/
theorem rationalFunctionFinitePlace_tameResidueStdAddChar_eq_one_iff_mem_tameKernel
    (F : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X])
    (x : MilnorKDeg (rationalFunctionCompletion F (.finite v)) 2) :
    nonarchimedeanLocalFieldTameResidueStdAddChar
      (rationalFunctionCompletion F (.finite v)) x = 1 ↔
      x ∈ (nonarchimedeanLocalFieldTameMilnorResidue
        (rationalFunctionCompletion F (.finite v))).ker :=
  nonarchimedeanLocalFieldTameResidueStdAddChar_eq_one_iff_mem_tameKernel
    (rationalFunctionCompletion F (.finite v)) x

/-- At the infinite place of `F(t)`, the residue-normalized phase is one exactly at zero tame
residue. -/
theorem rationalFunctionInfinitePlace_tameResidueStdAddChar_eq_one_iff_mem_tameKernel
    (F : Type u) [Field F] [Finite F]
    (x : MilnorKDeg (rationalFunctionCompletion F .infinite) 2) :
    nonarchimedeanLocalFieldTameResidueStdAddChar
      (rationalFunctionCompletion F .infinite) x = 1 ↔
      x ∈ (nonarchimedeanLocalFieldTameMilnorResidue
        (rationalFunctionCompletion F .infinite)).ker :=
  nonarchimedeanLocalFieldTameResidueStdAddChar_eq_one_iff_mem_tameKernel
    (rationalFunctionCompletion F .infinite) x

/-- In the Laurent-series local model, the residue-normalized phase is one exactly at zero tame
residue. -/
theorem laurentSeries_tameResidueStdAddChar_eq_one_iff_mem_tameKernel
    (F : Type u) [Field F] [Finite F] (x : MilnorKDeg F⸨X⸩ 2) :
    nonarchimedeanLocalFieldTameResidueStdAddChar F⸨X⸩ x = 1 ↔
      x ∈ (nonarchimedeanLocalFieldTameMilnorResidue F⸨X⸩).ker :=
  nonarchimedeanLocalFieldTameResidueStdAddChar_eq_one_iff_mem_tameKernel F⸨X⸩ x

end

end GaloisForLFunctions.HTGeometry.ABHN
