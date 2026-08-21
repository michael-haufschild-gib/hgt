/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanLocalFieldMilnorResidue
import GaloisForLFunctions.HTGeometry.ABHN.NumberFieldFiniteLocalField
import GaloisForLFunctions.HTGeometry.ABHN.RationalFunctionFiniteLocalField
import GaloisForLFunctions.HTGeometry.ABHN.LaurentSeriesFiniteLocalField

/-!
# Tame Milnor residues at concrete global-field local models

The generic nonarchimedean local-field tame sequence applies to every finite completion of a
number field, every finite completion of a rational function field over a finite field, and the
standard Laurent-series local model.  These are closed local `K₂` consequences; they do not
identify a completion at infinity of `F(t)` with its Laurent-series model and do not assert the
local Brauer invariant.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped LaurentSeries ValuativeRel WithZeroMulInt

universe u

/-- At every finite number-field place, the degree-two tame Milnor symbol is surjective. -/
theorem numberFieldFinitePlace_tameHom_surjective
    (K : Type u) [Field K] [NumberField K] (v : NumberField.FinitePlace K) :
    Function.Surjective
      (nonarchimedeanLocalFieldResidueData (completion K (.finite v))).tameHom :=
  nonarchimedeanLocalField_tameHom_surjective (completion K (.finite v))

/-- At every finite number-field place, the standard tame residue
`K₂ᴹ(Kᵥ) → K₁ᴹ(kᵥ)` is surjective. -/
theorem numberFieldFinitePlace_tameMilnorResidue_surjective
    (K : Type u) [Field K] [NumberField K] (v : NumberField.FinitePlace K) :
    Function.Surjective
      (nonarchimedeanLocalFieldTameMilnorResidue (completion K (.finite v))) :=
  nonarchimedeanLocalField_tameMilnorResidue_surjective (completion K (.finite v))

/-- The tame quotient at every finite number-field place is its finite residue-unit group. -/
noncomputable def numberFieldFinitePlaceTameHomQuotientKerEquiv
    (K : Type u) [Field K] [NumberField K] (v : NumberField.FinitePlace K) :
    MilnorKDeg (completion K (.finite v)) 2 ⧸
      (nonarchimedeanLocalFieldResidueData (completion K (.finite v))).tameHom.ker ≃+
        Additive (IsLocalRing.ResidueField
          (nonarchimedeanLocalFieldIntValuation (completion K (.finite v))).valuationSubring)ˣ :=
  nonarchimedeanLocalFieldTameHomQuotientKerEquiv (completion K (.finite v))

/-- The tame quotient at every finite number-field place is finite cyclic. -/
theorem numberFieldFinitePlaceTameHomQuotient_isAddCyclic
    (K : Type u) [Field K] [NumberField K] (v : NumberField.FinitePlace K) :
    IsAddCyclic (MilnorKDeg (completion K (.finite v)) 2 ⧸
      (nonarchimedeanLocalFieldResidueData (completion K (.finite v))).tameHom.ker) :=
  nonarchimedeanLocalFieldTameHomQuotient_isAddCyclic (completion K (.finite v))

/-- At every finite place of `F(t)`, the degree-two tame Milnor symbol is surjective. -/
theorem rationalFunctionFinitePlace_tameHom_surjective
    (F : Type u) [Field F] [Finite F]
    (v : IsDedekindDomain.HeightOneSpectrum (Polynomial F)) :
    Function.Surjective
      (nonarchimedeanLocalFieldResidueData
        (rationalFunctionCompletion F (.finite v))).tameHom :=
  nonarchimedeanLocalField_tameHom_surjective
    (rationalFunctionCompletion F (.finite v))

/-- At every finite place of `F(t)`, the standard tame residue
`K₂ᴹ(Kᵥ) → K₁ᴹ(kᵥ)` is surjective. -/
theorem rationalFunctionFinitePlace_tameMilnorResidue_surjective
    (F : Type u) [Field F] [Finite F]
    (v : IsDedekindDomain.HeightOneSpectrum (Polynomial F)) :
    Function.Surjective
      (nonarchimedeanLocalFieldTameMilnorResidue
        (rationalFunctionCompletion F (.finite v))) :=
  nonarchimedeanLocalField_tameMilnorResidue_surjective
    (rationalFunctionCompletion F (.finite v))

/-- The tame quotient at every finite place of `F(t)` is its finite residue-unit group. -/
noncomputable def rationalFunctionFinitePlaceTameHomQuotientKerEquiv
    (F : Type u) [Field F] [Finite F]
    (v : IsDedekindDomain.HeightOneSpectrum (Polynomial F)) :
    MilnorKDeg (rationalFunctionCompletion F (.finite v)) 2 ⧸
      (nonarchimedeanLocalFieldResidueData
        (rationalFunctionCompletion F (.finite v))).tameHom.ker ≃+
        Additive (IsLocalRing.ResidueField
          (nonarchimedeanLocalFieldIntValuation
            (rationalFunctionCompletion F (.finite v))).valuationSubring)ˣ :=
  nonarchimedeanLocalFieldTameHomQuotientKerEquiv
    (rationalFunctionCompletion F (.finite v))

/-- The tame quotient at every finite place of `F(t)` is finite cyclic. -/
theorem rationalFunctionFinitePlaceTameHomQuotient_isAddCyclic
    (F : Type u) [Field F] [Finite F]
    (v : IsDedekindDomain.HeightOneSpectrum (Polynomial F)) :
    IsAddCyclic (MilnorKDeg (rationalFunctionCompletion F (.finite v)) 2 ⧸
      (nonarchimedeanLocalFieldResidueData
        (rationalFunctionCompletion F (.finite v))).tameHom.ker) :=
  nonarchimedeanLocalFieldTameHomQuotient_isAddCyclic
    (rationalFunctionCompletion F (.finite v))

/-- The degree-two tame Milnor symbol of the standard finite-coefficient Laurent local field is
surjective. -/
theorem laurentSeries_tameHom_surjective
    (F : Type u) [Field F] [Finite F] :
    Function.Surjective (nonarchimedeanLocalFieldResidueData F⸨X⸩).tameHom :=
  nonarchimedeanLocalField_tameHom_surjective F⸨X⸩

/-- The standard tame residue `K₂ᴹ(F((X))) → K₁ᴹ(F)` is surjective. -/
theorem laurentSeries_tameMilnorResidue_surjective
    (F : Type u) [Field F] [Finite F] :
    Function.Surjective (nonarchimedeanLocalFieldTameMilnorResidue F⸨X⸩) :=
  nonarchimedeanLocalField_tameMilnorResidue_surjective F⸨X⸩

/-- The Laurent-series tame quotient is its finite coefficient-residue-unit group. -/
noncomputable def laurentSeriesTameHomQuotientKerEquiv
    (F : Type u) [Field F] [Finite F] :
    MilnorKDeg F⸨X⸩ 2 ⧸ (nonarchimedeanLocalFieldResidueData F⸨X⸩).tameHom.ker ≃+
      Additive (IsLocalRing.ResidueField
        (nonarchimedeanLocalFieldIntValuation F⸨X⸩).valuationSubring)ˣ :=
  nonarchimedeanLocalFieldTameHomQuotientKerEquiv F⸨X⸩

/-- The Laurent-series tame quotient is finite cyclic. -/
theorem laurentSeriesTameHomQuotient_isAddCyclic
    (F : Type u) [Field F] [Finite F] :
    IsAddCyclic (MilnorKDeg F⸨X⸩ 2 ⧸
      (nonarchimedeanLocalFieldResidueData F⸨X⸩).tameHom.ker) :=
  nonarchimedeanLocalFieldTameHomQuotient_isAddCyclic F⸨X⸩

end GaloisForLFunctions.HTGeometry.ABHN
