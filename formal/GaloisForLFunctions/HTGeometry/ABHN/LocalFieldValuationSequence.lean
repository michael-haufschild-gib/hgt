/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.LocalValuationSequence
import GaloisForLFunctions.HTGeometry.ABHN.LaurentSeriesFiniteLocalField
import GaloisForLFunctions.HTGeometry.MilnorKResidueValuation

/-!
# Valuation sequence for the local function field `F((X))`

The standard Laurent-series local field has an onto integer valuation.  Choosing an element of
valuation `-1` produces the uniformizer required by `ResidueData`; hence its field units modulo
valuation-zero units are canonically the integer value group.

This remains a valuation-theoretic local-field input.  It does not construct the local reciprocity
map or identify the Brauer group with `ℚ/ℤ`.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped LaurentSeries PowerSeries ValuativeRel WithZero WithZeroMulInt

universe u

noncomputable section

/-- A chosen Laurent-series element with valuation `-1`. -/
noncomputable def laurentSeriesUniformizer (F : Type u) [Field F] : F⸨X⸩ :=
  (LaurentSeries.valuation_surjective F (WithZero.exp (-1 : ℤ))).choose

theorem laurentSeriesUniformizer_valuation (F : Type u) [Field F] :
    Valued.v (laurentSeriesUniformizer F) = WithZero.exp (-1 : ℤ) :=
  (LaurentSeries.valuation_surjective F (WithZero.exp (-1 : ℤ))).choose_spec

theorem laurentSeriesUniformizer_ne_zero (F : Type u) [Field F] :
    laurentSeriesUniformizer F ≠ 0 := by
  intro h
  have hval := laurentSeriesUniformizer_valuation F
  rw [h, map_zero] at hval
  exact absurd hval.symm (by simp [WithZero.exp])

/-- The selected Laurent-series uniformizer, made into a field unit. -/
noncomputable def laurentSeriesUniformizerUnit (F : Type u) [Field F] : F⸨X⸩ˣ :=
  Units.mk0 (laurentSeriesUniformizer F) (laurentSeriesUniformizer_ne_zero F)

theorem laurentSeriesUniformizer_tameVal (F : Type u) [Field F] :
    Multiplicative.toAdd (tameValHom
      (Valued.v : Valuation F⸨X⸩ ℤᵐ⁰) (laurentSeriesUniformizerUnit F)) = 1 := by
  have hcoe : ((tameUnzero (Valued.v : Valuation F⸨X⸩ ℤᵐ⁰)
      (laurentSeriesUniformizerUnit F) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) =
      ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) := by
    rw [coe_tameUnzero]
    exact laurentSeriesUniformizer_valuation F
  have hun : tameUnzero (Valued.v : Valuation F⸨X⸩ ℤᵐ⁰)
      (laurentSeriesUniformizerUnit F) = Multiplicative.ofAdd (-1 : ℤ) :=
    WithZero.coe_inj.1 hcoe
  rw [tameValHom_toAdd, hun]
  simp

/-- Residue data for the standard valuation on the local function field `F((X))`. -/
noncomputable def laurentSeriesResidueData (F : Type u) [Field F] :
    ResidueData F⸨X⸩
      (IsLocalRing.ResidueField
        (Valued.v : Valuation F⸨X⸩ ℤᵐ⁰).valuationSubring) :=
  residueDataOfValuation (Valued.v : Valuation F⸨X⸩ ℤᵐ⁰)
    (laurentSeriesUniformizerUnit F) (laurentSeriesUniformizer_tameVal F)

/-- The `F((X))` valuation is onto its integer value group. -/
theorem laurentSeriesValuation_surjective (F : Type u) [Field F] :
    Function.Surjective (laurentSeriesResidueData F).val :=
  residueDataValuation_surjective _

/-- Valuation-zero Laurent-series units are exactly the kernel of the integer valuation. -/
theorem laurentSeriesValuation_exact (F : Type u) [Field F] : Function.Exact
    (MonoidHom.toAdditive (laurentSeriesResidueData F).val.ker.subtype)
    (MonoidHom.toAdditive (laurentSeriesResidueData F).val) :=
  residueDataValuation_exact _

/-- The unit quotient of the local function field is the integer value group. -/
noncomputable def laurentSeriesQuotientKerValuationEquiv (F : Type u) [Field F] :
    F⸨X⸩ˣ ⧸ (laurentSeriesResidueData F).val.ker ≃* Multiplicative ℤ :=
  residueDataQuotientKerValuationEquiv _

end

end GaloisForLFunctions.HTGeometry.ABHN
