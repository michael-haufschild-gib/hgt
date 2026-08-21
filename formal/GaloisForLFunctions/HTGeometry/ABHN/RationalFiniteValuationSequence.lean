/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.LocalValuationSequence
import GaloisForLFunctions.HTGeometry.ABHN.RationalFiniteLocalField
import GaloisForLFunctions.HTGeometry.MilnorKResidueValuation

/-!
# Valuation sequence at finite completions of `ℚ`

At a finite rational place, the image of a chosen global uniformizer in the adic completion is a
uniformizer for the completed valuation.  This yields residue data and the split unit/valuation
sequence for every finite completion of `ℚ`.

This packages a local input for class field theory.  It neither constructs local reciprocity nor
identifies the local Brauer group with `ℚ/ℤ`.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open IsDedekindDomain
open scoped WithZero WithZeroMulInt

noncomputable section

/-- The global chosen uniformizer embedded in the finite adic completion. -/
noncomputable def rationalFiniteAdicUniformizer (v : NumberField.FinitePlace ℚ) :
    v.maximalIdeal.adicCompletion ℚ :=
  NumberField.FinitePlace.embedding v.maximalIdeal (placeUniformizer ℚ v.maximalIdeal)

theorem rationalFiniteAdicUniformizer_valuation (v : NumberField.FinitePlace ℚ) :
    Valued.v (rationalFiniteAdicUniformizer v) = WithZero.exp (-1 : ℤ) := by
  exact (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
    (v := v.maximalIdeal) (K := ℚ) (placeUniformizer ℚ v.maximalIdeal)).trans
      (placeUniformizer_valuation ℚ v.maximalIdeal)

theorem rationalFiniteAdicUniformizer_ne_zero (v : NumberField.FinitePlace ℚ) :
    rationalFiniteAdicUniformizer v ≠ 0 := by
  intro h
  have hval := rationalFiniteAdicUniformizer_valuation v
  rw [h, map_zero] at hval
  exact absurd hval.symm (by simp [WithZero.exp])

/-- The finite-completion uniformizer as a field unit. -/
noncomputable def rationalFiniteAdicUniformizerUnit (v : NumberField.FinitePlace ℚ) :
    (v.maximalIdeal.adicCompletion ℚ)ˣ :=
  Units.mk0 (rationalFiniteAdicUniformizer v) (rationalFiniteAdicUniformizer_ne_zero v)

theorem rationalFiniteAdicUniformizer_tameVal (v : NumberField.FinitePlace ℚ) :
    Multiplicative.toAdd (tameValHom
      (Valued.v : Valuation (v.maximalIdeal.adicCompletion ℚ) ℤᵐ⁰)
      (rationalFiniteAdicUniformizerUnit v)) = 1 := by
  have hcoe : ((tameUnzero (Valued.v : Valuation (v.maximalIdeal.adicCompletion ℚ) ℤᵐ⁰)
      (rationalFiniteAdicUniformizerUnit v) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) =
      ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) := by
    rw [coe_tameUnzero]
    exact rationalFiniteAdicUniformizer_valuation v
  have hun : tameUnzero (Valued.v : Valuation (v.maximalIdeal.adicCompletion ℚ) ℤᵐ⁰)
      (rationalFiniteAdicUniformizerUnit v) = Multiplicative.ofAdd (-1 : ℤ) :=
    WithZero.coe_inj.1 hcoe
  rw [tameValHom_toAdd, hun]
  simp

/-- Residue data for a finite completion of `ℚ`. -/
noncomputable def rationalFiniteAdicResidueData (v : NumberField.FinitePlace ℚ) :
    ResidueData (v.maximalIdeal.adicCompletion ℚ)
      (IsLocalRing.ResidueField
        (Valued.v : Valuation (v.maximalIdeal.adicCompletion ℚ) ℤᵐ⁰).valuationSubring) :=
  residueDataOfValuation (Valued.v : Valuation (v.maximalIdeal.adicCompletion ℚ) ℤᵐ⁰)
    (rationalFiniteAdicUniformizerUnit v) (rationalFiniteAdicUniformizer_tameVal v)

/-- The completed finite rational valuation is surjective onto the integer value group. -/
theorem rationalFiniteAdicValuation_surjective (v : NumberField.FinitePlace ℚ) :
    Function.Surjective (rationalFiniteAdicResidueData v).val :=
  residueDataValuation_surjective _

/-- At a finite completion of `ℚ`, valuation-zero units form exactly the valuation kernel. -/
theorem rationalFiniteAdicValuation_exact (v : NumberField.FinitePlace ℚ) : Function.Exact
    (MonoidHom.toAdditive (rationalFiniteAdicResidueData v).val.ker.subtype)
    (MonoidHom.toAdditive (rationalFiniteAdicResidueData v).val) :=
  residueDataValuation_exact _

/-- The multiplicative unit quotient at a finite completion of `ℚ` is its integer value group. -/
noncomputable def rationalFiniteAdicQuotientKerValuationEquiv (v : NumberField.FinitePlace ℚ) :
    (v.maximalIdeal.adicCompletion ℚ)ˣ ⧸ (rationalFiniteAdicResidueData v).val.ker ≃*
      Multiplicative ℤ :=
  residueDataQuotientKerValuationEquiv _

end

end GaloisForLFunctions.HTGeometry.ABHN
