/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.LocalValuationSequence
import GaloisForLFunctions.HTGeometry.ABHN.RationalFunctionFiniteLocalField
import GaloisForLFunctions.HTGeometry.MilnorKResidueValuation

/-!
# Valuation sequences at finite completions of rational function fields

For every height-one place of `F[X]`, the image of the chosen global uniformizer is a uniformizer
in the `v`-adic completion of `F(t)`.  This yields residue data and the split unit/valuation
sequence for each finite local function-field model.

The result is valuation-theoretic infrastructure only; it does not contain local reciprocity or a
Brauer-group invariant.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open IsDedekindDomain
open scoped Polynomial WithZero WithZeroMulInt

universe u

noncomputable section

/-- The global chosen uniformizer embedded in a finite `F(t)`-adic completion. -/
noncomputable def rationalFunctionFiniteAdicUniformizer
    (F : Type u) [Field F] (v : HeightOneSpectrum F[X]) : v.adicCompletion (RatFunc F) :=
  NumberField.FinitePlace.embedding v (placeUniformizer (RatFunc F) v)

theorem rationalFunctionFiniteAdicUniformizer_valuation
    (F : Type u) [Field F] (v : HeightOneSpectrum F[X]) :
    Valued.v (rationalFunctionFiniteAdicUniformizer F v) = WithZero.exp (-1 : ℤ) := by
  exact (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
    (v := v) (K := RatFunc F) (placeUniformizer (RatFunc F) v)).trans
      (placeUniformizer_valuation (RatFunc F) v)

theorem rationalFunctionFiniteAdicUniformizer_ne_zero
    (F : Type u) [Field F] (v : HeightOneSpectrum F[X]) :
    rationalFunctionFiniteAdicUniformizer F v ≠ 0 := by
  intro h
  have hval := rationalFunctionFiniteAdicUniformizer_valuation F v
  rw [h, map_zero] at hval
  exact absurd hval.symm (by simp [WithZero.exp])

/-- The finite-completion uniformizer as a field unit. -/
noncomputable def rationalFunctionFiniteAdicUniformizerUnit
    (F : Type u) [Field F] (v : HeightOneSpectrum F[X]) : (v.adicCompletion (RatFunc F))ˣ :=
  Units.mk0 (rationalFunctionFiniteAdicUniformizer F v)
    (rationalFunctionFiniteAdicUniformizer_ne_zero F v)

theorem rationalFunctionFiniteAdicUniformizer_tameVal
    (F : Type u) [Field F] (v : HeightOneSpectrum F[X]) :
    Multiplicative.toAdd (tameValHom
      (Valued.v : Valuation (v.adicCompletion (RatFunc F)) ℤᵐ⁰)
      (rationalFunctionFiniteAdicUniformizerUnit F v)) = 1 := by
  have hcoe : ((tameUnzero (Valued.v : Valuation (v.adicCompletion (RatFunc F)) ℤᵐ⁰)
      (rationalFunctionFiniteAdicUniformizerUnit F v) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) =
      ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) := by
    rw [coe_tameUnzero]
    exact rationalFunctionFiniteAdicUniformizer_valuation F v
  have hun : tameUnzero (Valued.v : Valuation (v.adicCompletion (RatFunc F)) ℤᵐ⁰)
      (rationalFunctionFiniteAdicUniformizerUnit F v) = Multiplicative.ofAdd (-1 : ℤ) :=
    WithZero.coe_inj.1 hcoe
  rw [tameValHom_toAdd, hun]
  simp

/-- Residue data for a finite completion of `F(t)`. -/
noncomputable def rationalFunctionFiniteAdicResidueData
    (F : Type u) [Field F] (v : HeightOneSpectrum F[X]) :
    ResidueData (v.adicCompletion (RatFunc F))
      (IsLocalRing.ResidueField
        (Valued.v : Valuation (v.adicCompletion (RatFunc F)) ℤᵐ⁰).valuationSubring) :=
  residueDataOfValuation (Valued.v : Valuation (v.adicCompletion (RatFunc F)) ℤᵐ⁰)
    (rationalFunctionFiniteAdicUniformizerUnit F v)
    (rationalFunctionFiniteAdicUniformizer_tameVal F v)

/-- The finite `F(t)`-adic valuation is onto the integer value group. -/
theorem rationalFunctionFiniteAdicValuation_surjective
    (F : Type u) [Field F] (v : HeightOneSpectrum F[X]) :
    Function.Surjective (rationalFunctionFiniteAdicResidueData F v).val :=
  residueDataValuation_surjective _

/-- At a finite `F(t)`-adic completion, valuation-zero units are exactly the valuation kernel. -/
theorem rationalFunctionFiniteAdicValuation_exact
    (F : Type u) [Field F] (v : HeightOneSpectrum F[X]) : Function.Exact
    (MonoidHom.toAdditive (rationalFunctionFiniteAdicResidueData F v).val.ker.subtype)
    (MonoidHom.toAdditive (rationalFunctionFiniteAdicResidueData F v).val) :=
  residueDataValuation_exact _

/-- The field-unit quotient at a finite `F(t)`-adic completion is the integer value group. -/
noncomputable def rationalFunctionFiniteAdicQuotientKerValuationEquiv
    (F : Type u) [Field F] (v : HeightOneSpectrum F[X]) :
    (v.adicCompletion (RatFunc F))ˣ ⧸ (rationalFunctionFiniteAdicResidueData F v).val.ker ≃*
      Multiplicative ℤ :=
  residueDataQuotientKerValuationEquiv _

end

end GaloisForLFunctions.HTGeometry.ABHN
