/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.LocalValuationSequence
import GaloisForLFunctions.HTGeometry.ABHN.Places
import GaloisForLFunctions.HTGeometry.MilnorKResidueValuation

/-!
# Valuation sequences at finite completions of number fields

For every finite place of a number field, the chosen global uniformizer embedded in the adic
completion has valuation `-1`. It supplies residue data and a split unit/valuation sequence at
that completed field. This is the common valuation-theoretic local layer before local class field
theory; it does not construct a local Brauer invariant.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open IsDedekindDomain
open scoped WithZero WithZeroMulInt

universe u

noncomputable section

variable (K : Type u) [Field K] [NumberField K]

/-- The chosen global uniformizer embedded in a finite adic completion of a number field. -/
noncomputable def numberFieldFiniteAdicUniformizer
    (v : NumberField.FinitePlace K) : v.maximalIdeal.adicCompletion K :=
  NumberField.FinitePlace.embedding v.maximalIdeal
    (placeUniformizer K v.maximalIdeal)

/-- The finite-completion uniformizer has valuation `-1`. -/
theorem numberFieldFiniteAdicUniformizer_valuation
    (v : NumberField.FinitePlace K) :
    Valued.v (numberFieldFiniteAdicUniformizer K v) = WithZero.exp (-1 : ℤ) := by
  exact (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
    (v := v.maximalIdeal) (K := K) (placeUniformizer K v.maximalIdeal)).trans
      (placeUniformizer_valuation K v.maximalIdeal)

/-- The finite-completion uniformizer is nonzero. -/
theorem numberFieldFiniteAdicUniformizer_ne_zero
    (v : NumberField.FinitePlace K) : numberFieldFiniteAdicUniformizer K v ≠ 0 := by
  intro h
  have hval := numberFieldFiniteAdicUniformizer_valuation K v
  rw [h, map_zero] at hval
  exact absurd hval.symm (by simp [WithZero.exp])

/-- The finite-completion uniformizer as a unit. -/
noncomputable def numberFieldFiniteAdicUniformizerUnit
    (v : NumberField.FinitePlace K) : (v.maximalIdeal.adicCompletion K)ˣ :=
  Units.mk0 (numberFieldFiniteAdicUniformizer K v)
    (numberFieldFiniteAdicUniformizer_ne_zero K v)

/-- The finite-completion uniformizer maps to `1` under the tame integer valuation. -/
theorem numberFieldFiniteAdicUniformizer_tameVal
    (v : NumberField.FinitePlace K) :
    Multiplicative.toAdd (tameValHom
      (Valued.v : Valuation (v.maximalIdeal.adicCompletion K) ℤᵐ⁰)
      (numberFieldFiniteAdicUniformizerUnit K v)) = 1 := by
  have hcoe : ((tameUnzero (Valued.v : Valuation (v.maximalIdeal.adicCompletion K) ℤᵐ⁰)
      (numberFieldFiniteAdicUniformizerUnit K v) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) =
      ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) := by
    rw [coe_tameUnzero]
    exact numberFieldFiniteAdicUniformizer_valuation K v
  have hun : tameUnzero (Valued.v : Valuation (v.maximalIdeal.adicCompletion K) ℤᵐ⁰)
      (numberFieldFiniteAdicUniformizerUnit K v) = Multiplicative.ofAdd (-1 : ℤ) :=
    WithZero.coe_inj.1 hcoe
  rw [tameValHom_toAdd, hun]
  simp

/-- Residue data for a finite completion of a number field. -/
noncomputable def numberFieldFiniteAdicResidueData
    (v : NumberField.FinitePlace K) :
    ResidueData (v.maximalIdeal.adicCompletion K)
      (IsLocalRing.ResidueField
        (Valued.v : Valuation (v.maximalIdeal.adicCompletion K) ℤᵐ⁰).valuationSubring) :=
  residueDataOfValuation (Valued.v : Valuation (v.maximalIdeal.adicCompletion K) ℤᵐ⁰)
    (numberFieldFiniteAdicUniformizerUnit K v)
    (numberFieldFiniteAdicUniformizer_tameVal K v)

/-- The finite completed valuation is onto the integer value group. -/
theorem numberFieldFiniteAdicValuation_surjective
    (v : NumberField.FinitePlace K) :
    Function.Surjective (numberFieldFiniteAdicResidueData K v).val :=
  residueDataValuation_surjective _

/-- At a finite completed place, valuation-zero units are exactly the valuation kernel. -/
theorem numberFieldFiniteAdicValuation_exact
    (v : NumberField.FinitePlace K) : Function.Exact
    (MonoidHom.toAdditive (numberFieldFiniteAdicResidueData K v).val.ker.subtype)
    (MonoidHom.toAdditive (numberFieldFiniteAdicResidueData K v).val) :=
  residueDataValuation_exact _

/-- The field-unit quotient at a finite completed place is the integer value group. -/
noncomputable def numberFieldFiniteAdicQuotientKerValuationEquiv
    (v : NumberField.FinitePlace K) :
    (v.maximalIdeal.adicCompletion K)ˣ ⧸ (numberFieldFiniteAdicResidueData K v).val.ker ≃*
      Multiplicative ℤ :=
  residueDataQuotientKerValuationEquiv _

end

end GaloisForLFunctions.HTGeometry.ABHN
