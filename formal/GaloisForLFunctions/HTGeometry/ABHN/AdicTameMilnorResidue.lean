/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.NumberFieldFiniteValuationSequence
import GaloisForLFunctions.HTGeometry.ABHN.RationalFunctionFiniteValuationSequence
import GaloisForLFunctions.HTGeometry.MilnorKFiniteDegreeOne

/-!
# Tame Milnor residues for the actual adic valuation

The generic nonarchimedean-local-field residue uses a normalized valuation recovered from the
valuative relation.  For comparison with a global finite place, the concrete adic valuation is
better: its chosen uniformizer is the embedded global uniformizer, and its residue map is the map
used by completion.

This module proves once and for all that residue data made directly from an integer-valued
valuation have surjective residue-unit and tame-symbol maps.  It then exposes the degree-two tame
Milnor residues attached to the concrete number-field and rational-function adic valuations.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped Polynomial WithZero WithZeroMulInt

universe u v

noncomputable section

variable {K : Type u} [Field K]

/-- Every residue-field unit lifts to a valuation-zero unit for residue data made from a
valuation. -/
theorem residueDataOfValuation_residueUnit_surjective
    (w : Valuation K ℤᵐ⁰) (π : Kˣ)
    (hπ : Multiplicative.toAdd (tameValHom w π) = 1)
    (y : (IsLocalRing.ResidueField w.valuationSubring)ˣ) :
    ∃ a : Kˣ, (residueDataOfValuation w π hπ).val' a = 0 ∧
      (residueDataOfValuation w π hπ).residueUnit a = y := by
  let A := w.valuationSubring
  obtain ⟨x, hx⟩ := IsLocalRing.residue_surjective
    (y : IsLocalRing.ResidueField A)
  have hres0 : IsLocalRing.residue A x ≠ 0 := by
    rw [hx]
    exact y.ne_zero
  obtain ⟨u, hu⟩ := (IsLocalRing.residue_ne_zero_iff_isUnit x).mp hres0
  let a : Kˣ := Units.map A.subtype.toMonoidHom u
  have haVal : w (a : K) = 1 := by
    change w (algebraMap A K (u : A)) = 1
    exact (Valuation.integer.integers w).valuation_unit u
  have haKer : a ∈ (tameValHom w).ker :=
    (tameValHom_mem_ker_iff w a).2 haVal
  refine ⟨a, ?_, ?_⟩
  · exact (residueDataOfValuation w π hπ).val'_eq_zero_iff.2 haKer
  · apply Units.ext
    rw [ResidueData.residueUnit_of_mem_ker _ haKer]
    change IsLocalRing.residue A ((u : Aˣ) : A) =
      (y : IsLocalRing.ResidueField A)
    rw [hu, hx]

/-- The degree-two tame symbol made from an integer-valued valuation is surjective. -/
theorem residueDataOfValuation_tameHom_surjective
    (w : Valuation K ℤᵐ⁰) (π : Kˣ)
    (hπ : Multiplicative.toAdd (tameValHom w π) = 1) :
    Function.Surjective (residueDataOfValuation w π hπ).tameHom := by
  intro y
  obtain ⟨a, ha, hay⟩ :=
    residueDataOfValuation_residueUnit_surjective w π hπ y.toMul
  have haKer : a ∈ (residueDataOfValuation w π hπ).val.ker :=
    (residueDataOfValuation w π hπ).val'_eq_zero_iff.1 ha
  refine ⟨milnorClassDeg K 2 ⟨[a, (residueDataOfValuation w π hπ).unif], rfl⟩, ?_⟩
  rw [TameData.tameHom_symbol, TameData.tame_of_mem_ker_left
    (residueDataOfValuation w π hπ).toTameData haKer]
  apply Additive.toMul.injective
  change (residueDataOfValuation w π hπ).res ⟨a, haKer⟩ ^
    (residueDataOfValuation w π hπ).val'
      (residueDataOfValuation w π hπ).unif = y.toMul
  rw [(residueDataOfValuation w π hπ).val'_unif, zpow_one]
  rw [← (residueDataOfValuation w π hπ).residueUnit_of_mem_ker haKer, hay]

/-- Convert any degree-two tame symbol into the standard degree-one Milnor target. -/
noncomputable def residueDataTameMilnorResidue
    {k : Type v} [Field k] (D : ResidueData K k) :
    MilnorKDeg K 2 →+ MilnorKDeg k 1 :=
  (milnorDegOneEquiv _).symm.toAddMonoidHom.comp D.tameHom

/-- Surjectivity of a tame symbol passes to its standard Milnor `K₁` presentation. -/
theorem residueDataTameMilnorResidue_surjective
    {k : Type v} [Field k] (D : ResidueData K k)
    (hD : Function.Surjective D.tameHom) :
    Function.Surjective (residueDataTameMilnorResidue D) := by
  intro y
  obtain ⟨x, hx⟩ := hD (milnorDegOneEquiv _ y)
  refine ⟨x, ?_⟩
  change (milnorDegOneEquiv _).symm (D.tameHom x) = y
  rw [hx]
  exact (milnorDegOneEquiv _).symm_apply_apply y

/-- Tame Milnor residue for the actual extended valuation at a finite number-field place. -/
noncomputable def numberFieldFiniteAdicTameMilnorResidue
    (K : Type u) [Field K] [NumberField K] (v : NumberField.FinitePlace K) :
    MilnorKDeg (v.maximalIdeal.adicCompletion K) 2 →+
      MilnorKDeg (IsLocalRing.ResidueField
        (Valued.v : Valuation (v.maximalIdeal.adicCompletion K) ℤᵐ⁰).valuationSubring) 1 :=
  residueDataTameMilnorResidue (numberFieldFiniteAdicResidueData K v)

/-- The concrete finite number-field adic tame residue is onto. -/
theorem numberFieldFiniteAdicTameMilnorResidue_surjective
    (K : Type u) [Field K] [NumberField K] (v : NumberField.FinitePlace K) :
    Function.Surjective (numberFieldFiniteAdicTameMilnorResidue K v) := by
  apply residueDataTameMilnorResidue_surjective
  unfold numberFieldFiniteAdicResidueData
  exact residueDataOfValuation_tameHom_surjective _ _ _

/-- Tame Milnor residue for the actual extended valuation at a finite place of `F(t)`. -/
noncomputable def rationalFunctionFiniteAdicTameMilnorResidue
    (F : Type u) [Field F] [Finite F] (v : IsDedekindDomain.HeightOneSpectrum F[X]) :
    MilnorKDeg (v.adicCompletion (RatFunc F)) 2 →+
      MilnorKDeg (IsLocalRing.ResidueField
        (Valued.v : Valuation (v.adicCompletion (RatFunc F)) ℤᵐ⁰).valuationSubring) 1 :=
  residueDataTameMilnorResidue (rationalFunctionFiniteAdicResidueData F v)

/-- The concrete finite `F(t)`-adic tame residue is onto. -/
theorem rationalFunctionFiniteAdicTameMilnorResidue_surjective
    (F : Type u) [Field F] [Finite F] (v : IsDedekindDomain.HeightOneSpectrum F[X]) :
    Function.Surjective (rationalFunctionFiniteAdicTameMilnorResidue F v) := by
  apply residueDataTameMilnorResidue_surjective
  unfold rationalFunctionFiniteAdicResidueData
  exact residueDataOfValuation_tameHom_surjective _ _ _

end

end GaloisForLFunctions.HTGeometry.ABHN
