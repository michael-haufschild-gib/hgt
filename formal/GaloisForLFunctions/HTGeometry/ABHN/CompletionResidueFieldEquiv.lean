/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.NumberFieldFiniteLocalField
import GaloisForLFunctions.HTGeometry.ABHN.RationalFunctionFiniteLocalField
import GaloisForLFunctions.HTGeometry.MilnorKDegRingEquiv

/-!
# Residue fields are preserved by finite-place completion

At a finite place, the map from the pre-completion valuation ring to the completed valuation ring
induces a surjection on residue fields by density.  Since both source and target are fields, that
surjection is an isomorphism.  This supplies the explicit completion/residue-field transport
needed to compare global tame residues with their completed local counterparts.

This is only residue-field transport.  It neither compares Milnor groups nor constructs a Brauer
invariant.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open IsDedekindDomain
open scoped Polynomial ValuativeRel WithZero WithZeroMulInt

universe u

/-- Finite-place completion of a number field preserves its residue field. -/
noncomputable def numberFieldAdicCompletion_residueFieldMapEquiv
    (K : Type u) [Field K] [NumberField K] (v : NumberField.FinitePlace K) :
    IsLocalRing.ResidueField ((v.maximalIdeal.valuation K).integer) ≃+*
      IsLocalRing.ResidueField
        ((Valued.v : Valuation (v.maximalIdeal.adicCompletion K) ℤᵐ⁰).integer) :=
  RingEquiv.ofBijective
    (IsLocalRing.ResidueField.map
      (algebraMap (v.maximalIdeal.valuation K).integer
        (Valued.v : Valuation (v.maximalIdeal.adicCompletion K) ℤᵐ⁰).integer))
    ⟨RingHom.injective _, numberFieldAdicCompletion_residueField_map_surjective K v⟩

/-- Finite-place completion of `F(t)` preserves its residue field. -/
noncomputable def rationalFunctionAdicCompletion_residueFieldMapEquiv
    (F : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X]) :
    IsLocalRing.ResidueField ((v.valuation (RatFunc F)).integer) ≃+*
      IsLocalRing.ResidueField
        ((Valued.v : Valuation (v.adicCompletion (RatFunc F)) ℤᵐ⁰).integer) :=
  RingEquiv.ofBijective
    (IsLocalRing.ResidueField.map
      (algebraMap (v.valuation (RatFunc F)).integer
        (Valued.v : Valuation (v.adicCompletion (RatFunc F)) ℤᵐ⁰).integer))
    ⟨RingHom.injective _, rationalFunctionAdicCompletion_residueField_map_surjective F v⟩

/-- Completion at a finite number-field place transports every graded residue Milnor `K` group. -/
noncomputable def numberFieldAdicCompletion_residueMilnorKDegAddEquiv
    (K : Type u) [Field K] [NumberField K] (v : NumberField.FinitePlace K) (n : ℕ) :
    MilnorKDeg (IsLocalRing.ResidueField ((v.maximalIdeal.valuation K).integer)) n ≃+
      MilnorKDeg (IsLocalRing.ResidueField
        ((Valued.v : Valuation (v.maximalIdeal.adicCompletion K) ℤᵐ⁰).integer)) n :=
  milnorKDegAddEquivOfRingEquiv (numberFieldAdicCompletion_residueFieldMapEquiv K v) n

/-- Completion at a finite place of `F(t)` transports every graded residue Milnor `K` group. -/
noncomputable def rationalFunctionAdicCompletion_residueMilnorKDegAddEquiv
    (F : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X]) (n : ℕ) :
    MilnorKDeg (IsLocalRing.ResidueField ((v.valuation (RatFunc F)).integer)) n ≃+
      MilnorKDeg (IsLocalRing.ResidueField
        ((Valued.v : Valuation (v.adicCompletion (RatFunc F)) ℤᵐ⁰).integer)) n :=
  milnorKDegAddEquivOfRingEquiv (rationalFunctionAdicCompletion_residueFieldMapEquiv F v) n

end GaloisForLFunctions.HTGeometry.ABHN
