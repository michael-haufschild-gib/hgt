/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.NumberFieldFiniteLocalField
import GaloisForLFunctions.HTGeometry.ABHN.RationalFunctionFiniteLocalField
import GaloisForLFunctions.HTGeometry.FiniteMilnorKOneCharacterTransport
import GaloisForLFunctions.HTGeometry.MilnorKDegRingEquiv

/-!
# Residue fields are preserved by finite-place completion

At a finite place, the map from the pre-completion valuation ring to the completed valuation ring
induces a surjection on residue fields by density.  Since both source and target are fields, that
surjection is an isomorphism.  This supplies the explicit completion/residue-field transport
needed to compare global tame residues with their completed local counterparts.

The equivalences transport all graded Milnor `K` groups and, in degree one, the canonical faithful
finite-field circle character.  This does not yet construct a Brauer invariant.
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

/-- The valuation-subring residue field at a finite number-field place is the residue field of its
completion.  The two outer equivalences only change between the `valuationSubring` and `integer`
presentations of the same valuation ring. -/
noncomputable def numberFieldAdicCompletion_valuationResidueFieldEquiv
    (K : Type u) [Field K] [NumberField K] (v : NumberField.FinitePlace K) :
    IsLocalRing.ResidueField ((v.maximalIdeal.valuation K).valuationSubring) ≃+*
      IsLocalRing.ResidueField
        ((Valued.v : Valuation (v.maximalIdeal.adicCompletion K) ℤᵐ⁰).valuationSubring) :=
  (IsLocalRing.ResidueField.mapEquiv (RingEquiv.subringCongr rfl)).trans
    ((numberFieldAdicCompletion_residueFieldMapEquiv K v).trans
      (IsLocalRing.ResidueField.mapEquiv (RingEquiv.subringCongr rfl)))

/-- The valuation-subring residue field at a finite place of `F(t)` is the residue field of its
completion. -/
noncomputable def rationalFunctionAdicCompletion_valuationResidueFieldEquiv
    (F : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X]) :
    IsLocalRing.ResidueField ((v.valuation (RatFunc F)).valuationSubring) ≃+*
      IsLocalRing.ResidueField
        ((Valued.v : Valuation (v.adicCompletion (RatFunc F)) ℤᵐ⁰).valuationSubring) :=
  (IsLocalRing.ResidueField.mapEquiv (RingEquiv.subringCongr rfl)).trans
    ((rationalFunctionAdicCompletion_residueFieldMapEquiv F v).trans
      (IsLocalRing.ResidueField.mapEquiv (RingEquiv.subringCongr rfl)))

/-- The residue field at a finite number-field place is finite, transported back from completion. -/
noncomputable instance numberFieldFinitePlaceResidueFieldFinite
    (K : Type u) [Field K] [NumberField K] (v : NumberField.FinitePlace K) :
    Finite (IsLocalRing.ResidueField ((v.maximalIdeal.valuation K).integer)) :=
  Finite.of_equiv
    (IsLocalRing.ResidueField
      ((Valued.v : Valuation (v.maximalIdeal.adicCompletion K) ℤᵐ⁰).integer))
    (numberFieldAdicCompletion_residueFieldMapEquiv K v).symm.toEquiv

/-- The residue field at a finite place of `F(t)` is finite, transported back from completion. -/
noncomputable instance rationalFunctionFinitePlaceResidueFieldFinite
    (F : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X]) :
    Finite (IsLocalRing.ResidueField ((v.valuation (RatFunc F)).integer)) :=
  Finite.of_equiv
    (IsLocalRing.ResidueField
      ((Valued.v : Valuation (v.adicCompletion (RatFunc F)) ℤᵐ⁰).integer))
    (rationalFunctionAdicCompletion_residueFieldMapEquiv F v).symm.toEquiv

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

/-- Completion transports every Milnor degree between valuation-subring residue fields at a finite
number-field place. -/
noncomputable def numberFieldAdicCompletion_valuationResidueMilnorKDegAddEquiv
    (K : Type u) [Field K] [NumberField K] (v : NumberField.FinitePlace K) (n : ℕ) :
    MilnorKDeg (IsLocalRing.ResidueField
        ((v.maximalIdeal.valuation K).valuationSubring)) n ≃+
      MilnorKDeg (IsLocalRing.ResidueField
        ((Valued.v : Valuation (v.maximalIdeal.adicCompletion K) ℤᵐ⁰).valuationSubring)) n :=
  milnorKDegAddEquivOfRingEquiv
    (numberFieldAdicCompletion_valuationResidueFieldEquiv K v) n

/-- Completion transports every Milnor degree between valuation-subring residue fields at a finite
place of `F(t)`. -/
noncomputable def rationalFunctionAdicCompletion_valuationResidueMilnorKDegAddEquiv
    (F : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X]) (n : ℕ) :
    MilnorKDeg (IsLocalRing.ResidueField
        ((v.valuation (RatFunc F)).valuationSubring)) n ≃+
      MilnorKDeg (IsLocalRing.ResidueField
        ((Valued.v : Valuation (v.adicCompletion (RatFunc F)) ℤᵐ⁰).valuationSubring)) n :=
  milnorKDegAddEquivOfRingEquiv
    (rationalFunctionAdicCompletion_valuationResidueFieldEquiv F v) n

/-- The canonical residue Milnor `K₁` phase transported to a completed number-field place. -/
noncomputable def numberFieldAdicCompletion_residueMilnorKOneStdAddChar
    (K : Type u) [Field K] [NumberField K] (v : NumberField.FinitePlace K) :
    AddChar
      (MilnorKDeg (IsLocalRing.ResidueField
        ((Valued.v : Valuation (v.maximalIdeal.adicCompletion K) ℤᵐ⁰).integer)) 1) ℂ :=
  finiteMilnorKOneStdAddCharTransport
    (numberFieldAdicCompletion_residueFieldMapEquiv K v)

/-- The completed number-field residue phase agrees with the global-place residue phase. -/
theorem numberFieldAdicCompletion_residueMilnorKOneStdAddChar_apply_equiv
    (K : Type u) [Field K] [NumberField K] (v : NumberField.FinitePlace K)
    (x : MilnorKDeg (IsLocalRing.ResidueField
      ((v.maximalIdeal.valuation K).integer)) 1) :
    numberFieldAdicCompletion_residueMilnorKOneStdAddChar K v
        (numberFieldAdicCompletion_residueMilnorKDegAddEquiv K v 1 x) =
      finiteMilnorKOneStdAddChar
        (IsLocalRing.ResidueField ((v.maximalIdeal.valuation K).integer)) x :=
  finiteMilnorKOneStdAddCharTransport_apply_equiv
    (numberFieldAdicCompletion_residueFieldMapEquiv K v) x

/-- The transported completed number-field residue phase remains faithful. -/
theorem numberFieldAdicCompletion_residueMilnorKOneStdAddChar_injective
    (K : Type u) [Field K] [NumberField K] (v : NumberField.FinitePlace K) :
    Function.Injective (numberFieldAdicCompletion_residueMilnorKOneStdAddChar K v) :=
  finiteMilnorKOneStdAddCharTransport_injective
    (numberFieldAdicCompletion_residueFieldMapEquiv K v)

/-- At a completed number-field place, the transported residue phase is one only at zero. -/
theorem numberFieldAdicCompletion_residueMilnorKOneStdAddChar_eq_one_iff_eq_zero
    (K : Type u) [Field K] [NumberField K] (v : NumberField.FinitePlace K)
    (x : MilnorKDeg (IsLocalRing.ResidueField
      ((Valued.v : Valuation (v.maximalIdeal.adicCompletion K) ℤᵐ⁰).integer)) 1) :
    numberFieldAdicCompletion_residueMilnorKOneStdAddChar K v x = 1 ↔ x = 0 :=
  finiteMilnorKOneStdAddCharTransport_eq_one_iff_eq_zero
    (numberFieldAdicCompletion_residueFieldMapEquiv K v) x

/-- The canonical residue Milnor `K₁` phase transported to a completed finite place of `F(t)`. -/
noncomputable def rationalFunctionAdicCompletion_residueMilnorKOneStdAddChar
    (F : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X]) :
    AddChar
      (MilnorKDeg (IsLocalRing.ResidueField
        ((Valued.v : Valuation (v.adicCompletion (RatFunc F)) ℤᵐ⁰).integer)) 1) ℂ :=
  finiteMilnorKOneStdAddCharTransport
    (rationalFunctionAdicCompletion_residueFieldMapEquiv F v)

/-- The completed `F(t)` residue phase agrees with the global-place residue phase. -/
theorem rationalFunctionAdicCompletion_residueMilnorKOneStdAddChar_apply_equiv
    (F : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X])
    (x : MilnorKDeg (IsLocalRing.ResidueField
      ((v.valuation (RatFunc F)).integer)) 1) :
    rationalFunctionAdicCompletion_residueMilnorKOneStdAddChar F v
        (rationalFunctionAdicCompletion_residueMilnorKDegAddEquiv F v 1 x) =
      finiteMilnorKOneStdAddChar
        (IsLocalRing.ResidueField ((v.valuation (RatFunc F)).integer)) x :=
  finiteMilnorKOneStdAddCharTransport_apply_equiv
    (rationalFunctionAdicCompletion_residueFieldMapEquiv F v) x

/-- The transported completed `F(t)` residue phase remains faithful. -/
theorem rationalFunctionAdicCompletion_residueMilnorKOneStdAddChar_injective
    (F : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X]) :
    Function.Injective (rationalFunctionAdicCompletion_residueMilnorKOneStdAddChar F v) :=
  finiteMilnorKOneStdAddCharTransport_injective
    (rationalFunctionAdicCompletion_residueFieldMapEquiv F v)

/-- At a completed finite place of `F(t)`, the transported residue phase is one only at zero. -/
theorem rationalFunctionAdicCompletion_residueMilnorKOneStdAddChar_eq_one_iff_eq_zero
    (F : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X])
    (x : MilnorKDeg (IsLocalRing.ResidueField
      ((Valued.v : Valuation (v.adicCompletion (RatFunc F)) ℤᵐ⁰).integer)) 1) :
    rationalFunctionAdicCompletion_residueMilnorKOneStdAddChar F v x = 1 ↔ x = 0 :=
  finiteMilnorKOneStdAddCharTransport_eq_one_iff_eq_zero
    (rationalFunctionAdicCompletion_residueFieldMapEquiv F v) x

end GaloisForLFunctions.HTGeometry.ABHN
