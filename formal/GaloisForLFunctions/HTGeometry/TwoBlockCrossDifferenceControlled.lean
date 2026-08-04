import GaloisForLFunctions.HTGeometry.SeparantCoefficientMap
import GaloisForLFunctions.HTGeometry.TwoBlockControlledSaturation

/-!
# The cross-difference certificate with a controlled multiplier

The two-block cross-difference of two coefficients of a cleared characteristic satisfies a
saturation certificate over the jet fraction field, with the initial and the separant of the
characteristic as multipliers.  Transporting that certificate to an irreducible factor and
exchanging the multiplier produces a certificate in the two-block ring whose multiplier is built
from the factor itself.

This is the form the divisibility bridge consumes: the bridge needs the multiplier's order in the
left block to be bounded by that of the factor, which a multiplier obtained by clearing denominators
never guarantees.
-/

namespace GaloisForLFunctions

open scoped Differential

noncomputable section

/-- The initial commutes with an injective coefficient map. -/
theorem mvPolynomialInitialAt_map {K L σ : Type*} [CommRing K] [CommRing L] {f : K →+* L}
    (hf : Function.Injective f) (i : σ) (P : MvPolynomial σ K) :
    mvPolynomialInitialAt i (MvPolynomial.map f P) =
      MvPolynomial.map f (mvPolynomialInitialAt i P) := by
  classical
  have hmap : mvPolynomialAsPolynomialAt i (MvPolynomial.map f P) =
      Polynomial.map (MvPolynomial.map f) (mvPolynomialAsPolynomialAt i P) := by
    rw [← mvPolynomialPolynomialEquivAt_apply, ← mvPolynomialPolynomialEquivAt_apply,
      mvPolynomialPolynomialEquivAt_map]
  unfold mvPolynomialInitialAt
  rw [hmap]
  by_cases hP : mvPolynomialAsPolynomialAt i P = 0
  · rw [hP]
    simp
  · have hlead :
        (Polynomial.map (MvPolynomial.map f) (mvPolynomialAsPolynomialAt i P)).leadingCoeff =
          MvPolynomial.map f (mvPolynomialAsPolynomialAt i P).leadingCoeff := by
      refine Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ ?_
      intro h0
      exact (Polynomial.leadingCoeff_ne_zero.mpr hP)
        (MvPolynomial.map_injective f hf (by simpa using h0))
    rw [hlead]
    exact (MvPolynomial.map_rename f Subtype.val _).symm

/-- **The cross-difference certificate with a controlled multiplier.**

For an irreducible factor of the cleared two-block characteristic whose right-block support is that
of the characteristic, the cross-difference of any two coefficients satisfies a certificate in the
two-block ring whose multiplier is a product of powers of the initial and the separant of the factor
in the right-block splitting. -/
theorem exists_twoBlock_crossDifference_controlled_saturation
    {F E : Type*} [Field F] [Field E] [Differential F] [Differential E] [Algebra F E]
    [DifferentialAlgebra F E] [CharZero F] [CharZero E]
    (G : IntermediateField F E) (hGclosed : DerivationClosed G) {y : E}
    (hG : G ≤ differentialAdjoin F ({y} : Set E))
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    (P : DifferentialPolynomial Unit G)
    (hP : IsMinimalScalarDifferentialPolynomialRank
      (differentialIntermediateRelationIdeal G y : Set _) P)
    (hPirr : Irreducible P)
    (Cc : PrimitiveTwoBlockDifferentialCharacteristic G hG hy P)
    (m n : (Unit × ℕ) →₀ ℕ)
    {A : DifferentialPolynomial (Unit ⊕ Unit) F}
    (hAdvd : A ∣ Cc.polynomial)
    (hAvars : (differentialPolynomialTwoBlockEquiv F A).vars = P.vars)
    (hAirr : Irreducible (MvPolynomial.map
      (algebraMap (DifferentialPolynomial Unit F)
        (FractionRing (DifferentialPolynomial Unit F)))
      (differentialPolynomialTwoBlockEquiv F A))) :
    letI : Differential (DifferentialPolynomial Unit F) := differentialPolynomialDifferential F
    ∃ a b : ℕ,
      (differentialPolynomialTwoBlockEquiv F).symm
            (scalarDifferentialPolynomialInitial (differentialPolynomialTwoBlockEquiv F A) ^ a *
              scalarDifferentialPolynomialSeparant
                (differentialPolynomialTwoBlockEquiv F A) ^ b) *
          differentialPolynomialCrossDifference
            (differentialPolynomialTwoBlockCoefficient m Cc.polynomial)
            (differentialPolynomialTwoBlockCoefficient n Cc.polynomial) ∈
        differentialPolynomialFamilyIterateIdeal A := by
  classical
  letI : Differential (DifferentialPolynomial Unit F) := differentialPolynomialDifferential F
  letI : Differential (FractionRing (DifferentialPolynomial Unit F)) :=
    differentialIndependentJetFractionDifferential y hy
  letI : Differential G := derivationClosedDifferential G hGclosed
  letI : Algebra G (FractionRing (DifferentialPolynomial Unit F)) :=
    (differentialIntermediateToJetFraction G hG hy).toRingHom.toAlgebra
  -- the factor divides the mapped characteristic
  have hunit : IsUnit (MvPolynomial.C (Cc.scalar :
      FractionRing (DifferentialPolynomial Unit F)) :
      DifferentialPolynomial Unit (FractionRing (DifferentialPolynomial Unit F))) :=
    IsUnit.map MvPolynomial.C Cc.scalar.isUnit
  have hdvdmap : MvPolynomial.map
        (algebraMap (DifferentialPolynomial Unit F)
          (FractionRing (DifferentialPolynomial Unit F)))
        (differentialPolynomialTwoBlockEquiv F A) ∣
      MvPolynomial.C (Cc.scalar : FractionRing (DifferentialPolynomial Unit F)) *
        MvPolynomial.map (differentialIntermediateToJetFraction G hG hy).toRingHom P := by
    rw [← Cc.clearing]
    exact map_dvd _ (map_dvd (differentialPolynomialTwoBlockEquiv F) hAdvd)
  have hassoc : Associated
      (MvPolynomial.C (Cc.scalar : FractionRing (DifferentialPolynomial Unit F)) *
        MvPolynomial.map (differentialIntermediateToJetFraction G hG hy).toRingHom P)
      (MvPolynomial.map (differentialIntermediateToJetFraction G hG hy).toRingHom P) :=
    associated_unit_mul_left _ _ hunit
  have hdvd := hassoc.dvd_iff_dvd_right.mp hdvdmap
  obtain ⟨B, hB⟩ := hdvd
  -- squarefreeness of the mapped characteristic
  have hsq : Squarefree (MvPolynomial.map
      (differentialIntermediateToJetFraction G hG hy).toRingHom P) :=
    irreducible_map_squarefree_of_charZero
      (K := FractionRing (DifferentialPolynomial Unit F)) hPirr
  have hsqAB : Squarefree (MvPolynomial.map
        (algebraMap (DifferentialPolynomial Unit F)
          (FractionRing (DifferentialPolynomial Unit F)))
        (differentialPolynomialTwoBlockEquiv F A) * B) := by
    rw [← hB]
    exact hsq
  -- the factor has the order of the characteristic
  have hvarsL : (MvPolynomial.map
        (algebraMap (DifferentialPolynomial Unit F)
          (FractionRing (DifferentialPolynomial Unit F)))
        (differentialPolynomialTwoBlockEquiv F A)).vars =
      (MvPolynomial.map (differentialIntermediateToJetFraction G hG hy).toRingHom P).vars := by
    rw [MvPolynomial.vars_map_of_injective _
        (IsFractionRing.injective (DifferentialPolynomial Unit F)
          (FractionRing (DifferentialPolynomial Unit F))),
      MvPolynomial.vars_map_of_injective _
        (differentialIntermediateToJetFraction G hG hy).injective, hAvars]
  have horder : scalarDifferentialPolynomialOrder (MvPolynomial.map
        (algebraMap (DifferentialPolynomial Unit F)
          (FractionRing (DifferentialPolynomial Unit F)))
        (differentialPolynomialTwoBlockEquiv F A)) =
      scalarDifferentialPolynomialOrder (MvPolynomial.map
        (algebraMap (DifferentialPolynomial Unit F)
          (FractionRing (DifferentialPolynomial Unit F)))
        (differentialPolynomialTwoBlockEquiv F A) * B) := by
    rw [← hB, scalarDifferentialPolynomialOrder, scalarDifferentialPolynomialOrder, hvarsL]
  have hAvarsNonempty : (differentialPolynomialTwoBlockEquiv F A).vars.Nonempty := by
    rw [hAvars]
    exact hP.2.2.1
  -- the input certificate, read at the factor
  obtain ⟨a, b, hsat⟩ := Cc.exists_mappedCrossRelation_saturation G hGclosed hG hy P hP m n
  have hIL : scalarDifferentialPolynomialInitial (MvPolynomial.map
        (differentialIntermediateToJetFraction G hG hy).toRingHom P) =
      MvPolynomial.map (differentialIntermediateToJetFraction G hG hy).toRingHom
        (scalarDifferentialPolynomialInitial P) := by
    rw [scalarDifferentialPolynomialInitial, scalarDifferentialPolynomialInitial,
      scalarDifferentialPolynomialLeader_map
        (differentialIntermediateToJetFraction G hG hy).injective,
      mvPolynomialInitialAt_map (differentialIntermediateToJetFraction G hG hy).injective]
  have hSL : scalarDifferentialPolynomialSeparant (MvPolynomial.map
        (differentialIntermediateToJetFraction G hG hy).toRingHom P) =
      MvPolynomial.map (differentialIntermediateToJetFraction G hG hy).toRingHom
        (scalarDifferentialPolynomialSeparant P) :=
    scalarDifferentialPolynomialSeparant_map
      (differentialIntermediateToJetFraction G hG hy).injective P
  have hcert : scalarDifferentialPolynomialInitial (MvPolynomial.map
          (algebraMap (DifferentialPolynomial Unit F)
            (FractionRing (DifferentialPolynomial Unit F)))
          (differentialPolynomialTwoBlockEquiv F A) * B) ^ a *
        (scalarDifferentialPolynomialSeparant (MvPolynomial.map
            (algebraMap (DifferentialPolynomial Unit F)
              (FractionRing (DifferentialPolynomial Unit F)))
            (differentialPolynomialTwoBlockEquiv F A) * B) ^ b *
          MvPolynomial.map
            (algebraMap (DifferentialPolynomial Unit F)
              (FractionRing (DifferentialPolynomial Unit F)))
            (differentialPolynomialTwoBlockEquiv F
              (differentialPolynomialCrossDifference
                (differentialPolynomialTwoBlockCoefficient m Cc.polynomial)
                (differentialPolynomialTwoBlockCoefficient n Cc.polynomial)))) ∈
      differentialPolynomialIterateIdeal (MvPolynomial.map
        (algebraMap (DifferentialPolynomial Unit F)
          (FractionRing (DifferentialPolynomial Unit F)))
        (differentialPolynomialTwoBlockEquiv F A)) := by
    rw [← hB, hIL, hSL, Cc.map_coefficientCrossRelation G hG hy P m n]
    refine differentialPolynomialIterateIdeal_le_of_dvd ⟨B, hB⟩ ?_
    have hrearrange : MvPolynomial.map (differentialIntermediateToJetFraction G hG hy).toRingHom
            (scalarDifferentialPolynomialInitial P) ^ a *
          (MvPolynomial.map (differentialIntermediateToJetFraction G hG hy).toRingHom
              (scalarDifferentialPolynomialSeparant P) ^ b *
            (MvPolynomial.C (Cc.scalar : FractionRing (DifferentialPolynomial Unit F)) *
              MvPolynomial.map (differentialIntermediateToJetFraction G hG hy).toRingHom
                (differentialCharacteristicCoefficientCrossRelation G (P.coeff m) (P.coeff n)
                  (differentialPolynomialTwoBlockCoefficient m Cc.polynomial)
                  (differentialPolynomialTwoBlockCoefficient n Cc.polynomial)))) =
        MvPolynomial.C (Cc.scalar : FractionRing (DifferentialPolynomial Unit F)) *
          (MvPolynomial.map (differentialIntermediateToJetFraction G hG hy).toRingHom
              (scalarDifferentialPolynomialInitial P) ^ a *
            MvPolynomial.map (differentialIntermediateToJetFraction G hG hy).toRingHom
              (scalarDifferentialPolynomialSeparant P) ^ b *
            MvPolynomial.map (differentialIntermediateToJetFraction G hG hy).toRingHom
              (differentialCharacteristicCoefficientCrossRelation G (P.coeff m) (P.coeff n)
                (differentialPolynomialTwoBlockCoefficient m Cc.polynomial)
                (differentialPolynomialTwoBlockCoefficient n Cc.polynomial))) := by
      ring
    rw [hrearrange]
    exact Ideal.mul_mem_left _ _ hsat
  exact exists_twoBlock_controlled_certificate hy hAvarsNonempty hAirr hsqAB horder hcert

end

end GaloisForLFunctions
