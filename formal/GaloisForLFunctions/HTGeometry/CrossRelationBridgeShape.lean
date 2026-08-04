import GaloisForLFunctions.HTGeometry.SeparantCoefficientMap
import GaloisForLFunctions.HTGeometry.DifferentialLurothComponentTransfer

/-!
# The saturation, in the shape the divisibility bridge consumes

The characteristic saturation produces a membership of the form
`initial^a · separant^b · crossRelation ∈ iterateIdeal`, with the separant taken *before* mapping,
while the divisibility bridge wants `separant(mapped)^e · Q ∈ iterateIdeal(mapped)`.

Since an injective coefficient map commutes with the separant, the two are the same statement after a
commutation; this file performs that rearrangement so the bridge applies verbatim.
-/

namespace GaloisForLFunctions

open MvPolynomial

noncomputable section

/-- **The saturation membership, rearranged for the divisibility bridge.** -/
theorem exists_separant_pow_mul_mem_iterateIdeal_of_saturation
    {F E : Type*} [Field F] [Field E]
    [Differential F] [Differential E] [Algebra F E] [DifferentialAlgebra F E]
    [CharZero E]
    (G : IntermediateField F E) (hGclosed : DerivationClosed G) {y : E}
    (hG : G ≤ differentialAdjoin F ({y} : Set E))
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    (P : DifferentialPolynomial Unit G)
    (hP : IsMinimalScalarDifferentialPolynomialRank
      (differentialIntermediateRelationIdeal G y : Set _) P)
    (C : PrimitiveTwoBlockDifferentialCharacteristic G hG hy P)
    (m n : (Unit × ℕ) →₀ ℕ) :
    letI : Differential G := derivationClosedDifferential G hGclosed
    letI : Differential (FractionRing (DifferentialPolynomial Unit F)) :=
      differentialIndependentJetFractionDifferential y hy
    ∃ a b : ℕ,
      scalarDifferentialPolynomialSeparant
          (MvPolynomial.map
            (differentialIntermediateToJetFraction G hG hy).toRingHom P) ^ b *
        (MvPolynomial.map (differentialIntermediateToJetFraction G hG hy).toRingHom
              (scalarDifferentialPolynomialInitial P) ^ a *
          MvPolynomial.map (differentialIntermediateToJetFraction G hG hy).toRingHom
            (differentialCharacteristicCoefficientCrossRelation G (P.coeff m) (P.coeff n)
              (differentialPolynomialTwoBlockCoefficient m C.polynomial)
              (differentialPolynomialTwoBlockCoefficient n C.polynomial)))
        ∈ differentialPolynomialIterateIdeal
          (MvPolynomial.map
            (differentialIntermediateToJetFraction G hG hy).toRingHom P) := by
  letI : Differential G := derivationClosedDifferential G hGclosed
  letI : Differential (FractionRing (DifferentialPolynomial Unit F)) :=
    differentialIndependentJetFractionDifferential y hy
  obtain ⟨a, b, hmem⟩ :=
    PrimitiveTwoBlockDifferentialCharacteristic.exists_mappedCrossRelation_saturation
      G hGclosed hG hy P hP C m n
  refine ⟨a, b, ?_⟩
  have hsep : scalarDifferentialPolynomialSeparant
      (MvPolynomial.map (differentialIntermediateToJetFraction G hG hy).toRingHom P)
      = MvPolynomial.map (differentialIntermediateToJetFraction G hG hy).toRingHom
        (scalarDifferentialPolynomialSeparant P) :=
    scalarDifferentialPolynomialSeparant_map
      (differentialIntermediateToJetFraction G hG hy).injective P
  rw [hsep]
  have hcomm : ∀ u v w : DifferentialPolynomial Unit
      (FractionRing (DifferentialPolynomial Unit F)),
      v * (u * w) = u * v * w := by
    intro u v w
    ring
  rw [hcomm]
  exact hmem

end

end GaloisForLFunctions
