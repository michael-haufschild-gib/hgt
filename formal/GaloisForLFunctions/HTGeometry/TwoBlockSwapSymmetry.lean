import GaloisForLFunctions.HTGeometry.TwoBlockCrossDifferenceControlled

/-!
# Block symmetry of a diagonal-vanishing two-block polynomial

A two-block polynomial that vanishes on the diagonal and whose coefficient cross-differences all lie
in a prime ideal has its block swap in that ideal as well.

The mechanism is proportionality: the cross-differences say that the coefficient vector read in the
left block and the coefficient vector read in the right block are proportional modulo the ideal.
Substituting the proportionality into the swapped polynomial turns it into a multiple of the
diagonal, which vanishes identically.

This is the block-symmetry statement of the Lüroth argument in the only form that does not presuppose
an order bound: it is an ideal membership, proved by a finite computation on the coefficient family,
and it needs no divisibility bridge.
-/

namespace GaloisForLFunctions

noncomputable section

variable {F L : Type*} [CommRing F] [Field L]

/-- The diagonal of a two-block polynomial is the sum of its coefficients against the corresponding
left-block monomials. -/
theorem differentialPolynomialTwoBlockDiagonal_eq_sum
    (C : DifferentialPolynomial (Unit ⊕ Unit) F) :
    differentialPolynomialTwoBlockDiagonal C =
      ∑ m ∈ (differentialPolynomialTwoBlockEquiv F C).support,
        differentialPolynomialTwoBlockCoefficient m C * MvPolynomial.monomial m 1 := by
  classical
  rw [differentialPolynomialTwoBlockDiagonal]
  conv_lhs => rw [MvPolynomial.as_sum (differentialPolynomialTwoBlockEquiv F C)]
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.aeval_monomial, differentialPolynomialTwoBlockCoefficient,
    MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul]
  simp

/-- The block swap expands over the right-block monomials with the two roles exchanged. -/
theorem differentialPolynomialTwoBlockSwap_eq_sum
    (C : DifferentialPolynomial (Unit ⊕ Unit) F) :
    differentialPolynomialTwoBlockSwap F C =
      ∑ m ∈ (differentialPolynomialTwoBlockEquiv F C).support,
        differentialPolynomialRight (ι := Unit)
            (differentialPolynomialTwoBlockCoefficient m C) *
          differentialPolynomialLeft (κ := Unit) (MvPolynomial.monomial m 1) := by
  classical
  conv_lhs => rw [differentialPolynomialTwoBlock_reconstruct C]
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, differentialPolynomialTwoBlockSwap_left,
    differentialPolynomialTwoBlockSwap_right]

/-- **Block symmetry from proportionality.**  If every coefficient cross-difference of a
diagonal-vanishing two-block polynomial lies in an ideal, and one coefficient survives the
coefficient map, then the block swap lies in that ideal. -/
theorem twoBlockSwap_mem_of_crossDifference_mem
    (φ : DifferentialPolynomial Unit F →+* L)
    (C : DifferentialPolynomial (Unit ⊕ Unit) F)
    (hdiag : differentialPolynomialTwoBlockDiagonal C = 0)
    {P : Ideal (DifferentialPolynomial Unit L)}
    (hcross : ∀ m n : (Unit × ℕ) →₀ ℕ,
      MvPolynomial.map φ (differentialPolynomialTwoBlockEquiv F
        (differentialPolynomialCrossDifference
          (differentialPolynomialTwoBlockCoefficient m C)
          (differentialPolynomialTwoBlockCoefficient n C))) ∈ P)
    {μ : (Unit × ℕ) →₀ ℕ}
    (hμ : φ (differentialPolynomialTwoBlockCoefficient μ C) ≠ 0) :
    MvPolynomial.map φ (differentialPolynomialTwoBlockEquiv F
      (differentialPolynomialTwoBlockSwap F C)) ∈ P := by
  classical
  set S := (differentialPolynomialTwoBlockEquiv F C).support with hS
  set a : ((Unit × ℕ) →₀ ℕ) → DifferentialPolynomial Unit F :=
    fun m => differentialPolynomialTwoBlockCoefficient m C with ha
  set b : ((Unit × ℕ) →₀ ℕ) → DifferentialPolynomial Unit L :=
    fun m => MvPolynomial.map φ (differentialPolynomialTwoBlockEquiv F
      (differentialPolynomialRight (ι := Unit) (a m))) with hb
  set u : ((Unit × ℕ) →₀ ℕ) → L :=
    fun m => φ (MvPolynomial.monomial m 1) with hu
  -- the swap expands as a combination of the coefficient polynomials read in the right block
  have hswap : MvPolynomial.map φ (differentialPolynomialTwoBlockEquiv F
      (differentialPolynomialTwoBlockSwap F C)) =
      ∑ m ∈ S, MvPolynomial.C (u m) * b m := by
    rw [differentialPolynomialTwoBlockSwap_eq_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_mul, map_mul, differentialPolynomialTwoBlockEquiv_left,
      MvPolynomial.map_C]
    rw [hb, hu]
    ring
  -- the diagonal identity, read after the coefficient map
  have hdiagsum : ∑ m ∈ S, u m * φ (a m) = 0 := by
    have hz := congrArg φ (differentialPolynomialTwoBlockDiagonal_eq_sum C)
    rw [hdiag, map_zero, map_sum] at hz
    calc ∑ m ∈ S, u m * φ (a m)
        = ∑ m ∈ S, φ (a m * MvPolynomial.monomial m 1) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [map_mul, hu, ha]
          ring
      _ = 0 := hz.symm
  -- the cross-differences give proportionality of the two coefficient readings
  have hprop : ∀ m : (Unit × ℕ) →₀ ℕ,
      MvPolynomial.C (φ (a μ)) * b m - MvPolynomial.C (φ (a m)) * b μ ∈ P := by
    intro m
    have hc := hcross m μ
    rw [differentialPolynomialCrossDifference] at hc
    rw [map_sub, map_sub, map_mul, map_mul, map_mul, map_mul,
      differentialPolynomialTwoBlockEquiv_left, differentialPolynomialTwoBlockEquiv_left,
      MvPolynomial.map_C, MvPolynomial.map_C] at hc
    exact hc
  -- assemble
  have hkey : MvPolynomial.C (φ (a μ)) *
      MvPolynomial.map φ (differentialPolynomialTwoBlockEquiv F
        (differentialPolynomialTwoBlockSwap F C)) =
      ∑ m ∈ S, MvPolynomial.C (u m) *
        (MvPolynomial.C (φ (a μ)) * b m - MvPolynomial.C (φ (a m)) * b μ) +
        MvPolynomial.C (∑ m ∈ S, u m * φ (a m)) * b μ := by
    rw [hswap, Finset.mul_sum, map_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_mul]
    ring
  have hmem : MvPolynomial.C (φ (a μ)) *
      MvPolynomial.map φ (differentialPolynomialTwoBlockEquiv F
        (differentialPolynomialTwoBlockSwap F C)) ∈ P := by
    rw [hkey, hdiagsum, map_zero, zero_mul, add_zero]
    exact Ideal.sum_mem _ fun m _ => Ideal.mul_mem_left _ _ (hprop m)
  have hunit : IsUnit (MvPolynomial.C (φ (a μ)) :
      DifferentialPolynomial Unit L) := by
    refine IsUnit.map MvPolynomial.C ?_
    exact (isUnit_iff_ne_zero).2 hμ
  obtain ⟨v, hv⟩ := hunit.exists_left_inv
  have hrecover : v * (MvPolynomial.C (φ (a μ)) *
      MvPolynomial.map φ (differentialPolynomialTwoBlockEquiv F
        (differentialPolynomialTwoBlockSwap F C))) =
      MvPolynomial.map φ (differentialPolynomialTwoBlockEquiv F
        (differentialPolynomialTwoBlockSwap F C)) := by
    rw [← mul_assoc, hv, one_mul]
  rw [← hrecover]
  exact Ideal.mul_mem_left _ _ hmem

open scoped Differential

/-- **The coefficient cross-differences lie in the component of an irreducible factor.**

The corpus's saturation certificate puts a multiple of each cross-difference in the differential
ideal of the cleared characteristic, hence in the component of any factor; the initial and the
separant of the characteristic are outside that component, so the cross-difference itself lies in
it. -/
theorem exists_component_crossDifference_mem
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
    {A : DifferentialPolynomial (Unit ⊕ Unit) F}
    (hAdvd : A ∣ Cc.polynomial)
    (hAvars : (differentialPolynomialTwoBlockEquiv F A).vars = P.vars)
    (hAirr : Irreducible (MvPolynomial.map
      (algebraMap (DifferentialPolynomial Unit F)
        (FractionRing (DifferentialPolynomial Unit F)))
      (differentialPolynomialTwoBlockEquiv F A))) :
    letI : Differential (DifferentialPolynomial Unit F) := differentialPolynomialDifferential F
    letI : Differential (FractionRing (DifferentialPolynomial Unit F)) :=
      differentialIndependentJetFractionDifferential y hy
    ∃ Pc : Ideal (DifferentialPolynomial Unit
        (FractionRing (DifferentialPolynomial Unit F))),
      Pc.IsPrime ∧
        differentialPolynomialIterateIdeal (MvPolynomial.map
          (algebraMap (DifferentialPolynomial Unit F)
            (FractionRing (DifferentialPolynomial Unit F)))
          (differentialPolynomialTwoBlockEquiv F A)) ≤ Pc ∧
        (∀ Z : DifferentialPolynomial Unit (FractionRing (DifferentialPolynomial Unit F)),
          Z ∈ Pc → scalarDifferentialPolynomialOrder Z ≤
            scalarDifferentialPolynomialOrder (MvPolynomial.map
              (algebraMap (DifferentialPolynomial Unit F)
                (FractionRing (DifferentialPolynomial Unit F)))
              (differentialPolynomialTwoBlockEquiv F A)) →
          MvPolynomial.map
            (algebraMap (DifferentialPolynomial Unit F)
              (FractionRing (DifferentialPolynomial Unit F)))
            (differentialPolynomialTwoBlockEquiv F A) ∣ Z) ∧
        ∀ m n : (Unit × ℕ) →₀ ℕ,
          MvPolynomial.map
            (algebraMap (DifferentialPolynomial Unit F)
              (FractionRing (DifferentialPolynomial Unit F)))
            (differentialPolynomialTwoBlockEquiv F
              (differentialPolynomialCrossDifference
                (differentialPolynomialTwoBlockCoefficient m Cc.polynomial)
                (differentialPolynomialTwoBlockCoefficient n Cc.polynomial))) ∈ Pc := by
  classical
  letI : Differential (DifferentialPolynomial Unit F) := differentialPolynomialDifferential F
  letI : Differential (FractionRing (DifferentialPolynomial Unit F)) :=
    differentialIndependentJetFractionDifferential y hy
  letI : Differential G := derivationClosedDifferential G hGclosed
  letI : Algebra G (FractionRing (DifferentialPolynomial Unit F)) :=
    (differentialIntermediateToJetFraction G hG hy).toRingHom.toAlgebra
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
  obtain ⟨B, hB⟩ := hassoc.dvd_iff_dvd_right.mp hdvdmap
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
  have hA'vars : (MvPolynomial.map
      (algebraMap (DifferentialPolynomial Unit F)
        (FractionRing (DifferentialPolynomial Unit F)))
      (differentialPolynomialTwoBlockEquiv F A)).vars.Nonempty := by
    obtain ⟨j, hj⟩ := hAvarsNonempty
    refine ⟨j, ?_⟩
    rw [MvPolynomial.vars_map_of_injective _
      (IsFractionRing.injective (DifferentialPolynomial Unit F)
        (FractionRing (DifferentialPolynomial Unit F)))]
    exact hj
  obtain ⟨Pc, hPcprime, hPcle, hPcdvd, _hinit, _hsep, _hirr⟩ :=
    exists_component_prime_of_irreducible hA'vars hAirr
  refine ⟨Pc, hPcprime, hPcle, hPcdvd, ?_⟩
  intro m n
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
  refine mem_of_initial_separant_powers_mem (a := a) (b := b) hAirr hA'vars hsqAB horder
    hPcprime hPcdvd ?_
  rw [← hB, hIL, hSL, Cc.map_coefficientCrossRelation G hG hy P m n]
  refine hPcle (differentialPolynomialIterateIdeal_le_of_dvd ⟨B, hB⟩ ?_)
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

/-- **The block swap is saturated into the differential ideal of an irreducible factor.**

Powers of the initial and the separant of the factor absorb the block swap of the cleared
characteristic into the factor's differential ideal, in the two-block ring over `F`.  This is block
symmetry in the form that needs no order bound: the cross-differences put the two coefficient
readings in proportion inside the component, the diagonal vanishing turns the swap into a multiple
of the diagonal there, and the ring-level Ritt reduction converts component membership into a
certificate whose multiplier is built from the factor. -/
theorem exists_twoBlock_swap_controlled_saturation
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
          differentialPolynomialTwoBlockSwap F Cc.polynomial ∈
        differentialPolynomialFamilyIterateIdeal A := by
  classical
  letI : Differential (DifferentialPolynomial Unit F) := differentialPolynomialDifferential F
  letI : Differential (FractionRing (DifferentialPolynomial Unit F)) :=
    differentialIndependentJetFractionDifferential y hy
  obtain ⟨Pc, hPcprime, hPcle, hPcdvd, hcross⟩ :=
    exists_component_crossDifference_mem G hGclosed hG hy P hP hPirr Cc hAdvd hAvars hAirr
  have hAvarsNonempty : (differentialPolynomialTwoBlockEquiv F A).vars.Nonempty := by
    rw [hAvars]
    exact hP.2.2.1
  -- a surviving coefficient
  have hCne : differentialPolynomialTwoBlockEquiv F Cc.polynomial ≠ 0 :=
    (differentialPolynomialTwoBlockEquiv F).injective.ne Cc.ne_zero
  obtain ⟨μ, hμsupp⟩ : (differentialPolynomialTwoBlockEquiv F Cc.polynomial).support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    exact hCne (MvPolynomial.support_eq_empty.mp hempty)
  have hμ : algebraMap (DifferentialPolynomial Unit F)
      (FractionRing (DifferentialPolynomial Unit F))
      (differentialPolynomialTwoBlockCoefficient μ Cc.polynomial) ≠ 0 := by
    refine fun h0 => (MvPolynomial.mem_support_iff.mp hμsupp) ?_
    have hzero : differentialPolynomialTwoBlockCoefficient μ Cc.polynomial = 0 :=
      IsFractionRing.injective (DifferentialPolynomial Unit F)
        (FractionRing (DifferentialPolynomial Unit F)) (by simpa using h0)
    exact hzero
  have hswapmem := twoBlockSwap_mem_of_crossDifference_mem
    (algebraMap (DifferentialPolynomial Unit F)
      (FractionRing (DifferentialPolynomial Unit F)))
    Cc.polynomial Cc.diagonal hcross hμ
  obtain ⟨a, b, hmem⟩ := exists_oracle_initial_separant_powers_mem_diffPolyIterateIdeal
    (algebraMap (DifferentialPolynomial Unit F)
      (FractionRing (DifferentialPolynomial Unit F)))
    (IsFractionRing.injective (DifferentialPolynomial Unit F)
      (FractionRing (DifferentialPolynomial Unit F)))
    (algebraMap_jetFraction_deriv hy) hAvarsNonempty hPcle hPcdvd hswapmem
  refine ⟨a, b, mem_familyIterateIdeal_of_twoBlockEquiv_mem ?_⟩
  rw [map_mul, AlgEquiv.apply_symm_apply, mul_assoc]
  exact hmem

end

end GaloisForLFunctions
