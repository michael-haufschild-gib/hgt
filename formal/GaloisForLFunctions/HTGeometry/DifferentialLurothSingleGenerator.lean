import GaloisForLFunctions.HTGeometry.TwoBlockCoefficientEvaluation
import GaloisForLFunctions.HTGeometry.TwoBlockOrderSymmetry
import GaloisForLFunctions.HTGeometry.LurothLowRankCriterion
import GaloisForLFunctions.HTGeometry.RatioFieldReciprocity

/-!
# A single generator for an intermediate differential field

An intermediate differential field of a free differential field is generated, as a differential
field, by one element.

The generator is a ratio of two coefficients of the cleared two-block characteristic.  That such a
ratio generates is the low-rank criterion; its hypotheses are the block symmetry of the cleared
characteristic together with the fact that a coefficient of a split polynomial has no larger jet
degree than the polynomial, which together bound the order and the leader degree of the numerator and
the denominator by those of the characteristic relation.  A ratio outside the base field exists
because the ratios generate the intermediate field.
-/

namespace GaloisForLFunctions

open scoped Differential

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Differential F] [Differential E] [Algebra F E]
  [DifferentialAlgebra F E] [CharZero F] [CharZero E]

omit [CharZero F] [CharZero E] in
/-- The base field is closed under the derivation. -/
theorem derivationClosed_bot : DerivationClosed (⊥ : IntermediateField F E) := by
  intro x hx
  obtain ⟨a, rfl⟩ := IntermediateField.mem_bot.mp hx
  rw [DifferentialAlgebra.deriv_algebraMap a]
  exact IntermediateField.mem_bot.mpr ⟨a′, rfl⟩

omit [Differential F] [DifferentialAlgebra F E] [CharZero F] [CharZero E] in
/-- Every jet degree of the cleared characteristic is a jet degree of the characteristic
relation. -/
theorem twoBlockEquiv_degreeOf_eq
    (G : IntermediateField F E) {y : E}
    (hG : G ≤ differentialAdjoin F ({y} : Set E))
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    (P : DifferentialPolynomial Unit G)
    (Cc : PrimitiveTwoBlockDifferentialCharacteristic G hG hy P) (v : Unit × ℕ) :
    MvPolynomial.degreeOf v (differentialPolynomialTwoBlockEquiv F Cc.polynomial) =
      MvPolynomial.degreeOf v P := by
  classical
  have hinj : Function.Injective (algebraMap (DifferentialPolynomial Unit F)
      (FractionRing (DifferentialPolynomial Unit F))) := IsFractionRing.injective _ _
  have hC0 : (MvPolynomial.C (Cc.scalar : FractionRing (DifferentialPolynomial Unit F)) :
      DifferentialPolynomial Unit (FractionRing (DifferentialPolynomial Unit F))) ≠ 0 :=
    MvPolynomial.C_ne_zero.mpr Cc.scalar.ne_zero
  have hmapPne : MvPolynomial.map
      (differentialIntermediateToJetFraction G hG hy).toRingHom P ≠ 0 := by
    intro h0
    have hzero : MvPolynomial.map (algebraMap (DifferentialPolynomial Unit F)
        (FractionRing (DifferentialPolynomial Unit F)))
        (differentialPolynomialTwoBlockEquiv F Cc.polynomial) = 0 := by
      rw [Cc.clearing, h0, mul_zero]
    have hequiv0 : differentialPolynomialTwoBlockEquiv F Cc.polynomial = 0 :=
      MvPolynomial.map_injective _ hinj (by simpa using hzero)
    exact Cc.ne_zero ((differentialPolynomialTwoBlockEquiv F).injective (by simpa using hequiv0))
  have hleft : MvPolynomial.degreeOf v (differentialPolynomialTwoBlockEquiv F Cc.polynomial) =
      MvPolynomial.degreeOf v (MvPolynomial.map
        (algebraMap (DifferentialPolynomial Unit F)
          (FractionRing (DifferentialPolynomial Unit F)))
        (differentialPolynomialTwoBlockEquiv F Cc.polynomial)) := by
    rw [MvPolynomial.degreeOf_eq_sup, MvPolynomial.degreeOf_eq_sup,
      MvPolynomial.support_map_of_injective _ hinj]
  have hrightmap : MvPolynomial.degreeOf v (MvPolynomial.map
      (differentialIntermediateToJetFraction G hG hy).toRingHom P) =
      MvPolynomial.degreeOf v P := by
    rw [MvPolynomial.degreeOf_eq_sup, MvPolynomial.degreeOf_eq_sup,
      MvPolynomial.support_map_of_injective _
        (differentialIntermediateToJetFraction G hG hy).injective]
  rw [hleft, Cc.clearing, MvPolynomial.degreeOf_mul_eq hC0 hmapPne, hrightmap]
  have hCdeg : MvPolynomial.degreeOf v
      (MvPolynomial.C (Cc.scalar : FractionRing (DifferentialPolynomial Unit F)) :
        DifferentialPolynomial Unit (FractionRing (DifferentialPolynomial Unit F))) = 0 := by
    simp [MvPolynomial.degreeOf_C]
  rw [hCdeg, Nat.zero_add]

/-- **A single generator.**  Some ratio of two coefficients of the cleared characteristic generates
the intermediate field as a differential field. -/
theorem exists_differentialLuroth_generator
    (G : IntermediateField F E) (hGclosed : DerivationClosed G) {y : E}
    (hG : G ≤ differentialAdjoin F ({y} : Set E))
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    (P : DifferentialPolynomial Unit G)
    (hP : IsMinimalScalarDifferentialPolynomialRank
      (differentialIntermediateRelationIdeal G y : Set _) P)
    (hPirr : Irreducible P)
    (Cc : PrimitiveTwoBlockDifferentialCharacteristic G hG hy P)
    (hGbot : G ≠ ⊥) :
    ∃ w : E, differentialAdjoin F ({w} : Set E) = G := by
  classical
  obtain ⟨μ, hμ⟩ := MvPolynomial.exists_coeff_ne_zero hPirr.ne_zero
  -- a coefficient ratio outside the base field
  obtain ⟨ν, hν⟩ : ∃ ν : (Unit × ℕ) →₀ ℕ,
      ((P.coeff ν / P.coeff μ : G) : E) ∉ (⊥ : IntermediateField F E) := by
    by_contra hno
    push Not at hno
    refine hGbot ?_
    refine le_antisymm ?_ bot_le
    calc G = characteristicDifferentialRatioField G P μ :=
          (characteristicDifferentialRatioField_eq G hGclosed hG hP hμ).symm
      _ ≤ (⊥ : IntermediateField F E) := by
          refine differentialAdjoin_le F ?_ derivationClosed_bot
          rintro x ⟨m, rfl⟩
          exact hno m
  -- the evaluations of the two coefficients
  obtain ⟨c, hc, hcoeff⟩ := exists_scalar_twoBlockCoefficient_eval G hG hy P Cc
  have hKne : differentialPolynomialEvalOver (K := F) (fun _ : Unit ↦ y)
      (differentialPolynomialTwoBlockCoefficient μ Cc.polynomial) ≠ 0 :=
    (twoBlockCoefficient_eval_ne_zero_iff G hG hy P Cc hc hcoeff μ).2 hμ
  have hdiv := twoBlockCoefficient_eval_div G hG hy P Cc hc hcoeff
  -- the jet bounds for the coefficients
  have hdegbound : ∀ (σ : (Unit × ℕ) →₀ ℕ) (k : ℕ),
      MvPolynomial.degreeOf (((), k) : Unit × ℕ)
        (differentialPolynomialTwoBlockCoefficient σ Cc.polynomial) ≤
      MvPolynomial.degreeOf (((), k) : Unit × ℕ) P := by
    intro σ k
    calc MvPolynomial.degreeOf (((), k) : Unit × ℕ)
          (differentialPolynomialTwoBlockCoefficient σ Cc.polynomial)
        ≤ MvPolynomial.degreeOf ((Sum.inl () : Unit ⊕ Unit), k) Cc.polynomial :=
          degreeOf_twoBlockCoefficient_le Cc.polynomial σ k
      _ = MvPolynomial.degreeOf ((Sum.inr () : Unit ⊕ Unit), k) Cc.polynomial :=
          twoBlock_degreeOf_inl_eq_degreeOf_inr G hGclosed hG hy P hP hPirr Cc k
      _ = MvPolynomial.degreeOf (((), k) : Unit × ℕ)
            (differentialPolynomialTwoBlockEquiv F Cc.polynomial) :=
          (degreeOf_twoBlockEquiv_inr Cc.polynomial k).symm
      _ = MvPolynomial.degreeOf (((), k) : Unit × ℕ) P :=
          twoBlockEquiv_degreeOf_eq G hG hy P Cc ((), k)
  have hordbound : ∀ (σ : (Unit × ℕ) →₀ ℕ),
      ∀ q ∈ (differentialPolynomialTwoBlockCoefficient σ Cc.polynomial).vars,
        q.2 ≤ scalarDifferentialPolynomialOrder P := by
    intro σ q hq
    obtain ⟨u, k⟩ := q
    obtain rfl : u = () := Subsingleton.elim _ _
    by_contra hk
    have hPzero : MvPolynomial.degreeOf (((), k) : Unit × ℕ) P = 0 := by
      by_contra hPne
      have hmem : (((), k) : Unit × ℕ) ∈ P.vars :=
        MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mpr hPne
      have hle : k ≤ scalarDifferentialPolynomialOrder P :=
        Finset.le_sup (f := fun p : Unit × ℕ ↦ p.2) hmem
      omega
    have hzero : MvPolynomial.degreeOf (((), k) : Unit × ℕ)
        (differentialPolynomialTwoBlockCoefficient σ Cc.polynomial) = 0 := by
      have := hdegbound σ k
      omega
    exact (MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hq) hzero
  refine ⟨differentialPolynomialEvalOver (K := F) (fun _ : Unit ↦ y)
      (differentialPolynomialTwoBlockCoefficient ν Cc.polynomial) /
    differentialPolynomialEvalOver (K := F) (fun _ : Unit ↦ y)
      (differentialPolynomialTwoBlockCoefficient μ Cc.polynomial), ?_⟩
  refine eq_differentialAdjoin_of_ratio_rank_le G hGclosed hG hP hKne ?_ ?_
    (hordbound ν) (hordbound μ) ?_ ?_
  · rw [hdiv ν μ]
    exact (P.coeff ν / P.coeff μ).2
  · rw [hdiv ν μ]
    exact hν
  · exact hdegbound ν (scalarDifferentialPolynomialOrder P)
  · exact hdegbound μ (scalarDifferentialPolynomialOrder P)

/-- **The differential Lüroth theorem.**  Every derivation-closed intermediate field strictly above
the base, inside a free differential field on one generator, is itself generated by one element.

The characteristic relation and its primitive two-block clearing are produced by the corpus's kernel
theory from any nonconstant element of the intermediate field; the generator is then a ratio of two
coefficients of that clearing. -/
theorem differentialLuroth
    (G : IntermediateField F E) (hGclosed : DerivationClosed G) {y : E}
    (hG : G ≤ differentialAdjoin F ({y} : Set E))
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    (hGbot : G ≠ ⊥) :
    ∃ w : E, differentialAdjoin F ({w} : Set E) = G := by
  classical
  -- a nonconstant element of the intermediate field
  obtain ⟨u, huF⟩ : ∃ u : G, (u : E) ∉ (⊥ : IntermediateField F E) := by
    by_contra hno
    push Not at hno
    exact hGbot (le_antisymm (fun x hx => hno ⟨x, hx⟩) bot_le)
  -- the irreducible characteristic of minimal rank
  obtain ⟨P, hP, hPirr⟩ :=
    exists_irreducible_minimal_differentialKernelCharacteristic G hG u huF
  -- its primitive two-block clearing
  obtain ⟨Cc⟩ := exists_primitiveTwoBlockDifferentialCharacteristic G hG hy hPirr.ne_zero hP.1
  exact exists_differentialLuroth_generator G hGclosed hG hy P hP hPirr Cc hGbot

end

end GaloisForLFunctions
