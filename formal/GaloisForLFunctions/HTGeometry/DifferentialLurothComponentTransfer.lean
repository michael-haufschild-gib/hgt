import GaloisForLFunctions.HTGeometry.DifferentialLurothCoefficient
import GaloisForLFunctions.HTGeometry.DifferentialLurothScalarExtensionSquarefree

/-!
# Component transfer for the differential Luroth coefficient theorem

This file moves the characteristic saturation from the intermediate coefficient field to the
formal fraction field of one free jet palette.  The fraction field is equipped with the derivation
transported through the canonical free-jet parametrization, so the coefficient embedding really
commutes with total differentiation; it is not treated as a constant-coefficient map.

The resulting package has three parts.

* total derivatives and their generated ideal commute with a derivation-preserving coefficient
  embedding;
* the coefficient cross-relation belongs to the characteristic saturation and its image is exactly
  the two-copy cross-difference, up to the single denominator-clearing unit;
* equation (78) implies that the cleared characteristic is squarefree after passage to the formal
  fraction field, even though its irreducibility need not survive scalar extension.

These are the componentwise inputs to Ritt's reciprocity argument.  No finite-generation
hypothesis on the intermediate differential field is introduced.
-/

open scoped Differential

namespace GaloisForLFunctions

noncomputable section

/-! ## The differential structure on the formal free-jet fraction field -/

/-- Transport the ambient derivation to the rational formal-jet field through the canonical
parametrization.  This presentation is intentionally tied to `y`: it makes the inverse
parametrization, and hence every restricted intermediate-field coefficient, commute with the
derivation definitionally up to the displayed equivalence. -/
@[reducible]
noncomputable def differentialIndependentJetFractionDifferential
    {F E : Type*} [Field F] [Field E]
    [Differential F] [Differential E] [Algebra F E] [DifferentialAlgebra F E]
    (y : E) (hy : DifferentialIndependent F (fun _ : Unit ↦ y)) :
    Differential (FractionRing (DifferentialPolynomial Unit F)) := by
  let K := FractionRing (DifferentialPolynomial Unit F)
  let A := differentialAdjoin F (Set.range fun _ : Unit ↦ y)
  let e : K ≃ₐ[F] A :=
    differentialIndependentAdjoinParametrization (fun _ : Unit ↦ y) hy
  exact
    { deriv :=
        { toLinearMap :=
            { toFun := fun z ↦ e.symm ((e z)′)
              map_add' := by
                intro z w
                simp
              map_smul' := by
                intro n z
                simp }
          map_one_eq_zero' := by simp
          leibniz' := by
            intro z w
            change e.symm ((e (z * w))′) =
              z • e.symm ((e w)′) + w • e.symm ((e z)′)
            simp only [map_mul, Derivation.leibniz, map_add, map_smul]
            simp [smul_eq_mul, mul_comm] } }

/-- The transported formal-jet derivation is intertwined by the free-jet parametrization. -/
@[simp]
theorem differentialIndependentJetFraction_deriv
    {F E : Type*} [Field F] [Field E]
    [Differential F] [Differential E] [Algebra F E] [DifferentialAlgebra F E]
    (y : E) (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    (z : FractionRing (DifferentialPolynomial Unit F)) :
    letI : Differential (FractionRing (DifferentialPolynomial Unit F)) :=
      differentialIndependentJetFractionDifferential y hy
    differentialIndependentAdjoinParametrization (fun _ : Unit ↦ y) hy z′ =
      (differentialIndependentAdjoinParametrization (fun _ : Unit ↦ y) hy z)′ := by
  let K := FractionRing (DifferentialPolynomial Unit F)
  let A := differentialAdjoin F (Set.range fun _ : Unit ↦ y)
  let e : K ≃ₐ[F] A :=
    differentialIndependentAdjoinParametrization (fun _ : Unit ↦ y) hy
  change e (e.symm ((e z)′)) = (e z)′
  exact e.apply_symm_apply _

/-- The inverse free-jet coordinate map on a derivation-closed intermediate field commutes with
the restricted derivation. -/
theorem differentialIntermediateToJetFraction_deriv
    {F E : Type*} [Field F] [Field E]
    [Differential F] [Differential E] [Algebra F E] [DifferentialAlgebra F E]
    (G : IntermediateField F E) (hGclosed : DerivationClosed G) {y : E}
    (hG : G ≤ differentialAdjoin F ({y} : Set E))
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y)) (g : G) :
    letI : Differential G := derivationClosedDifferential G hGclosed
    letI : Differential (FractionRing (DifferentialPolynomial Unit F)) :=
      differentialIndependentJetFractionDifferential y hy
    (differentialIntermediateToJetFraction G hG hy g)′ =
      differentialIntermediateToJetFraction G hG hy g′ := by
  let K := FractionRing (DifferentialPolynomial Unit F)
  let A := differentialAdjoin F (Set.range fun _ : Unit ↦ y)
  let e : K ≃ₐ[F] A :=
    differentialIndependentAdjoinParametrization (fun _ : Unit ↦ y) hy
  let φ : G →ₐ[F] K := differentialIntermediateToJetFraction G hG hy
  apply e.injective
  rw [differentialIndependentJetFraction_deriv]
  apply Subtype.ext
  simp [e, φ, A, differentialIntermediateToJetFraction,
    derivationClosedDifferential_apply]

/-! ## Total derivatives commute with coefficient embeddings -/

/-- Mapping coefficients through a derivation-preserving ring homomorphism commutes with the total
differential-polynomial derivation. -/
theorem map_differentialPolynomialOverDerivation_of_commutes
    {K L ι : Type*} [CommRing K] [CommRing L]
    [Differential K] [Differential L]
    (f : K →+* L) (hf : ∀ c : K, f c′ = (f c)′)
    (P : DifferentialPolynomial ι K) :
    MvPolynomial.map f (differentialPolynomialOverDerivation ι K P) =
      differentialPolynomialOverDerivation ι L (MvPolynomial.map f P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      simp only [differentialPolynomialOverDerivation_C, MvPolynomial.map_C]
      exact congrArg MvPolynomial.C (hf c)
  | add P Q hP hQ =>
      simp only [map_add, hP, hQ]
  | mul_X P j hP =>
      rcases j with ⟨i, n⟩
      simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, hP,
        differentialPolynomialOverDerivation_X, MvPolynomial.map_X]

/-- Every iterated total derivative commutes with a derivation-preserving coefficient map. -/
theorem map_differentialPolynomialIterateOver_of_commutes
    {K L : Type*} [Field K] [Field L]
    [Differential K] [Differential L]
    (f : K →+* L) (hf : ∀ c : K, f c′ = (f c)′)
    (n : ℕ) (P : DifferentialPolynomial Unit K) :
    MvPolynomial.map f (differentialPolynomialIterateOver n P) =
      differentialPolynomialIterateOver n (MvPolynomial.map f P) := by
  induction n with
  | zero => rfl
  | succ n hn =>
      rw [differentialPolynomialIterateOver_succ,
        differentialPolynomialIterateOver_succ,
        map_differentialPolynomialOverDerivation_of_commutes, hn]

/-- The differential principal ideal generated by one polynomial maps into the differential
principal ideal generated by its coefficient image. -/
theorem map_mem_differentialPolynomialIterateIdeal_of_commutes
    {K L : Type*} [Field K] [Field L]
    [Differential K] [Differential L]
    (f : K →+* L) (hf : ∀ c : K, f c′ = (f c)′)
    {P Q : DifferentialPolynomial Unit K}
    (hQ : Q ∈ differentialPolynomialIterateIdeal P) :
    MvPolynomial.map f Q ∈
      differentialPolynomialIterateIdeal (MvPolynomial.map f P) := by
  let R := DifferentialPolynomial Unit K
  change Q ∈ Submodule.span R
    (Set.range fun n : ℕ ↦ differentialPolynomialIterateOver n P) at hQ
  refine Submodule.span_induction (hx := hQ) ?_ ?_ ?_ ?_
  · rintro _ ⟨n, rfl⟩
    rw [map_differentialPolynomialIterateOver_of_commutes f hf]
    exact differentialPolynomialIterateOver_mem_iterateIdeal _ _
  · simpa using (Ideal.zero_mem
      (differentialPolynomialIterateIdeal (MvPolynomial.map f P)))
  · intro A B _ _ hA hB
    simpa using (Ideal.add_mem _ hA hB)
  · intro a A _ hA
    simpa [smul_eq_mul] using
      (differentialPolynomialIterateIdeal (MvPolynomial.map f P)).mul_mem_left
        (MvPolynomial.map f a) hA

/-! ## The coefficient cross-relation and characteristic saturation -/

/-- The relation over the intermediate coefficient field obtained from two cleared coefficients.
Its image in the free-jet fraction field is the two-copy projective cross-difference, apart from
the one common clearing unit. -/
def differentialCharacteristicCoefficientCrossRelation
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (G : IntermediateField F E) (p q : G)
    (P Q : DifferentialPolynomial Unit F) :
    DifferentialPolynomial Unit G :=
  MvPolynomial.C q * MvPolynomial.map (algebraMap F G) P -
    MvPolynomial.C p * MvPolynomial.map (algebraMap F G) Q

/-- The cross-relation of two characteristic coefficients vanishes at the original free element. -/
theorem PrimitiveTwoBlockDifferentialCharacteristic.coefficientCrossRelation_mem
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (G : IntermediateField F E) {y : E}
    (hG : G ≤ differentialAdjoin F ({y} : Set E))
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    (P : DifferentialPolynomial Unit G)
    (C : PrimitiveTwoBlockDifferentialCharacteristic G hG hy P)
    (m n : (Unit × ℕ) →₀ ℕ) :
    differentialCharacteristicCoefficientCrossRelation G (P.coeff m) (P.coeff n)
        (differentialPolynomialTwoBlockCoefficient m C.polynomial)
        (differentialPolynomialTwoBlockCoefficient n C.polynomial) ∈
      differentialIntermediateRelationIdeal G y := by
  change differentialPolynomialEvalOver (K := G) (fun _ : Unit ↦ y)
      (differentialCharacteristicCoefficientCrossRelation G (P.coeff m) (P.coeff n)
        (differentialPolynomialTwoBlockCoefficient m C.polynomial)
        (differentialPolynomialTwoBlockCoefficient n C.polynomial)) = 0
  simp only [differentialCharacteristicCoefficientCrossRelation, map_sub, map_mul,
    differentialPolynomialEvalOver_C,
    differentialPolynomialEvalOver_map_intermediate]
  rw [C.coefficient_specialization G hG hy P m,
    C.coefficient_specialization G hG hy P n]
  ring

/-- After mapping to the formal fraction field, the coefficient cross-relation is exactly the
two-block cross-difference multiplied by the denominator-clearing unit. -/
theorem PrimitiveTwoBlockDifferentialCharacteristic.map_coefficientCrossRelation
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (G : IntermediateField F E) {y : E}
    (hG : G ≤ differentialAdjoin F ({y} : Set E))
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    (P : DifferentialPolynomial Unit G)
    (C : PrimitiveTwoBlockDifferentialCharacteristic G hG hy P)
    (m n : (Unit × ℕ) →₀ ℕ) :
    let R := DifferentialPolynomial Unit F
    let K := FractionRing R
    let φ : G →ₐ[F] K := differentialIntermediateToJetFraction G hG hy
    MvPolynomial.map (algebraMap R K)
        (differentialPolynomialTwoBlockEquiv F
          (differentialPolynomialCrossDifference
            (differentialPolynomialTwoBlockCoefficient m C.polynomial)
            (differentialPolynomialTwoBlockCoefficient n C.polynomial))) =
      MvPolynomial.C (C.scalar : K) *
        MvPolynomial.map φ.toRingHom
          (differentialCharacteristicCoefficientCrossRelation G
            (P.coeff m) (P.coeff n)
            (differentialPolynomialTwoBlockCoefficient m C.polynomial)
            (differentialPolynomialTwoBlockCoefficient n C.polynomial)) := by
  let R := DifferentialPolynomial Unit F
  let K := FractionRing R
  let φ : G →ₐ[F] K := differentialIntermediateToJetFraction G hG hy
  let P₀ := differentialPolynomialTwoBlockCoefficient m C.polynomial
  let Q₀ := differentialPolynomialTwoBlockCoefficient n C.polynomial
  have hm := congrArg (MvPolynomial.coeff m) C.clearing
  have hn := congrArg (MvPolynomial.coeff n) C.clearing
  simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul] at hm hn
  have hbaseR :
      (algebraMap R K).comp (MvPolynomial.C : F →+* R) = algebraMap F K := by
    ext c
    simp [R, K]
  have hbaseG : φ.toRingHom.comp (algebraMap F G) = algebraMap F K := by
    ext c
    exact φ.commutes c
  rw [differentialPolynomialTwoBlockEquiv_crossDifference]
  simp only [map_sub, map_mul, MvPolynomial.map_C, MvPolynomial.map_map]
  rw [hbaseR]
  change MvPolynomial.C (algebraMap R K Q₀) * MvPolynomial.map (algebraMap F K) P₀ -
      MvPolynomial.C (algebraMap R K P₀) * MvPolynomial.map (algebraMap F K) Q₀ = _
  rw [hm, hn]
  simp only [differentialCharacteristicCoefficientCrossRelation, map_sub, map_mul,
    MvPolynomial.map_C, MvPolynomial.map_map]
  rw [hbaseG]
  ring

/-- The characteristic saturation transports to the formal free-jet fraction field.  The
coefficient map here carries the restricted differential structure, so this is a map of total
differential ideals rather than only of their underlying ordinary ideals. -/
theorem PrimitiveTwoBlockDifferentialCharacteristic.exists_mappedCrossRelation_saturation
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
    let K := FractionRing (DifferentialPolynomial Unit F)
    let φ : G →ₐ[F] K := differentialIntermediateToJetFraction G hG hy
    letI : Differential G := derivationClosedDifferential G hGclosed
    letI : Differential K := differentialIndependentJetFractionDifferential y hy
    ∃ a b : ℕ,
      MvPolynomial.map φ.toRingHom (scalarDifferentialPolynomialInitial P) ^ a *
          MvPolynomial.map φ.toRingHom (scalarDifferentialPolynomialSeparant P) ^ b *
          MvPolynomial.map φ.toRingHom
            (differentialCharacteristicCoefficientCrossRelation G
              (P.coeff m) (P.coeff n)
              (differentialPolynomialTwoBlockCoefficient m C.polynomial)
              (differentialPolynomialTwoBlockCoefficient n C.polynomial)) ∈
        differentialPolynomialIterateIdeal (MvPolynomial.map φ.toRingHom P) := by
  let K := FractionRing (DifferentialPolynomial Unit F)
  let φ : G →ₐ[F] K := differentialIntermediateToJetFraction G hG hy
  letI : Differential G := derivationClosedDifferential G hGclosed
  letI : Differential K := differentialIndependentJetFractionDifferential y hy
  let Q := differentialCharacteristicCoefficientCrossRelation G
    (P.coeff m) (P.coeff n)
    (differentialPolynomialTwoBlockCoefficient m C.polynomial)
    (differentialPolynomialTwoBlockCoefficient n C.polynomial)
  have hQ : Q ∈ differentialIntermediateRelationIdeal G y :=
    C.coefficientCrossRelation_mem G hG hy P m n
  obtain ⟨a, b, hab⟩ :=
    exists_initial_separant_powers_mem_differentialIntermediatePolynomialIterateIdeal
      G hGclosed y hP hQ
  refine ⟨a, b, ?_⟩
  have hφ : ∀ g : G, φ g′ = (φ g)′ := by
    intro g
    exact (differentialIntermediateToJetFraction_deriv G hGclosed hG hy g).symm
  have hmapped :=
    map_mem_differentialPolynomialIterateIdeal_of_commutes φ.toRingHom hφ hab
  simpa [Q] using hmapped

/-! ## Equation (78), squarefree recombination, and the cleared characteristic -/

/-- A squarefree element of a unique-factorization monoid divides any element divisible by each
of its irreducible factors.  This is the recombination step used after componentwise contraction. -/
theorem Squarefree.dvd_of_forall_irreducible_factor_dvd
    {R : Type*} [CommMonoidWithZero R] [UniqueFactorizationMonoid R]
    {P Q : R} (hP : Squarefree P)
    (hfactor : ∀ A : R, Irreducible A → A ∣ P → A ∣ Q) :
    P ∣ Q := by
  induction P using WfDvdMonoid.induction_on_irreducible with
  | zero => exact (not_squarefree_zero hP).elim
  | unit u hu => exact hu.dvd
  | mul A p hA0 hp ih =>
      have hsplit := squarefree_mul_iff.mp hP
      have hAQ : A ∣ Q := by
        apply ih hsplit.2.2
        intro q hq hqA
        apply hfactor q hq
        simpa [mul_comm] using dvd_mul_of_dvd_right hqA p
      have hpQ : p ∣ Q := hfactor p hp (dvd_mul_right p A)
      exact hsplit.1.mul_dvd hpQ hAQ

/-- The cleared two-block characteristic is squarefree over the formal left-jet fraction field.
This is the direct downstream use of equation (78): scalar extension may split the irreducible
characteristic polynomial, but the support theorem prevents any factor from repeating. -/
theorem PrimitiveTwoBlockDifferentialCharacteristic.mappedPolynomial_squarefree
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E] [CharZero E]
    (G : IntermediateField F E) {y : E}
    (hG : G ≤ differentialAdjoin F ({y} : Set E))
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    (P : DifferentialPolynomial Unit G) (hPirreducible : Irreducible P)
    (C : PrimitiveTwoBlockDifferentialCharacteristic G hG hy P) :
    let R := DifferentialPolynomial Unit F
    let K := FractionRing R
    Squarefree
      (MvPolynomial.map (algebraMap R K)
        (differentialPolynomialTwoBlockEquiv F C.polynomial)) := by
  let R := DifferentialPolynomial Unit F
  let K := FractionRing R
  let φ : G →ₐ[F] K := differentialIntermediateToJetFraction G hG hy
  letI : Algebra G K := φ.toRingHom.toAlgebra
  have hmap : Squarefree (MvPolynomial.map φ.toRingHom P) := by
    simpa [φ] using
      (irreducible_map_squarefree_of_charZero (K := K) hPirreducible)
  rw [C.clearing]
  have hunit : IsUnit
      (MvPolynomial.C (C.scalar : K) : MvPolynomial (Unit × ℕ) K) :=
    IsUnit.map MvPolynomial.C C.scalar.isUnit
  exact (associated_unit_mul_left _ _ hunit).squarefree_iff.mpr hmap

/-! ## Primitive products needed by the terminal reciprocity step -/

/-- Extending a nonzero polynomial over a field as coefficient constants gives a primitive
multivariable polynomial over the new polynomial coefficient ring. -/
theorem MvPolynomialPrimitive.map_C_of_ne_zero
    {F σ τ : Type*} [Field F]
    {P : MvPolynomial σ F} (hP0 : P ≠ 0) :
    MvPolynomialPrimitive
      (MvPolynomial.map
        (MvPolynomial.C : F →+* MvPolynomial τ F) P) := by
  intro r hr
  rw [MvPolynomial.C_dvd_iff_dvd_coeff] at hr
  obtain ⟨m, hm⟩ := Finsupp.ne_iff.mp hP0
  have hrd : r ∣ MvPolynomial.C (P.coeff m) := by
    simpa using hr m
  exact isUnit_of_dvd_unit hrd
    (IsUnit.map (MvPolynomial.C : F →+* MvPolynomial τ F) hm.isUnit)

/-- The product of two nonzero primitive multivariable polynomials over a UFD is primitive. -/
theorem MvPolynomialPrimitive.mul
    {R σ : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R]
    {P Q : MvPolynomial σ R}
    (hP : MvPolynomialPrimitive P)
    (hQ : MvPolynomialPrimitive Q)
    (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) :
    MvPolynomialPrimitive (P * Q) := by
  intro r hr
  by_contra hru
  have hr0 : r ≠ 0 := by
    intro hr0
    subst r
    rcases hr with ⟨T, hT⟩
    exact (mul_ne_zero hP0 hQ0) (by simpa using hT)
  obtain ⟨p, hp, hpr⟩ :=
    WfDvdMonoid.exists_irreducible_factor hru hr0
  have hpCprime : Prime (MvPolynomial.C p : MvPolynomial σ R) :=
    (MvPolynomial.prime_C_iff σ).2 hp.prime
  have hpdiv : MvPolynomial.C p ∣ P * Q :=
    (map_dvd (MvPolynomial.C : R →+* MvPolynomial σ R) hpr).trans hr
  rcases hpCprime.dvd_mul.mp hpdiv with hpP | hpQ
  · exact hp.not_isUnit (hP p hpP)
  · exact hp.not_isUnit (hQ p hpQ)

/-- A two-copy cross-difference vanishes exactly when its two entries are proportional over the
base field. -/
theorem differentialPolynomialCrossDifference_eq_zero_iff
    {F : Type*} [Field F]
    {P Q : DifferentialPolynomial Unit F} (hQ0 : Q ≠ 0) :
    differentialPolynomialCrossDifference P Q = 0 ↔
      ∃ c : F, P = MvPolynomial.C c * Q := by
  constructor
  · intro hzero
    obtain ⟨m, hm⟩ := Finsupp.ne_iff.mp hQ0
    have hcoeff := congrArg
      (differentialPolynomialTwoBlockCoefficient m) hzero
    rw [differentialPolynomialTwoBlockCoefficient_crossDifference] at hcoeff
    simp only [map_zero, differentialPolynomialTwoBlockCoefficient] at hcoeff
    have heq : MvPolynomial.C (Q.coeff m) * P =
        MvPolynomial.C (P.coeff m) * Q := by
      calc
        MvPolynomial.C (Q.coeff m) * P = P * MvPolynomial.C (Q.coeff m) :=
          mul_comm _ _
        _ = Q * MvPolynomial.C (P.coeff m) := (sub_eq_zero.mp hcoeff).symm
        _ = MvPolynomial.C (P.coeff m) * Q := mul_comm _ _
    refine ⟨P.coeff m / Q.coeff m, ?_⟩
    apply mul_left_cancel₀ (MvPolynomial.C_ne_zero.mpr hm)
    calc
      MvPolynomial.C (Q.coeff m) * P =
          MvPolynomial.C (P.coeff m) * Q := heq
      _ = MvPolynomial.C (Q.coeff m) *
          (MvPolynomial.C (P.coeff m / Q.coeff m) * Q) := by
        rw [← mul_assoc, ← MvPolynomial.C_mul,
          mul_div_cancel₀ (P.coeff m) hm]
  · rintro ⟨c, rfl⟩
    simp [differentialPolynomialCrossDifference]
    ring

end

end GaloisForLFunctions
