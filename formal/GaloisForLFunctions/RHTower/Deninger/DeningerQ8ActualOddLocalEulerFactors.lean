import GaloisForLFunctions.RHTower.Deninger.DeningerQ8ActualFiveInertiaCarrier
import GaloisForLFunctions.RHTower.Deninger.DeningerQ8ActualFortyOneInertiaCarrier
import GaloisForLFunctions.RHTower.Artin.ArtinRationalPrimeLocalEulerFactor

/-!
# Actual odd ramified Euler factors of the SST quaternion representation

The source-selected inertia carriers at `5` and `41` both contain the central
quaternion involution. Its literal action on the faithful two-dimensional
Artin carrier is `-1`, so the full and decomposition-local inertia invariant
spaces vanish. Consequently every Frobenius lift, and hence each canonical
rational-prime Euler polynomial, is exactly `1` at both odd ramified primes.
-/

namespace RHTower

open scoped NumberField Pointwise
noncomputable section

local notation "K1" => deningerQ8RootNumberNegOneFirstQuadraticField
local notation "K2" => deningerQ8RootNumberNegOneSecondQuadraticField
local notation "K3" => deningerQ8RootNumberNegOneTopField

local instance deningerQ8ActualOddLocalEulerFactorsLocalInst1 : CharZero K3 :=
  charZero_of_injective_algebraMap (algebraMap ℚ K3).injective
noncomputable local instance deningerQ8ActualOddLocalEulerFactorsLocalInst2 : FiniteDimensional ℚ K1 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadUBasis
noncomputable local instance deningerQ8ActualOddLocalEulerFactorsLocalInst3 : FiniteDimensional K1 K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadVBasis
noncomputable local instance deningerQ8ActualOddLocalEulerFactorsLocalInst4 : FiniteDimensional ℚ K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadIntegralBasis
noncomputable local instance deningerQ8ActualOddLocalEulerFactorsLocalInst5 : FiniteDimensional K2 K3 :=
  Module.Basis.finiteDimensional_of_finite
    (AdjoinRoot.powerBasis
      deningerQ8RootNumberNegOne_thirdQuadratic_irreducible.ne_zero).basis
noncomputable local instance deningerQ8ActualOddLocalEulerFactorsLocalInst6 : FiniteDimensional ℚ K3 :=
  FiniteDimensional.trans ℚ K2 K3
noncomputable local instance q8OddLocalEulerNumberField : NumberField K3 := NumberField.mk
noncomputable local instance deningerQ8ActualOddLocalEulerFactorsLocalInst7 : IsGalois ℚ K3 :=
  deningerQ8RootNumberNegOne_isGalois
noncomputable local instance q8OddLocalEulerFieldAction :
    MulSemiringAction Gal(K3/ℚ) K3 := inferInstance
noncomputable local instance q8OddLocalEulerIsGaloisGroup :
    IsGaloisGroup Gal(K3/ℚ) ℚ K3 := IsGaloisGroup.of_isGalois ℚ K3
noncomputable local instance q8OddLocalEulerAlgebra :
    Algebra (𝓞 ℚ) (𝓞 K3) := inferInstance
noncomputable local instance q8OddLocalEulerMulSemiringAction :
    MulSemiringAction Gal(K3/ℚ) (𝓞 K3) := inferInstance
local instance q8OddLocalEulerSmulCommClass :
    SMulCommClass Gal(K3/ℚ) (𝓞 ℚ) (𝓞 K3) := by
  constructor
  intro g r s
  apply Subtype.ext
  change g ((algebraMap ℚ K3) (r : ℚ) * (s : K3)) =
    (algebraMap ℚ K3) (r : ℚ) * g (s : K3)
  rw [map_mul, g.commutes]



theorem q8Actual_five_centralInvolution_mem_inertia
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(5 : ℤ)})) :
    q8CAlgEquiv ∈ P.inertia Gal(K3/ℚ) := by
  rw [q8Actual_five_inertia_eq_cyclicSource P hPover,
    deningerQ8ActualCyclicSubgroup_eq_stabilizer_topY]
  change q8CAlgEquiv • deningerQ8RootNumberNegOneTopY =
    deningerQ8RootNumberNegOneTopY
  change q8CAlgEquiv deningerQ8RootNumberNegOneTopY =
    deningerQ8RootNumberNegOneTopY
  rw [q8CAlgEquiv_apply, q8C_topY]

theorem q8Actual_fortyOne_centralInvolution_mem_inertia
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(41 : ℤ)})) :
    q8CAlgEquiv ∈ P.inertia Gal(K3/ℚ) := by
  rw [q8Actual_fortyOne_inertia_eq_topXStabilizer P hPover,
    ]
  change q8CAlgEquiv • deningerQ8RootNumberNegOneTopX =
    deningerQ8RootNumberNegOneTopX
  change q8CAlgEquiv deningerQ8RootNumberNegOneTopX =
    deningerQ8RootNumberNegOneTopX
  rw [q8CAlgEquiv_apply, q8C_topX]

theorem q8Actual_artin_fullInertia_invariants_eq_bot_of_central_mem
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hc : q8CAlgEquiv ∈ P.inertia Gal(K3/ℚ)) :
    Representation.invariants
        ((deningerQ8ArtinRepresentation
          deningerQ8RootNumberNegOne_galoisEquivQ8).comp
            (P.inertia Gal(K3/ℚ)).subtype) = ⊥ := by
  apply le_bot_iff.mp
  intro v hv
  have hfix := (Representation.mem_invariants _ v).mp hv ⟨q8CAlgEquiv, hc⟩
  change deningerQ8ArtinRepresentation
      deningerQ8RootNumberNegOne_galoisEquivQ8 q8CAlgEquiv v = v at hfix
  rw [deningerQ8ArtinRepresentation_central_apply
    deningerQ8RootNumberNegOne_galoisEquivQ8 q8CAlgEquiv
    deningerQ8_galoisEquiv_q8C] at hfix
  have hvzero : v = 0 := by
    apply Prod.ext
    · exact CharZero.neg_eq_self_iff.mp (by
        simpa using congrArg Prod.fst hfix)
    · exact CharZero.neg_eq_self_iff.mp (by
        simpa using congrArg Prod.snd hfix)
  simpa using hvzero

theorem q8Actual_artin_localInertia_invariants_eq_bot_of_central_mem
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hc : q8CAlgEquiv ∈ P.inertia Gal(K3/ℚ)) :
    Representation.invariants
        (((deningerQ8ArtinRepresentation
          deningerQ8RootNumberNegOne_galoisEquivQ8).comp
            (MulAction.stabilizer Gal(K3/ℚ) P).subtype).comp
              (P.inertia (MulAction.stabilizer Gal(K3/ℚ) P)).subtype) = ⊥ := by
  apply le_bot_iff.mp
  intro v hv
  let cD : MulAction.stabilizer Gal(K3/ℚ) P :=
    ⟨q8CAlgEquiv, Ideal.inertia_le_stabilizer P hc⟩
  have hcD : cD ∈ P.inertia (MulAction.stabilizer Gal(K3/ℚ) P) := by
    exact AddSubgroup.coe_mem_inertia.mp hc
  have hfix := (Representation.mem_invariants _ v).mp hv ⟨cD, hcD⟩
  change deningerQ8ArtinRepresentation
      deningerQ8RootNumberNegOne_galoisEquivQ8 q8CAlgEquiv v = v at hfix
  rw [deningerQ8ArtinRepresentation_central_apply
    deningerQ8RootNumberNegOne_galoisEquivQ8 q8CAlgEquiv
    deningerQ8_galoisEquiv_q8C] at hfix
  have hvzero : v = 0 := by
    apply Prod.ext
    · exact CharZero.neg_eq_self_iff.mp (by
        simpa using congrArg Prod.fst hfix)
    · exact CharZero.neg_eq_self_iff.mp (by
        simpa using congrArg Prod.snd hfix)
  simpa using hvzero

theorem q8Actual_localEulerPolynomial_eq_one_of_central_mem
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hc : q8CAlgEquiv ∈ P.inertia Gal(K3/ℚ))
    (φ : MulAction.stabilizer Gal(K3/ℚ) P) :
    GaloisForLFunctions.localEulerPolynomial
        ((deningerQ8ArtinRepresentation
          deningerQ8RootNumberNegOne_galoisEquivQ8).comp
            (MulAction.stabilizer Gal(K3/ℚ) P).subtype)
        (P.inertia (MulAction.stabilizer Gal(K3/ℚ) P)) φ = 1 := by
  let W := Representation.invariants
    (((deningerQ8ArtinRepresentation
      deningerQ8RootNumberNegOne_galoisEquivQ8).comp
        (MulAction.stabilizer Gal(K3/ℚ) P).subtype).comp
          (P.inertia (MulAction.stabilizer Gal(K3/ℚ) P)).subtype)
  let A : Module.End ℂ W := Representation.toInvariants
    ((deningerQ8ArtinRepresentation
      deningerQ8RootNumberNegOne_galoisEquivQ8).comp
        (MulAction.stabilizer Gal(K3/ℚ) P).subtype)
    (P.inertia (MulAction.stabilizer Gal(K3/ℚ) P)) φ
  have hW : W = ⊥ := by
    simpa [W] using q8Actual_artin_localInertia_invariants_eq_bot_of_central_mem P hc
  have hfinrank : Module.finrank ℂ W = 0 := by rw [hW]; simp
  have hchar : A.charpoly = 1 := by
    apply A.charpoly_monic.natDegree_eq_zero.mp
    rw [A.charpoly_natDegree, hfinrank]
  change A.charpoly.reverse = 1
  rw [hchar]
  change Polynomial.reverse (Polynomial.C (1 : ℂ)) = Polynomial.C 1
  rw [Polynomial.reverse_C]

theorem q8Actual_five_frobeniusInertiaEulerPolynomial_eq_one
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(5 : ℤ)})) :
    @GaloisForLFunctions.frobeniusInertiaEulerPolynomial
      (ℂ × ℂ) inferInstance (𝓞 ℚ) (𝓞 K3) Gal(K3/ℚ)
      inferInstance inferInstance q8OddLocalEulerAlgebra inferInstance inferInstance
      q8OddLocalEulerMulSemiringAction q8OddLocalEulerSmulCommClass inferInstance
      inferInstance inferInstance P inferInstance inferInstance
      (deningerQ8ArtinRepresentation
        deningerQ8RootNumberNegOne_galoisEquivQ8) = 1 := by
  exact q8Actual_localEulerPolynomial_eq_one_of_central_mem P
    (q8Actual_five_centralInvolution_mem_inertia P hPover)
    (GaloisForLFunctions.arithmeticFrobeniusInStabilizer (R := 𝓞 ℚ) P)

theorem q8Actual_fortyOne_frobeniusInertiaEulerPolynomial_eq_one
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(41 : ℤ)})) :
    @GaloisForLFunctions.frobeniusInertiaEulerPolynomial
      (ℂ × ℂ) inferInstance (𝓞 ℚ) (𝓞 K3) Gal(K3/ℚ)
      inferInstance inferInstance q8OddLocalEulerAlgebra inferInstance inferInstance
      q8OddLocalEulerMulSemiringAction q8OddLocalEulerSmulCommClass inferInstance
      inferInstance inferInstance P inferInstance inferInstance
      (deningerQ8ArtinRepresentation
        deningerQ8RootNumberNegOne_galoisEquivQ8) = 1 := by
  exact q8Actual_localEulerPolynomial_eq_one_of_central_mem P
    (q8Actual_fortyOne_centralInvolution_mem_inertia P hPover)
    (GaloisForLFunctions.arithmeticFrobeniusInStabilizer (R := 𝓞 ℚ) P)

theorem five_mem_rationalPrimeFinitePlace : (5 : 𝓞 ℚ) ∈
    (GaloisForLFunctions.rationalPrimeFinitePlace 5 (by norm_num)).asIdeal := by
  simp [GaloisForLFunctions.rationalPrimeFinitePlace,
    GaloisForLFunctions.heightOneSpectrumRatOfNatPrime,
    GaloisForLFunctions.heightOneSpectrumEquiv,
    GaloisForLFunctions.heightOneSpectrumComap,
    GaloisForLFunctions.heightOneSpectrumIntOfNatPrime,
    Ideal.mem_span_singleton]
  rw [map_ofNat]

theorem fortyOne_mem_rationalPrimeFinitePlace : (41 : 𝓞 ℚ) ∈
    (GaloisForLFunctions.rationalPrimeFinitePlace 41 (by norm_num)).asIdeal := by
  simp [GaloisForLFunctions.rationalPrimeFinitePlace,
    GaloisForLFunctions.heightOneSpectrumRatOfNatPrime,
    GaloisForLFunctions.heightOneSpectrumEquiv,
    GaloisForLFunctions.heightOneSpectrumComap,
    GaloisForLFunctions.heightOneSpectrumIntOfNatPrime,
    Ideal.mem_span_singleton]
  rw [map_ofNat]

theorem q8Actual_five_rationalPrimeLocalEulerPolynomial_eq_one :
    @GaloisForLFunctions.rationalPrimeLocalEulerPolynomial
      K3 Gal(K3/ℚ) (ℂ × ℂ) inferInstance q8OddLocalEulerNumberField inferInstance
      inferInstance inferInstance q8OddLocalEulerFieldAction
      q8OddLocalEulerIsGaloisGroup inferInstance inferInstance inferInstance 5 (by norm_num)
      (deningerQ8ArtinRepresentation
        deningerQ8RootNumberNegOne_galoisEquivQ8) = 1 := by
  have hp5 : Nat.Prime 5 := by norm_num
  let v := GaloisForLFunctions.rationalPrimeFinitePlace 5 (by norm_num)
  let p : MaximalSpectrum (𝓞 ℚ) :=
    { asIdeal := v.asIdeal, isMaximal := v.isMaximal }
  let P : Ideal (𝓞 K3) :=
    GaloisForLFunctions.chosenMaximalPrimeAbove
      (A := 𝓞 ℚ) (B := 𝓞 K3) p
  letI : P.IsMaximal :=
    GaloisForLFunctions.chosenMaximalPrimeAbove_isMaximal
      (A := 𝓞 ℚ) (B := 𝓞 K3) p
  letI : P.LiesOver v.asIdeal := by
    simpa [p] using
      (GaloisForLFunctions.chosenMaximalPrimeAbove_liesOver
        (A := 𝓞 ℚ) (B := 𝓞 K3) p)
  have h5top : (5 : 𝓞 K3) ∈ P := by
    have hbase : (5 : 𝓞 ℚ) ∈ p.asIdeal := by
      simpa [p, v] using five_mem_rationalPrimeFinitePlace
    have hmap : algebraMap (𝓞 ℚ) (𝓞 K3) (5 : 𝓞 ℚ) ∈ P := by
      exact (Ideal.mem_of_liesOver P v.asIdeal (5 : 𝓞 ℚ)).mp
        (by simpa [p] using hbase)
    simpa only [map_ofNat] using hmap
  have hPoverZ : P.LiesOver (Ideal.span {(5 : ℤ)}) := by
    rw [Ideal.liesOver_span_iff (Ideal.IsMaximal.ne_top inferInstance)
      (by norm_num : Prime (5 : ℤ))]
    exact h5top
  have hlocal := q8Actual_five_frobeniusInertiaEulerPolynomial_eq_one P hPoverZ
  rw [@GaloisForLFunctions.frobeniusInertiaEulerPolynomial_eq_rationalPrimeLocalEulerPolynomial
    K3 Gal(K3/ℚ) (ℂ × ℂ) inferInstance q8OddLocalEulerNumberField inferInstance
    inferInstance inferInstance q8OddLocalEulerFieldAction q8OddLocalEulerIsGaloisGroup
    inferInstance inferInstance inferInstance 5 hp5 P inferInstance inferInstance
    (deningerQ8ArtinRepresentation
      deningerQ8RootNumberNegOne_galoisEquivQ8)] at hlocal
  exact hlocal

theorem q8Actual_fortyOne_rationalPrimeLocalEulerPolynomial_eq_one :
    @GaloisForLFunctions.rationalPrimeLocalEulerPolynomial
      K3 Gal(K3/ℚ) (ℂ × ℂ) inferInstance q8OddLocalEulerNumberField inferInstance
      inferInstance inferInstance q8OddLocalEulerFieldAction
      q8OddLocalEulerIsGaloisGroup inferInstance inferInstance inferInstance 41 (by norm_num)
      (deningerQ8ArtinRepresentation
        deningerQ8RootNumberNegOne_galoisEquivQ8) = 1 := by
  have hp41 : Nat.Prime 41 := by norm_num
  let v := GaloisForLFunctions.rationalPrimeFinitePlace 41 (by norm_num)
  let p : MaximalSpectrum (𝓞 ℚ) :=
    { asIdeal := v.asIdeal, isMaximal := v.isMaximal }
  let P : Ideal (𝓞 K3) :=
    GaloisForLFunctions.chosenMaximalPrimeAbove
      (A := 𝓞 ℚ) (B := 𝓞 K3) p
  letI : P.IsMaximal :=
    GaloisForLFunctions.chosenMaximalPrimeAbove_isMaximal
      (A := 𝓞 ℚ) (B := 𝓞 K3) p
  letI : P.LiesOver v.asIdeal := by
    simpa [p] using
      (GaloisForLFunctions.chosenMaximalPrimeAbove_liesOver
        (A := 𝓞 ℚ) (B := 𝓞 K3) p)
  have h41top : (41 : 𝓞 K3) ∈ P := by
    have hbase : (41 : 𝓞 ℚ) ∈ p.asIdeal := by
      simpa [p, v] using fortyOne_mem_rationalPrimeFinitePlace
    have hmap : algebraMap (𝓞 ℚ) (𝓞 K3) (41 : 𝓞 ℚ) ∈ P := by
      exact (Ideal.mem_of_liesOver P v.asIdeal (41 : 𝓞 ℚ)).mp
        (by simpa [p] using hbase)
    simpa only [map_ofNat] using hmap
  have hPoverZ : P.LiesOver (Ideal.span {(41 : ℤ)}) := by
    rw [Ideal.liesOver_span_iff (Ideal.IsMaximal.ne_top inferInstance)
      (by norm_num : Prime (41 : ℤ))]
    exact h41top
  have hlocal := q8Actual_fortyOne_frobeniusInertiaEulerPolynomial_eq_one P hPoverZ
  rw [@GaloisForLFunctions.frobeniusInertiaEulerPolynomial_eq_rationalPrimeLocalEulerPolynomial
    K3 Gal(K3/ℚ) (ℂ × ℂ) inferInstance q8OddLocalEulerNumberField inferInstance
    inferInstance inferInstance q8OddLocalEulerFieldAction q8OddLocalEulerIsGaloisGroup
    inferInstance inferInstance inferInstance 41 hp41 P inferInstance inferInstance
    (deningerQ8ArtinRepresentation
      deningerQ8RootNumberNegOne_galoisEquivQ8)] at hlocal
  exact hlocal

end
end RHTower
