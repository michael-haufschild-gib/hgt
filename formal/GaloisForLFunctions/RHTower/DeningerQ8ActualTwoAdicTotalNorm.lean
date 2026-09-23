import GaloisForLFunctions.RHTower.DeningerQ8ActualTwoAdicNormSelector
import GaloisForLFunctions.HTGeometry.ABHN.ValuationCoordinateTransport

/-!
# Actual dyadic total norm for the SST quaternion field

The decomposition generator on the biquadratic field preserves every contracted
prime above two, hence extends continuously to its completion.  Combining this
completed involution with the coefficient-faithful top-field norm witness proves
that the literal selected dyadic total norm is `-1`.
-/

namespace RHTower

noncomputable section

open scoped NumberField Pointwise ValuativeRel Polynomial WithZero WithZeroMulInt

local notation "K1" => deningerQ8RootNumberNegOneFirstQuadraticField
local notation "K2" => deningerQ8RootNumberNegOneSecondQuadraticField

local instance deningerQ8ActualTwoAdicTotalNormLocalInst1 : CharZero K2 :=
  charZero_of_injective_algebraMap (algebraMap ℚ K2).injective

noncomputable def q8FirstConjugationSecondRingEquiv : K2 ≃+* K2 :=
  { q8FirstConjugationSecond with
    invFun := q8FirstConjugationSecond
    left_inv := q8FirstConjugationSecond_involutive
    right_inv := q8FirstConjugationSecond_involutive }

@[simp] theorem q8FirstConjugationSecondRingEquiv_apply (x : K2) :
    q8FirstConjugationSecondRingEquiv x = q8FirstConjugationSecond x := rfl

@[simp] theorem q8FirstConjugationSecondRingEquiv_symm_apply (x : K2) :
    q8FirstConjugationSecondRingEquiv.symm x = q8FirstConjugationSecond x := rfl

theorem q8FirstConjugationSecond_q8BiquadTwoAdicU :
    q8FirstConjugationSecond (q8BiquadTwoAdicU : K2) =
      1 - (q8BiquadTwoAdicU : K2) := by
  change q8FirstConjugationSecond (algebraMap K1 K2 q8BiquadU) =
    1 - algebraMap K1 K2 q8BiquadU
  change q8FirstConjugationSecond
      (AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial q8BiquadU) = _
  rw [q8FirstConjugationSecond_of]
  change AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial
      (q8FirstConjugation q8BiquadU) = _
  unfold q8BiquadU
  rw [map_div₀, map_add, map_one, q8FirstConjugation_root]
  have htwo : q8FirstConjugation (2 : K1) = 2 := q8FirstConjugation_rat 2
  rw [htwo]
  change AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial
      ((1 - deningerQ8RootNumberNegOneFirstQuadraticRoot) / 2) =
    1 - AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial
      ((1 + deningerQ8RootNumberNegOneFirstQuadraticRoot) / 2)
  simp only [map_div₀, map_sub, map_add, map_one, map_ofNat]
  have hinv : (2 : K2)⁻¹ + 2⁻¹ = 1 := by norm_num
  linear_combination hinv

theorem q8BiquadTwoAdicU_mul_conjugate :
    (q8BiquadTwoAdicU : K2) *
      q8FirstConjugationSecond (q8BiquadTwoAdicU : K2) = -1 := by
  rw [q8FirstConjugationSecond_q8BiquadTwoAdicU]
  have hu := congrArg (fun x : 𝓞 K2 => (x : K2)) q8BiquadTwoAdicU_sq
  change (q8BiquadTwoAdicU : K2) ^ (2 : ℕ) = (q8BiquadTwoAdicU : K2) + 1 at hu
  rw [mul_sub, mul_one, ← pow_two, hu]
  ring

local notation "K3" => deningerQ8RootNumberNegOneTopField

local instance deningerQ8ActualTwoAdicTotalNormLocalInst2 : CharZero K3 :=
  charZero_of_injective_algebraMap (algebraMap ℚ K3).injective

noncomputable local instance deningerQ8ActualTwoAdicTotalNormLocalInst3 : FiniteDimensional ℚ K1 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadUBasis
noncomputable local instance deningerQ8ActualTwoAdicTotalNormLocalInst4 : FiniteDimensional K1 K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadVBasis
noncomputable local instance deningerQ8ActualTwoAdicTotalNormLocalInst5 : FiniteDimensional ℚ K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadIntegralBasis
noncomputable local instance deningerQ8ActualTwoAdicTotalNormLocalInst6 : FiniteDimensional K2 K3 :=
  Module.Basis.finiteDimensional_of_finite
    (AdjoinRoot.powerBasis
      deningerQ8RootNumberNegOne_thirdQuadratic_irreducible.ne_zero).basis
noncomputable local instance deningerQ8ActualTwoAdicTotalNormLocalInst7 : FiniteDimensional ℚ K3 :=
  FiniteDimensional.trans ℚ K2 K3
noncomputable local instance deningerQ8ActualTwoAdicTotalNormLocalInst8 : NumberField K2 := NumberField.mk
noncomputable local instance deningerQ8ActualTwoAdicTotalNormLocalInst9 : NumberField K3 := NumberField.mk
noncomputable local instance deningerQ8ActualTwoAdicTotalNormLocalInst10 : IsGalois ℚ K3 :=
  deningerQ8RootNumberNegOne_isGalois

noncomputable def q8BiquadContractedTwoPrime
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P) :
    IsDedekindDomain.HeightOneSpectrum (𝓞 K2) := by
  let Q0 := P.comap (algebraMap (𝓞 K2) (𝓞 K3))
  have hQmax : Q0.IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
      (R := 𝓞 K2) (S := 𝓞 K3) P
  have hQtwo : (2 : 𝓞 K2) ∈ Q0 := by
    change algebraMap (𝓞 K2) (𝓞 K3) 2 ∈ P
    simpa only [map_ofNat] using hPtwo
  have hQne : Q0 ≠ ⊥ := by
    intro hQ
    rw [hQ, Ideal.mem_bot] at hQtwo
    norm_num at hQtwo
  exact ⟨Q0, hQmax.isPrime, hQne⟩

theorem q8BiquadContractedTwoPrime_two_mem
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P) :
    (2 : 𝓞 K2) ∈ (q8BiquadContractedTwoPrime P hPtwo).asIdeal := by
  change algebraMap (𝓞 K2) (𝓞 K3) 2 ∈ P
  simpa only [map_ofNat] using hPtwo

theorem q8FirstConjugationSecond_preserves_contracted_two_prime
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P) :
    let Q : Ideal (𝓞 K2) :=
      P.comap (algebraMap (𝓞 K2) (𝓞 K3))
    ∀ x : 𝓞 K2,
      NumberField.RingOfIntegers.mapRingEquiv
          q8FirstConjugationSecondRingEquiv x ∈ Q ↔ x ∈ Q := by
  let Q : Ideal (𝓞 K2) :=
    P.comap (algebraMap (𝓞 K2) (𝓞 K3))
  have hI : q8IAlgEquiv ∈ MulAction.stabilizer Gal(K3/ℚ) P := by
    rw [q8Literal_two_decomposition_eq_cyclicSource P hPtwo,
      deningerQ8ActualCyclicSubgroup_eq_stabilizer_topY]
    exact q8IAlgEquiv_topY
  change q8IAlgEquiv • P = P at hI
  have hmove {y : 𝓞 K3} (hy : y ∈ P) : q8IAlgEquiv • y ∈ P := by
    have hy' := Ideal.smul_mem_pointwise_smul q8IAlgEquiv y P hy
    rwa [hI] at hy'
  let eO : 𝓞 K2 ≃+* 𝓞 K2 :=
    NumberField.RingOfIntegers.mapRingEquiv
      q8FirstConjugationSecondRingEquiv
  have hforward (x : 𝓞 K2) (hx : x ∈ Q) : eO x ∈ Q := by
    change algebraMap (𝓞 K2) (𝓞 K3) (eO x) ∈ P
    have hx3 : algebraMap (𝓞 K2) (𝓞 K3) x ∈ P := hx
    have hm := hmove hx3
    convert hm using 1
    apply NumberField.RingOfIntegers.ext
    change algebraMap K2 K3
        (q8FirstConjugationSecond (x : K2)) =
      q8IAlgEquiv (algebraMap K2 K3 (x : K2))
    change AdjoinRoot.of deningerQ8RootNumberNegOneThirdQuadraticPolynomial
        (q8FirstConjugationSecond (x : K2)) =
      q8I (AdjoinRoot.of deningerQ8RootNumberNegOneThirdQuadraticPolynomial (x : K2))
    rw [q8I_of]
    rfl
  change ∀ x : 𝓞 K2, eO x ∈ Q ↔ x ∈ Q
  intro x
  constructor
  · intro hx
    have hxx := hforward (eO x) hx
    have he2 : eO (eO x) = x := by
      apply NumberField.RingOfIntegers.ext
      exact q8FirstConjugationSecond_involutive (x : K2)
    rwa [he2] at hxx
  · exact hforward x

theorem q8FirstConjugationSecond_valuation_le_one_iff
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P)
    (x : K2) :
    let Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K2) :=
      q8BiquadContractedTwoPrime P hPtwo
    Q.valuation K2 (q8FirstConjugationSecondRingEquiv x) ≤ 1 ↔
      Q.valuation K2 x ≤ 1 := by
  let Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K2) :=
    q8BiquadContractedTwoPrime P hPtwo
  let e := q8FirstConjugationSecondRingEquiv
  let eO : 𝓞 K2 ≃+* 𝓞 K2 :=
    NumberField.RingOfIntegers.mapRingEquiv e
  have hQ (a : 𝓞 K2) : eO a ∈ Q.asIdeal ↔ a ∈ Q.asIdeal := by
    exact q8FirstConjugationSecond_preserves_contracted_two_prime P hPtwo a
  have hforward (y : K2) (hy : Q.valuation K2 y ≤ 1) :
      Q.valuation K2 (e y) ≤ 1 := by
    obtain ⟨n, d, hnd⟩ := Q.exists_primeCompl_mul_eq_of_integer y hy
    have hdnot : eO d ∉ Q.asIdeal := by
      intro hed
      exact (Ideal.mem_primeCompl_iff.mp d.property) ((hQ d).mp hed)
    have hdval : Q.valuation K2 (algebraMap (𝓞 K2) K2 (eO d)) = 1 :=
      Q.valuation_eq_one_iff_notMem.mpr hdnot
    have hnval : Q.valuation K2 (algebraMap (𝓞 K2) K2 (eO n)) ≤ 1 :=
      Q.valuation_le_one (K := K2) (eO n)
    have hnd' := congrArg e hnd
    have hprod : e y * algebraMap (𝓞 K2) K2 (eO d) =
        algebraMap (𝓞 K2) K2 (eO n) := by
      simpa [e, eO] using hnd'
    have hv := congrArg (Q.valuation K2) hprod
    rw [map_mul, hdval, mul_one] at hv
    rw [hv]
    exact hnval
  change Q.valuation K2 (e x) ≤ 1 ↔ Q.valuation K2 x ≤ 1
  constructor
  · intro hx
    have hxx := hforward (e x) hx
    have he2 : e (e x) = x := q8FirstConjugationSecond_involutive x
    rwa [he2] at hxx
  · exact hforward x

noncomputable def q8FirstConjugationSecondWithValRingEquiv
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P) :
    let Q := q8BiquadContractedTwoPrime P hPtwo
    WithVal (Q.valuation K2) ≃+* WithVal (Q.valuation K2) := by
  let Q := q8BiquadContractedTwoPrime P hPtwo
  let v := Q.valuation K2
  let e := q8FirstConjugationSecondRingEquiv
  let w := v.comap e.symm.toRingHom
  exact (WithVal.congr v w e).trans (WithVal.congr w v (.refl K2))

theorem continuous_q8FirstConjugationSecondWithValRingEquiv
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P) :
    Continuous (q8FirstConjugationSecondWithValRingEquiv P hPtwo) := by
  let Q := q8BiquadContractedTwoPrime P hPtwo
  let v := Q.valuation K2
  let e := q8FirstConjugationSecondRingEquiv
  let w := v.comap e.symm.toRingHom
  have hwv : w.IsEquiv v := by
    rw [Valuation.isEquiv_iff_val_le_one]
    intro x
    change v (e.symm x) ≤ 1 ↔ v x ≤ 1
    simpa [e, v] using
      q8FirstConjugationSecond_valuation_le_one_iff P hPtwo x
  have hpoint : ∀ x, w (e x) = v x := by
    intro x
    simp [w]
  let u1 :=
    GaloisForLFunctions.HTGeometry.ABHN.uniformEquiv_congr_of_valuation_eq
      v w e hpoint
  let u2 := hwv.uniformEquiv
  exact (u1.trans u2).continuous

theorem continuous_q8FirstConjugationSecondWithValRingEquiv_symm
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P) :
    Continuous (q8FirstConjugationSecondWithValRingEquiv P hPtwo).symm := by
  let Q := q8BiquadContractedTwoPrime P hPtwo
  let v := Q.valuation K2
  let e := q8FirstConjugationSecondRingEquiv
  let w := v.comap e.symm.toRingHom
  have hwv : w.IsEquiv v := by
    rw [Valuation.isEquiv_iff_val_le_one]
    intro x
    change v (e.symm x) ≤ 1 ↔ v x ≤ 1
    simpa [e, v] using
      q8FirstConjugationSecond_valuation_le_one_iff P hPtwo x
  have hpoint : ∀ x, w (e x) = v x := by
    intro x
    simp [w]
  let u1 :=
    GaloisForLFunctions.HTGeometry.ABHN.uniformEquiv_congr_of_valuation_eq
      v w e hpoint
  let u2 := hwv.uniformEquiv
  exact (u1.trans u2).symm.continuous

noncomputable def q8FirstConjugationSecondCompletedRingEquiv
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P) :
    let Q := q8BiquadContractedTwoPrime P hPtwo
    Q.adicCompletion K2 ≃+* Q.adicCompletion K2 := by
  let Q := q8BiquadContractedTwoPrime P hPtwo
  let f := q8FirstConjugationSecondWithValRingEquiv P hPtwo
  let fc := UniformSpace.Completion.mapRingEquiv f
    (continuous_q8FirstConjugationSecondWithValRingEquiv P hPtwo)
    (continuous_q8FirstConjugationSecondWithValRingEquiv_symm P hPtwo)
  exact (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv K2 Q).trans
    (fc.trans
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv K2 Q).symm)

@[simp] theorem q8FirstConjugationSecondCompletedRingEquiv_algebraMap
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P)
    (x : K2) :
    let Q := q8BiquadContractedTwoPrime P hPtwo
    q8FirstConjugationSecondCompletedRingEquiv P hPtwo
        (algebraMap K2 (Q.adicCompletion K2) x) =
      algebraMap K2 (Q.adicCompletion K2)
        (q8FirstConjugationSecond x) := by
  let Q := q8BiquadContractedTwoPrime P hPtwo
  change q8FirstConjugationSecondCompletedRingEquiv P hPtwo
      (x : Q.adicCompletion K2) =
    ((q8FirstConjugationSecond x : K2) : Q.adicCompletion K2)
  unfold q8FirstConjugationSecondCompletedRingEquiv
  apply IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext
  change UniformSpace.Completion.map
      (q8FirstConjugationSecondWithValRingEquiv P hPtwo)
        (WithVal.toVal (Q.valuation K2) x) =
    (WithVal.toVal (Q.valuation K2) (q8FirstConjugationSecond x) :
      UniformSpace.Completion (WithVal (Q.valuation K2)))
  rw [UniformSpace.Completion.map_coe
    (uniformContinuous_addMonoidHom_of_continuous
      (continuous_q8FirstConjugationSecondWithValRingEquiv P hPtwo))]
  rfl

theorem q8FirstConjugationSecond_valuation_le_one_iff_of_asIdeal_eq
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P)
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K2))
    (hQ : Q.asIdeal = P.comap (algebraMap (𝓞 K2) (𝓞 K3)))
    (x : K2) :
    Q.valuation K2 (q8FirstConjugationSecondRingEquiv x) ≤ 1 ↔
      Q.valuation K2 x ≤ 1 := by
  let e := q8FirstConjugationSecondRingEquiv
  let eO : 𝓞 K2 ≃+* 𝓞 K2 :=
    NumberField.RingOfIntegers.mapRingEquiv e
  have hQpreserve (a : 𝓞 K2) : eO a ∈ Q.asIdeal ↔ a ∈ Q.asIdeal := by
    rw [hQ]
    exact q8FirstConjugationSecond_preserves_contracted_two_prime P hPtwo a
  have hforward (y : K2) (hy : Q.valuation K2 y ≤ 1) :
      Q.valuation K2 (e y) ≤ 1 := by
    obtain ⟨n, d, hnd⟩ := Q.exists_primeCompl_mul_eq_of_integer y hy
    have hdnot : eO d ∉ Q.asIdeal := by
      intro hed
      exact (Ideal.mem_primeCompl_iff.mp d.property) ((hQpreserve d).mp hed)
    have hdval : Q.valuation K2 (algebraMap (𝓞 K2) K2 (eO d)) = 1 :=
      Q.valuation_eq_one_iff_notMem.mpr hdnot
    have hnval : Q.valuation K2 (algebraMap (𝓞 K2) K2 (eO n)) ≤ 1 :=
      Q.valuation_le_one (K := K2) (eO n)
    have hnd' := congrArg e hnd
    have hprod : e y * algebraMap (𝓞 K2) K2 (eO d) =
        algebraMap (𝓞 K2) K2 (eO n) := by
      simpa [e, eO] using hnd'
    have hv := congrArg (Q.valuation K2) hprod
    rw [map_mul, hdval, mul_one] at hv
    rw [hv]
    exact hnval
  change Q.valuation K2 (e x) ≤ 1 ↔ Q.valuation K2 x ≤ 1
  constructor
  · intro hx
    have hxx := hforward (e x) hx
    have he2 : e (e x) = x := q8FirstConjugationSecond_involutive x
    rwa [he2] at hxx
  · exact hforward x

noncomputable def q8FirstConjugationSecondWithValRingEquivAtPrime
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (_hPtwo : (2 : 𝓞 K3) ∈ P)
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K2))
    (_hQ : Q.asIdeal = P.comap (algebraMap (𝓞 K2) (𝓞 K3))) :
    WithVal (Q.valuation K2) ≃+* WithVal (Q.valuation K2) := by
  let v := Q.valuation K2
  let e := q8FirstConjugationSecondRingEquiv
  let w := v.comap e.symm.toRingHom
  exact (WithVal.congr v w e).trans (WithVal.congr w v (.refl K2))

theorem continuous_q8FirstConjugationSecondWithValRingEquivAtPrime
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P)
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K2))
    (hQ : Q.asIdeal = P.comap (algebraMap (𝓞 K2) (𝓞 K3))) :
    Continuous (q8FirstConjugationSecondWithValRingEquivAtPrime P hPtwo Q hQ) := by
  let v := Q.valuation K2
  let e := q8FirstConjugationSecondRingEquiv
  let w := v.comap e.symm.toRingHom
  have hwv : w.IsEquiv v := by
    rw [Valuation.isEquiv_iff_val_le_one]
    intro x
    change v (e.symm x) ≤ 1 ↔ v x ≤ 1
    simpa [e, v] using
      q8FirstConjugationSecond_valuation_le_one_iff_of_asIdeal_eq
        P hPtwo Q hQ x
  have hpoint : ∀ x, w (e x) = v x := by
    intro x
    simp [w]
  let u1 :=
    GaloisForLFunctions.HTGeometry.ABHN.uniformEquiv_congr_of_valuation_eq
      v w e hpoint
  let u2 := hwv.uniformEquiv
  exact (u1.trans u2).continuous

theorem continuous_q8FirstConjugationSecondWithValRingEquivAtPrime_symm
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P)
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K2))
    (hQ : Q.asIdeal = P.comap (algebraMap (𝓞 K2) (𝓞 K3))) :
    Continuous
      (q8FirstConjugationSecondWithValRingEquivAtPrime P hPtwo Q hQ).symm := by
  let v := Q.valuation K2
  let e := q8FirstConjugationSecondRingEquiv
  let w := v.comap e.symm.toRingHom
  have hwv : w.IsEquiv v := by
    rw [Valuation.isEquiv_iff_val_le_one]
    intro x
    change v (e.symm x) ≤ 1 ↔ v x ≤ 1
    simpa [e, v] using
      q8FirstConjugationSecond_valuation_le_one_iff_of_asIdeal_eq
        P hPtwo Q hQ x
  have hpoint : ∀ x, w (e x) = v x := by
    intro x
    simp [w]
  let u1 :=
    GaloisForLFunctions.HTGeometry.ABHN.uniformEquiv_congr_of_valuation_eq
      v w e hpoint
  let u2 := hwv.uniformEquiv
  exact (u1.trans u2).symm.continuous

noncomputable def q8FirstConjugationSecondCompletedRingEquivAtPrime
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P)
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K2))
    (hQ : Q.asIdeal = P.comap (algebraMap (𝓞 K2) (𝓞 K3))) :
    Q.adicCompletion K2 ≃+* Q.adicCompletion K2 := by
  let f := q8FirstConjugationSecondWithValRingEquivAtPrime P hPtwo Q hQ
  let fc := UniformSpace.Completion.mapRingEquiv f
    (continuous_q8FirstConjugationSecondWithValRingEquivAtPrime P hPtwo Q hQ)
    (continuous_q8FirstConjugationSecondWithValRingEquivAtPrime_symm P hPtwo Q hQ)
  exact (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv K2 Q).trans
    (fc.trans
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv K2 Q).symm)

@[simp] theorem q8FirstConjugationSecondCompletedRingEquivAtPrime_algebraMap
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P)
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K2))
    (hQ : Q.asIdeal = P.comap (algebraMap (𝓞 K2) (𝓞 K3)))
    (x : K2) :
    q8FirstConjugationSecondCompletedRingEquivAtPrime P hPtwo Q hQ
        (algebraMap K2 (Q.adicCompletion K2) x) =
      algebraMap K2 (Q.adicCompletion K2)
        (q8FirstConjugationSecond x) := by
  change q8FirstConjugationSecondCompletedRingEquivAtPrime P hPtwo Q hQ
      (x : Q.adicCompletion K2) =
    ((q8FirstConjugationSecond x : K2) : Q.adicCompletion K2)
  unfold q8FirstConjugationSecondCompletedRingEquivAtPrime
  apply IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext
  change UniformSpace.Completion.map
      (q8FirstConjugationSecondWithValRingEquivAtPrime P hPtwo Q hQ)
        (WithVal.toVal (Q.valuation K2) x) =
    (WithVal.toVal (Q.valuation K2) (q8FirstConjugationSecond x) :
      UniformSpace.Completion (WithVal (Q.valuation K2)))
  rw [UniformSpace.Completion.map_coe
    (uniformContinuous_addMonoidHom_of_continuous
      (continuous_q8FirstConjugationSecondWithValRingEquivAtPrime
        P hPtwo Q hQ))]
  rfl

noncomputable def q8FirstConjugationSecondCompletedRingEquivAtFinitePlace
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P)
    (place : NumberField.FinitePlace K2)
    (hQ : place.maximalIdeal.asIdeal =
      P.comap (algebraMap (𝓞 K2) (𝓞 K3))) :
    let E := GaloisForLFunctions.HTGeometry.ABHN.completion K2 (.finite place)
    E ≃+* E := by
  change place.maximalIdeal.adicCompletion K2 ≃+*
    place.maximalIdeal.adicCompletion K2
  exact q8FirstConjugationSecondCompletedRingEquivAtPrime
    P hPtwo place.maximalIdeal hQ

@[simp] theorem
    q8FirstConjugationSecondCompletedRingEquivAtFinitePlace_algebraMap
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P)
    (place : NumberField.FinitePlace K2)
    (hQ : place.maximalIdeal.asIdeal =
      P.comap (algebraMap (𝓞 K2) (𝓞 K3)))
    (x : K2) :
    let E := GaloisForLFunctions.HTGeometry.ABHN.completion K2 (.finite place)
    q8FirstConjugationSecondCompletedRingEquivAtFinitePlace
        P hPtwo place hQ (algebraMap K2 E x) =
      algebraMap K2 E (q8FirstConjugationSecond x) := by
  change q8FirstConjugationSecondCompletedRingEquivAtPrime
        P hPtwo place.maximalIdeal hQ
        (algebraMap K2 (place.maximalIdeal.adicCompletion K2) x) =
      algebraMap K2 (place.maximalIdeal.adicCompletion K2)
        (q8FirstConjugationSecond x)
  exact q8FirstConjugationSecondCompletedRingEquivAtPrime_algebraMap
    P hPtwo place.maximalIdeal hQ x

/-- Total dyadic norm law at any packaged finite place whose maximal ideal is
the contraction of the selected top prime. -/
theorem exists_q8ActualTwoAdicTotalNorm_neg_one_of_place
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P)
    (place : NumberField.FinitePlace K2)
    (hplace : (2 : 𝓞 K2) ∈ place.maximalIdeal.asIdeal)
    (hQ : place.maximalIdeal.asIdeal =
      P.comap (algebraMap (𝓞 K2) (𝓞 K3))) :
    let E := GaloisForLFunctions.HTGeometry.ABHN.completion K2 (.finite place)
    ∃ x : TensorProduct K2 E K3,
      Algebra.norm E x *
          q8FirstConjugationSecondCompletedRingEquivAtFinitePlace
            P hPtwo place hQ
            (Algebra.norm E x) = -1 := by
  obtain ⟨x, hx⟩ :=
    exists_q8BiquadTwoAdicU_completedTopScalarExtensionNorm place hplace
  refine ⟨x, ?_⟩
  rw [hx,
    q8FirstConjugationSecondCompletedRingEquivAtFinitePlace_algebraMap
      P hPtwo place hQ]
  rw [← map_mul, q8BiquadTwoAdicU_mul_conjugate]
  simp

noncomputable def q8ActualTwoAdicFinitePlace
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P) :
    NumberField.FinitePlace K2 :=
  NumberField.FinitePlace.mk (q8BiquadContractedTwoPrime P hPtwo)

theorem q8ActualTwoAdicFinitePlace_two_mem
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P) :
    (2 : 𝓞 K2) ∈ (q8ActualTwoAdicFinitePlace P hPtwo).maximalIdeal.asIdeal := by
  rw [q8ActualTwoAdicFinitePlace, NumberField.FinitePlace.maximalIdeal_mk]
  exact q8BiquadContractedTwoPrime_two_mem P hPtwo

theorem q8ActualTwoAdicFinitePlace_maximalIdeal_asIdeal
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P) :
    (q8ActualTwoAdicFinitePlace P hPtwo).maximalIdeal.asIdeal =
      P.comap (algebraMap (𝓞 K2) (𝓞 K3)) := by
  rw [q8ActualTwoAdicFinitePlace, NumberField.FinitePlace.maximalIdeal_mk]
  rfl

/-- The actual selected dyadic top-field norm followed by the conjugate
biquadratic norm is `-1`. -/
theorem exists_q8ActualTwoAdicTotalNorm_neg_one
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P) :
    let place := q8ActualTwoAdicFinitePlace P hPtwo
    let E := GaloisForLFunctions.HTGeometry.ABHN.completion K2 (.finite place)
    ∃ x : TensorProduct K2 E K3,
      Algebra.norm E x *
          q8FirstConjugationSecondCompletedRingEquivAtFinitePlace
            P hPtwo place
              (q8ActualTwoAdicFinitePlace_maximalIdeal_asIdeal P hPtwo)
            (Algebra.norm E x) = -1 := by
  exact exists_q8ActualTwoAdicTotalNorm_neg_one_of_place P hPtwo
    (q8ActualTwoAdicFinitePlace P hPtwo)
    (q8ActualTwoAdicFinitePlace_two_mem P hPtwo)
    (q8ActualTwoAdicFinitePlace_maximalIdeal_asIdeal P hPtwo)

end
end RHTower

