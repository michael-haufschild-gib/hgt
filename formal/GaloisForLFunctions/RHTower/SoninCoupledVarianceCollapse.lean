import GaloisForLFunctions.RHTower.PrimeArchCenteredEisensteinResidual

/-!
# Small-aperture collapse of coupled Sonin variance

The local Shannon-area bound makes the full coupled all-prime residual column vanish in operator
norm as the Sonin aperture tends to zero.  Every polynomial with zero constant term therefore has
normalized source variance tending to zero.  Since every positive aperture is nondegenerate, this
discharges the previously conditional source-variance collapse interface.

The resulting classification is exact: the normalized Sonin source--target upper comparison is
unconditionally equivalent to RH.  The same holds after restriction to centered monic
`2`-Eisenstein residuals in any infinite degree set.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- The all-prime coupled column has the scalar Shannon-area bound on every source vector. -/
theorem norm_sq_soninAllPrimeColumnOperator_apply_le_area
    (a : ℝ) (ha : 0 < a) (x : SoninL2) :
    ‖soninAllPrimeColumnOperator a ha x‖ ^ 2 ≤
      ((128 * a ^ 2) * soninAllPrimeColumnWeightSqMass) * ‖x‖ ^ 2 := by
  rw [norm_sq_soninAllPrimeColumnOperator_apply_eq_tsum]
  have hpoint : ∀ pk : Nat.Primes × ℕ,
      ‖centralSoninWeightedPrimePowerResidual a pk x‖ ^ 2 ≤
        ContinuousLinearMap.hsNormSq
            (centralSoninWeightedPrimePowerResidual a pk) * ‖x‖ ^ 2 := by
    intro pk
    let R := centralSoninWeightedPrimePowerResidual a pk
    have hR : ContinuousLinearMap.IsHilbertSchmidt R :=
      centralSoninWeightedPrimePowerResidual_isHilbertSchmidt a ha pk
    have hop : ‖R‖ ≤ ContinuousLinearMap.hsNorm R :=
      ContinuousLinearMap.opNorm_le_hsNorm hR
    have happ : ‖R x‖ ≤ ‖R‖ * ‖x‖ := R.le_opNorm x
    have hnorm : ‖R x‖ ≤ ContinuousLinearMap.hsNorm R * ‖x‖ :=
      happ.trans (mul_le_mul_of_nonneg_right hop (norm_nonneg x))
    have hsq : ‖R x‖ ^ 2 ≤ (ContinuousLinearMap.hsNorm R * ‖x‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg (R x)) hnorm 2
    calc
      ‖R x‖ ^ 2 ≤ (ContinuousLinearMap.hsNorm R * ‖x‖) ^ 2 := hsq
      _ = ContinuousLinearMap.hsNormSq R * ‖x‖ ^ 2 := by
        rw [mul_pow, ContinuousLinearMap.hsNorm,
          Real.sq_sqrt (ContinuousLinearMap.hsNormSq_nonneg R)]
  have hsum : Summable (fun pk : Nat.Primes × ℕ =>
      ContinuousLinearMap.hsNormSq
          (centralSoninWeightedPrimePowerResidual a pk) * ‖x‖ ^ 2) :=
    (summable_centralSoninWeightedPrimePowerResidual_hsNormSq a ha).mul_right _
  calc
    ∑' pk : Nat.Primes × ℕ,
        ‖centralSoninWeightedPrimePowerResidual a pk x‖ ^ 2 ≤
      ∑' pk : Nat.Primes × ℕ,
        ContinuousLinearMap.hsNormSq
            (centralSoninWeightedPrimePowerResidual a pk) * ‖x‖ ^ 2 :=
      (Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hpoint hsum).tsum_le_tsum
        hpoint hsum
    _ = (∑' pk : Nat.Primes × ℕ,
        ContinuousLinearMap.hsNormSq
          (centralSoninWeightedPrimePowerResidual a pk)) * ‖x‖ ^ 2 :=
      tsum_mul_right
    _ ≤ ((128 * a ^ 2) * soninAllPrimeColumnWeightSqMass) * ‖x‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      simpa [soninAllPrimeColumnWeightSqMass] using
        tsum_centralSoninWeightedPrimePowerResidual_hsNormSq_le_area a ha

/-- Operator-norm square of the physical coupled column is at most its scalar area budget. -/
theorem norm_soninAllPrimeColumnOperator_sq_le_area
    (a : ℝ) (ha : 0 < a) :
    ‖soninAllPrimeColumnOperator a ha‖ ^ 2 ≤
      (128 * a ^ 2) * soninAllPrimeColumnWeightSqMass := by
  let R : ℝ := (128 * a ^ 2) * soninAllPrimeColumnWeightSqMass
  have hR : 0 ≤ R := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg a))
    soninAllPrimeColumnWeightSqMass_nonneg
  have hop : ‖soninAllPrimeColumnOperator a ha‖ ≤ Real.sqrt R := by
    apply (soninAllPrimeColumnOperator a ha).opNorm_le_bound (Real.sqrt_nonneg R)
    intro x
    apply (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg R) (norm_nonneg x))).mp
    calc
      ‖soninAllPrimeColumnOperator a ha x‖ ^ 2 ≤ R * ‖x‖ ^ 2 :=
        norm_sq_soninAllPrimeColumnOperator_apply_le_area a ha x
      _ = (Real.sqrt R * ‖x‖) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hR]
  calc
    ‖soninAllPrimeColumnOperator a ha‖ ^ 2 ≤ (Real.sqrt R) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hop 2
    _ = R := Real.sq_sqrt hR

/-- Hilbert-coordinate presentation of the coupled column has the same small-aperture area bound. -/
theorem norm_soninAllPrimeColumnCoordinateOperator_sq_le_area
    (a : ℝ) (ha : 0 < a) :
    ‖soninAllPrimeColumnCoordinateOperator a ha‖ ^ 2 ≤
      (128 * a ^ 2) * soninAllPrimeColumnWeightSqMass := by
  let U := (ContinuousLinearMap.hsBasis ℂ SoninL2).repr
  let C := soninAllPrimeColumnCoordinateOperator a ha
  let R : ℝ := (128 * a ^ 2) * soninAllPrimeColumnWeightSqMass
  have hR : 0 ≤ R := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg a))
    soninAllPrimeColumnWeightSqMass_nonneg
  have hop : ‖C‖ ≤ Real.sqrt R := by
    apply C.opNorm_le_bound (Real.sqrt_nonneg R)
    intro f
    let x : SoninL2 := U.symm f
    have happly : soninAllPrimeColumnOperator a ha x = C f := by
      simp [soninAllPrimeColumnOperator, C, U, x]
    have hxnorm : ‖x‖ = ‖f‖ := by
      simpa only [x] using U.symm.norm_map f
    calc
      ‖C f‖ = ‖soninAllPrimeColumnOperator a ha x‖ := by rw [happly]
      _ ≤ ‖soninAllPrimeColumnOperator a ha‖ * ‖x‖ :=
        (soninAllPrimeColumnOperator a ha).le_opNorm x
      _ ≤ Real.sqrt R * ‖x‖ :=
        mul_le_mul_of_nonneg_right
          ((sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg R)).mp
            (by
              rw [Real.sq_sqrt hR]
              exact norm_soninAllPrimeColumnOperator_sq_le_area a ha))
          (norm_nonneg x)
      _ = Real.sqrt R * ‖f‖ := by rw [hxnorm]
  calc
    ‖C‖ ^ 2 ≤ (Real.sqrt R) ^ 2 := pow_le_pow_left₀ (norm_nonneg C) hop 2
    _ = R := Real.sq_sqrt hR

/-- Finite coefficient `l1` mass used in the quantitative polynomial-variance estimate. -/
def soninCoupledPolynomialCoeffL1 (p : Polynomial ℝ) : ℝ :=
  ∑ k ∈ p.support, |p.coeff k|

/-- Every coupled moment is bounded by the aperture-dependent area radius to its degree. -/
theorem re_soninAllPrimeCoupledTraceMoment_le_area_pow_mul_zero
    (a : SoninPositiveAperture) (k : ℕ) :
    (soninAllPrimeCoupledTraceMoment a k).re ≤
      (((128 * a.1 ^ 2) * soninAllPrimeColumnWeightSqMass) ^ k) *
        (soninAllPrimeCoupledTraceMoment a 0).re := by
  let C := soninAllPrimeColumnCoordinateOperator a.1 a.2
  let R : ℝ := (128 * a.1 ^ 2) * soninAllPrimeColumnWeightSqMass
  have hC : ContinuousLinearMap.IsHilbertSchmidt C :=
    HilbertSchmidt.isHilbertSchmidt_toOperatorRect
      (soninAllPrimeColumnKernel_isHSRect a.1 a.2)
  have hCR : ‖C‖ ^ 2 ≤ R :=
    norm_soninAllPrimeColumnCoordinateOperator_sq_le_area a.1 a.2
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        (soninAllPrimeCoupledTraceMoment a (k + 1)).re ≤
            R * (soninAllPrimeCoupledTraceMoment a k).re := by
          simpa only [HTGeometry.quantumMasterEffectMoment,
            HTGeometry.quantumChannelEffect, soninAllPrimeCoupledTraceMoment,
            soninAllPrimeCoupledCoordinateEnergy, C] using
              HTGeometry.quantumMasterEffectMoment_succ_le_effectRadius_mul hC hCR k
        _ ≤ R * (R ^ k * (soninAllPrimeCoupledTraceMoment a 0).re) :=
          mul_le_mul_of_nonneg_left ih
            (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg a.1))
              soninAllPrimeColumnWeightSqMass_nonneg)
        _ = R ^ (k + 1) * (soninAllPrimeCoupledTraceMoment a 0).re := by
          rw [pow_succ]
          ring

/-- Ratio-normalized coupled moments obey the aperture-dependent compact-support envelope. -/
theorem re_soninAllPrimeCoupledTraceMoment_div_zero_le_area_pow
    (a : SoninCoupledNondegenerateAperture) (k : ℕ) :
    (soninAllPrimeCoupledTraceMoment a.1 k).re /
        (soninAllPrimeCoupledTraceMoment a.1 0).re ≤
      ((128 * a.1.1 ^ 2) * soninAllPrimeColumnWeightSqMass) ^ k := by
  rw [div_le_iff₀
    ((soninAllPrimeCoupledTraceMoment_zero_re_pos_iff_column_ne_zero a.1).2 a.2)]
  exact re_soninAllPrimeCoupledTraceMoment_le_area_pow_mul_zero a.1 k

/-- A zero-constant polynomial has normalized source square expectation of order at most `a^4`. -/
theorem soninCoupledMomentNormalizedExpectation_sq_le_coeffL1_mul_area_sq
    (a : SoninCoupledNondegenerateAperture) (q : Polynomial ℝ)
    (hq : q.coeff 0 = 0)
    (hRle : (128 * a.1.1 ^ 2) * soninAllPrimeColumnWeightSqMass ≤ 1) :
    HTGeometry.momentNormalizedExpectation
        (soninAllPrimeCoupledRealTraceMoment a.1) (q ^ 2) ≤
      soninCoupledPolynomialCoeffL1 (q ^ 2) *
        ((128 * a.1.1 ^ 2) * soninAllPrimeColumnWeightSqMass) ^ 2 := by
  let r : Polynomial ℝ := q ^ 2
  let R : ℝ := (128 * a.1.1 ^ 2) * soninAllPrimeColumnWeightSqMass
  have hR0 : 0 ≤ R := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg a.1.1))
    soninAllPrimeColumnWeightSqMass_nonneg
  have hX : Polynomial.X ∣ q := Polynomial.X_dvd_iff.mpr hq
  have hX2 : Polynomial.X ^ 2 ∣ r := by
    simpa only [r] using pow_dvd_pow_of_dvd hX 2
  have hk2 : ∀ k ∈ r.support, 2 ≤ k := by
    intro k hk
    have hkne : r.coeff k ≠ 0 := Polynomial.mem_support_iff.mp hk
    by_contra hnot
    exact hkne ((Polynomial.X_pow_dvd_iff.mp hX2) k (by omega))
  have hmass : 0 < soninAllPrimeCoupledRealTraceMoment a.1 0 :=
    soninAllPrimeCoupledRealTraceMoment_zero_pos a
  rw [HTGeometry.momentNormalizedExpectation,
    HTGeometry.momentFunctional_eq_support_sum]
  change (∑ k ∈ r.support,
      r.coeff k * soninAllPrimeCoupledRealTraceMoment a.1 k) /
        soninAllPrimeCoupledRealTraceMoment a.1 0 ≤ _
  rw [Finset.sum_div]
  calc
    ∑ k ∈ r.support,
        r.coeff k * soninAllPrimeCoupledRealTraceMoment a.1 k /
          soninAllPrimeCoupledRealTraceMoment a.1 0 ≤
      ∑ k ∈ r.support, |r.coeff k| * R ^ 2 := by
        apply Finset.sum_le_sum
        intro k hk
        have hratio0 : 0 ≤ soninAllPrimeCoupledRealTraceMoment a.1 k /
            soninAllPrimeCoupledRealTraceMoment a.1 0 :=
          div_nonneg (soninAllPrimeCoupledTraceMoment_re_nonneg a.1 k) hmass.le
        have hratiopow : soninAllPrimeCoupledRealTraceMoment a.1 k /
            soninAllPrimeCoupledRealTraceMoment a.1 0 ≤ R ^ k :=
          re_soninAllPrimeCoupledTraceMoment_div_zero_le_area_pow a k
        have hpow : R ^ k ≤ R ^ 2 :=
          pow_le_pow_of_le_one hR0 hRle (hk2 k hk)
        calc
          r.coeff k * soninAllPrimeCoupledRealTraceMoment a.1 k /
              soninAllPrimeCoupledRealTraceMoment a.1 0 =
            r.coeff k * (soninAllPrimeCoupledRealTraceMoment a.1 k /
              soninAllPrimeCoupledRealTraceMoment a.1 0) := by ring
          _ ≤ |r.coeff k| *
              (soninAllPrimeCoupledRealTraceMoment a.1 k /
                soninAllPrimeCoupledRealTraceMoment a.1 0) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) hratio0
          _ ≤ |r.coeff k| * R ^ k :=
            mul_le_mul_of_nonneg_left hratiopow (abs_nonneg _)
          _ ≤ |r.coeff k| * R ^ 2 :=
            mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
    _ = soninCoupledPolynomialCoeffL1 r * R ^ 2 := by
      rw [soninCoupledPolynomialCoeffL1, Finset.sum_mul]

/-- Quantitative small-aperture bound for normalized coupled Sonin polynomial variance. -/
theorem soninCoupledMomentNormalizedVariance_le_coeffL1_mul_area_sq
    (a : SoninCoupledNondegenerateAperture) (q : Polynomial ℝ)
    (hq : q.coeff 0 = 0)
    (hRle : (128 * a.1.1 ^ 2) * soninAllPrimeColumnWeightSqMass ≤ 1) :
    HTGeometry.momentNormalizedVariance
        (soninAllPrimeCoupledRealTraceMoment a.1) q ≤
      soninCoupledPolynomialCoeffL1 (q ^ 2) *
        ((128 * a.1.1 ^ 2) * soninAllPrimeColumnWeightSqMass) ^ 2 :=
  (HTGeometry.momentNormalizedVariance_le_secondMoment _ q).trans
    (soninCoupledMomentNormalizedExpectation_sq_le_coeffL1_mul_area_sq a q hq hRle)

/-- **Unconditional source collapse.** Every fixed zero-constant integer test admits positive,
nondegenerate Sonin apertures with arbitrarily small normalized source variance. -/
theorem soninCoupledPrimeArchNormalizedVarianceCollapseToZero :
    SoninCoupledPrimeArchNormalizedVarianceCollapseToZero := by
  intro q hq δ hδ
  let p : Polynomial ℝ := q.map (Int.castRingHom ℝ)
  let d : ℝ := min δ 1
  let A : ℝ := 128 * soninAllPrimeColumnWeightSqMass
  let C : ℝ := soninCoupledPolynomialCoeffL1 (p ^ 2)
  let K : ℝ := 1 + A + C
  let av : ℝ := d / K ^ 2
  have hp0 : p.coeff 0 = 0 := by
    simp [p, hq]
  have hd0 : 0 < d := lt_min hδ zero_lt_one
  have hd1 : d ≤ 1 := min_le_right _ _
  have hdδ : d ≤ δ := min_le_left _ _
  have hA0 : 0 ≤ A := mul_nonneg (by norm_num) soninAllPrimeColumnWeightSqMass_nonneg
  have hC0 : 0 ≤ C := by
    dsimp only [C, soninCoupledPolynomialCoeffL1]
    positivity
  have hK1 : 1 ≤ K := by
    dsimp only [K]
    nlinarith
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK1
  have hKsq0 : 0 < K ^ 2 := sq_pos_of_pos hK0
  have hKsq1 : 1 ≤ K ^ 2 := by nlinarith
  have hav0 : 0 < av := div_pos hd0 hKsq0
  have hav1 : av ≤ 1 := by
    rw [div_le_one hKsq0]
    exact hd1.trans hKsq1
  let a : SoninCoupledNondegenerateAperture :=
    soninCoupledNondegenerateAperture ⟨av, hav0⟩
  have hAleK : A ≤ K := by
    dsimp only [K]
    nlinarith
  have hCleK : C ≤ K := by
    dsimp only [K]
    nlinarith
  have havsq : av ^ 2 ≤ av := by nlinarith
  have hRle : A * av ^ 2 ≤ d / K := by
    calc
      A * av ^ 2 ≤ K * av ^ 2 :=
        mul_le_mul_of_nonneg_right hAleK (sq_nonneg av)
      _ ≤ K * av := mul_le_mul_of_nonneg_left havsq hK0.le
      _ = d / K := by
        dsimp only [av]
        field_simp [hK0.ne']
  have hdKle1 : d / K ≤ 1 := by
    rw [div_le_one hK0]
    exact hd1.trans hK1
  have hsourceRle :
      (128 * a.1.1 ^ 2) * soninAllPrimeColumnWeightSqMass ≤ 1 := by
    simpa only [A, a, soninCoupledNondegenerateAperture_value,
      mul_assoc, mul_left_comm, mul_comm] using hRle.trans hdKle1
  have hR0 : 0 ≤ A * av ^ 2 := mul_nonneg hA0 (sq_nonneg av)
  have hR2 : (A * av ^ 2) ^ 2 ≤ (d / K) ^ 2 :=
    pow_le_pow_left₀ hR0 hRle 2
  have hbound : C * (A * av ^ 2) ^ 2 ≤ δ := by
    calc
      C * (A * av ^ 2) ^ 2 ≤ K * (A * av ^ 2) ^ 2 :=
        mul_le_mul_of_nonneg_right hCleK (sq_nonneg _)
      _ ≤ K * (d / K) ^ 2 := mul_le_mul_of_nonneg_left hR2 hK0.le
      _ = d ^ 2 / K := by
        field_simp [hK0.ne']
      _ ≤ d := by
        rw [div_le_iff₀ hK0]
        nlinarith
      _ ≤ δ := hdδ
  refine ⟨a, ?_⟩
  have hv := soninCoupledMomentNormalizedVariance_le_coeffL1_mul_area_sq
    a p hp0 hsourceRle
  change HTGeometry.momentNormalizedVariance
      (soninAllPrimeCoupledRealTraceMoment a.1) p ≤ δ
  calc
    HTGeometry.momentNormalizedVariance
        (soninAllPrimeCoupledRealTraceMoment a.1) p ≤
      C * (A * av ^ 2) ^ 2 := by
        simpa only [C, A, a, soninCoupledNondegenerateAperture_value,
          mul_assoc, mul_left_comm, mul_comm] using hv
    _ ≤ δ := hbound

/-- With source collapse discharged, the normalized Sonin comparison is exactly target
vacuum-Feshbach nonnegativity. -/
theorem soninCoupledPrimeArchNormalizedVarianceUpperBound_iff_targetNonnegative :
    SoninCoupledPrimeArchNormalizedVarianceUpperBound ↔
      PrimeArchVacuumFeshbachIntNonnegative :=
  soninCoupledPrimeArchNormalizedVarianceUpperBound_iff_targetNonnegative_of_collapse
    soninCoupledPrimeArchNormalizedVarianceCollapseToZero

/-- With source collapse discharged, the normalized Sonin comparison is exactly RH. -/
theorem soninCoupledPrimeArchNormalizedVarianceUpperBound_iff_riemannHypothesis :
    SoninCoupledPrimeArchNormalizedVarianceUpperBound ↔ RiemannHypothesis :=
  soninCoupledPrimeArchNormalizedVarianceUpperBound_iff_riemannHypothesis_of_collapse
    soninCoupledPrimeArchNormalizedVarianceCollapseToZero

/-- Small-aperture collapse classifies the moment-Feshbach source comparison exactly as RH. -/
theorem soninCoupledPrimeArchVacuumSourceFeshbachUpperBound_iff_riemannHypothesis :
    SoninCoupledPrimeArchVacuumSourceFeshbachUpperBound ↔ RiemannHypothesis :=
  soninCoupledPrimeArchPureStateQuantumFisherUpperBound_iff_sourceFeshbach.symm.trans
    (soninCoupledPrimeArchPureStateQuantumFisherUpperBound_iff_normalizedVariance.trans
      soninCoupledPrimeArchNormalizedVarianceUpperBound_iff_riemannHypothesis)

/-- Small-aperture collapse classifies pure-state quantum-Fisher comparison exactly as RH. -/
theorem soninCoupledPrimeArchPureStateQuantumFisherUpperBound_iff_riemannHypothesis :
    SoninCoupledPrimeArchPureStateQuantumFisherUpperBound ↔ RiemannHypothesis :=
  soninCoupledPrimeArchPureStateQuantumFisherUpperBound_iff_normalizedVariance.trans
    soninCoupledPrimeArchNormalizedVarianceUpperBound_iff_riemannHypothesis

/-- Small-aperture collapse classifies counterterm-free projective Fisher comparison exactly as
RH. -/
theorem soninCoupledPrimeArchVacuumProjectiveFisherUpperBound_iff_riemannHypothesis :
    SoninCoupledPrimeArchVacuumProjectiveFisherUpperBound ↔ RiemannHypothesis :=
  soninCoupledPrimeArchVacuumProjectiveFisherUpperBound_iff_sourceFeshbach.trans
    soninCoupledPrimeArchVacuumSourceFeshbachUpperBound_iff_riemannHypothesis

/-- Small-aperture collapse classifies quotient-free projective Robertson comparison exactly as
RH. -/
theorem soninCoupledPrimeArchVacuumProjectiveRobertsonUpperBound_iff_riemannHypothesis :
    SoninCoupledPrimeArchVacuumProjectiveRobertsonUpperBound ↔ RiemannHypothesis :=
  soninCoupledPrimeArchVacuumProjectiveRobertsonUpperBound_iff_fisher.trans
    soninCoupledPrimeArchVacuumProjectiveFisherUpperBound_iff_riemannHypothesis

/-- Small-aperture collapse classifies the aperture-plus-counterterm variance comparison exactly
as RH. -/
theorem soninCoupledPrimeArchVacuumVarianceRayleighUpperBound_iff_riemannHypothesis :
    SoninCoupledPrimeArchVacuumVarianceRayleighUpperBound ↔ RiemannHypothesis :=
  soninCoupledPrimeArchVacuumSourceFeshbachUpperBound_iff_variance.symm.trans
    soninCoupledPrimeArchVacuumSourceFeshbachUpperBound_iff_riemannHypothesis

/-- Small-aperture collapse classifies quotient-free Robertson Rayleigh comparison exactly as
RH. -/
theorem soninCoupledPrimeArchVacuumRobertsonRayleighUpperBound_iff_riemannHypothesis :
    SoninCoupledPrimeArchVacuumRobertsonRayleighUpperBound ↔ RiemannHypothesis :=
  soninCoupledPrimeArchVacuumRobertsonRayleighUpperBound_iff_variance.trans
    soninCoupledPrimeArchVacuumVarianceRayleighUpperBound_iff_riemannHypothesis

/-- On any infinite degree set, even the structured centered `2`-Eisenstein Sonin comparison is
exactly RH; its source-smallness component is now unconditional. -/
theorem soninCoupledPrimeArchCenteredTwoEisensteinResidualUpper_iff_riemannHypothesis
    {D : Set ℕ} (hD : D.Infinite) :
    SoninCoupledPrimeArchCenteredTwoEisensteinResidualNormalizedVarianceUpperBound D ↔
      RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_soninCoupledPrimeArchCenteredTwoEisensteinResidualUpper hD
  · intro hRH P _ _ _ _ ε hε
    exact (soninCoupledPrimeArchNormalizedVarianceUpperBound_iff_riemannHypothesis.mpr hRH)
      (HTGeometry.polynomialVacuumTail P)
      (HTGeometry.polynomialVacuumTail_coeff_zero P) ε hε

/-- Small-aperture collapse also classifies the comparison restricted to the strict complement
of the unconditional centered analytic-tail cone. -/
theorem soninCoupledPrimeArchCenteredResidualNormalizedVarianceUpperBound_iff_riemannHypothesis :
    SoninCoupledPrimeArchCenteredResidualNormalizedVarianceUpperBound ↔
      RiemannHypothesis := by
  constructor
  · exact
      riemannHypothesis_of_soninCoupledPrimeArchCenteredResidualNormalizedVarianceUpperBound
  · intro hRH q hq _hres ε hε
    exact
      (soninCoupledPrimeArchNormalizedVarianceUpperBound_iff_riemannHypothesis.mpr hRH)
        q hq ε hε

end

end RHTower
