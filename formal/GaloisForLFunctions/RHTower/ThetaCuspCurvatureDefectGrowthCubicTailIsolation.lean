import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectGrowthDominantCubic
/-!
# Exact mixed-tail isolation after dominant cubic absorption

Every full convolution power splits into its literal dominant power and
a positive mixed remainder with support at least 3k+5. The transfer of
this remainder is nonnegative and bounded by its own eighth moment.
Consequently only the mixed cubic error receives a monomial envelope;
the pure cubic keeps its cancellation-preserving pair comparison.

The resulting complete-source residual retains a strictly positive pair
coefficient throughout the actual source ray. Absorption of the deep
single tail, mixed cubic moment, and sectors five and seven remains open.
-/

namespace RHTower.ThetaCuspDefect
open MeasureTheory
open scoped BigOperators
noncomputable section

def convolutionPower (μ : Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | k+1 => μ ∗ convolutionPower μ k

def mixedConvolutionRemainder (μ ν : Measure ℝ) : ℕ → Measure ℝ
  | 0 => 0
  | k+1 => (μ+ν) ∗ mixedConvolutionRemainder μ ν k+ν ∗ convolutionPower μ k

theorem convolutionPower_finite (μ : Measure ℝ) [IsFiniteMeasure μ] (k : ℕ) :
    IsFiniteMeasure (convolutionPower μ k) := by
  induction k with
  | zero => change IsFiniteMeasure (Measure.dirac (0:ℝ)); infer_instance
  | succ k ih =>
      letI := ih
      change IsFiniteMeasure (μ ∗ convolutionPower μ k)
      infer_instance

theorem mixedConvolutionRemainder_finite (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (k : ℕ) : IsFiniteMeasure (mixedConvolutionRemainder μ ν k) := by
  induction k with
  | zero => change IsFiniteMeasure (0:Measure ℝ); infer_instance
  | succ k ih =>
      letI := ih
      letI := convolutionPower_finite μ k
      change IsFiniteMeasure ((μ+ν) ∗ mixedConvolutionRemainder μ ν k+ν ∗ convolutionPower μ k)
      infer_instance

theorem integrable_pow_convolutionPower (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : ∀ j : ℕ, Integrable (fun t : ℝ => t^j) μ) (k j : ℕ) :
    Integrable (fun t : ℝ => t^j) (convolutionPower μ k) := by
  induction k generalizing j with
  | zero => change Integrable _ (Measure.dirac 0); exact integrable_dirac (by simp)
  | succ k ih =>
      letI := convolutionPower_finite μ k
      exact integrable_pow_measure_conv μ _ hμ ih j

theorem integrable_pow_mixedConvolutionRemainder (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ j : ℕ, Integrable (fun t : ℝ => t^j) μ)
    (hν : ∀ j : ℕ, Integrable (fun t : ℝ => t^j) ν) (k j : ℕ) :
    Integrable (fun t : ℝ => t^j) (mixedConvolutionRemainder μ ν k) := by
  induction k generalizing j with
  | zero => simp [mixedConvolutionRemainder]
  | succ k ih =>
      letI := convolutionPower_finite μ k
      letI := mixedConvolutionRemainder_finite μ ν k
      exact (integrable_pow_measure_conv (μ+ν) _ (fun i => (hμ i).add_measure (hν i)) ih j).add_measure
        (integrable_pow_measure_conv ν _ hν (integrable_pow_convolutionPower μ hμ k) j)

theorem convolutionPower_add_split (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (k : ℕ) :
    convolutionPower (μ+ν) k=convolutionPower μ k+mixedConvolutionRemainder μ ν k := by
  induction k with
  | zero => simp [convolutionPower,mixedConvolutionRemainder]
  | succ k ih =>
      letI := convolutionPower_finite μ k
      letI := mixedConvolutionRemainder_finite μ ν k
      rw [convolutionPower,ih,Measure.conv_add,Measure.add_conv]
      change (μ ∗ convolutionPower μ k+ν ∗ convolutionPower μ k)+
        (μ+ν) ∗ mixedConvolutionRemainder μ ν k=
        μ ∗ convolutionPower μ k+((μ+ν) ∗ mixedConvolutionRemainder μ ν k+ν ∗ convolutionPower μ k)
      ac_rfl

theorem ae_lower_convolutionPower (μ : Measure ℝ) [IsFiniteMeasure μ]
    {a : ℝ} (hs : ∀ᵐ t ∂μ, a ≤ t) (k : ℕ) :
    ∀ᵐ t ∂convolutionPower μ k, a*(k:ℝ) ≤ t := by
  induction k with
  | zero => simp [convolutionPower]
  | succ k ih =>
      letI := convolutionPower_finite μ k
      have h := ae_add_lower_measure_conv μ _ hs ih
      change ∀ᵐ t ∂(μ ∗ convolutionPower μ k), a*((k+1:ℕ):ℝ) ≤ t
      filter_upwards [h] with t ht
      push_cast
      nlinarith

theorem ae_lower_mixedConvolutionRemainder (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hμ : ∀ᵐ t ∂μ, (3:ℝ) ≤ t) (hν : ∀ᵐ t ∂ν, (8:ℝ) ≤ t)
    (k : ℕ) : ∀ᵐ t ∂mixedConvolutionRemainder μ ν k, 3*(k:ℝ)+5 ≤ t := by
  have hν3 : ∀ᵐ t ∂ν, (3:ℝ) ≤ t := by filter_upwards [hν] with t ht; linarith
  have hμν : ∀ᵐ t ∂μ+ν, (3:ℝ) ≤ t := ae_add_measure_iff.mpr ⟨hμ,hν3⟩
  induction k with
  | zero => simp [mixedConvolutionRemainder]
  | succ k ih =>
      letI := convolutionPower_finite μ k
      letI := mixedConvolutionRemainder_finite μ ν k
      have h1 := ae_add_lower_measure_conv (μ+ν) _ hμν ih
      have h2 := ae_add_lower_measure_conv ν _ hν (ae_lower_convolutionPower μ hμ k)
      rw [mixedConvolutionRemainder,ae_add_measure_iff]
      constructor
      · filter_upwards [h1] with t ht
        push_cast
        linarith
      · filter_upwards [h2] with t ht
        push_cast
        linarith

theorem measureMoment_convolutionPower (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : ∀ j : ℕ, Integrable (fun t : ℝ => t^j) μ) (k : ℕ) {j : ℕ} (hj : j ≤ 8) :
    measureMoment (convolutionPower μ k) j=spectralPowerMoment (measureMoment μ) k j := by
  induction k generalizing j with
  | zero =>
      by_cases hj0 : j=0
      · subst j; norm_num [convolutionPower,measureMoment,spectralPowerMoment]
      · simp [convolutionPower,measureMoment,spectralPowerMoment,PowerSeries.coeff_one,hj0]
  | succ k ih =>
      letI := convolutionPower_finite μ k
      rw [convolutionPower,measureMoment_conv _ _ hμ (integrable_pow_convolutionPower μ hμ k),
        spectralPowerMoment_succ _ k hj]
      unfold momentConvolution
      apply Finset.sum_congr rfl
      intro i hi
      rw [ih (by omega : j-i ≤ 8)]

theorem growthTransferFunctional_convolutionPower (q : ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : ∀ j : ℕ, Integrable (fun t : ℝ => t^j) μ) (k : ℕ) :
    growthTransferFunctional q (measureMoment (convolutionPower μ k))=
      growthTransferFunctional q (spectralPowerMoment (measureMoment μ) k) := by
  unfold growthTransferFunctional
  apply Finset.sum_congr rfl
  intro i hi
  have hi5 : i ≤ 5 := by have := Finset.mem_range.mp hi; omega
  rw [measureMoment_convolutionPower μ hμ k (by omega : i+2 ≤ 8),
    measureMoment_convolutionPower μ hμ k (by omega : i+3 ≤ 8)]

theorem mixedPower_transfer_bounds {q : ℝ} (hq : 3/2 ≤ q) (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ j : ℕ, Integrable (fun t : ℝ => t^j) μ)
    (hν : ∀ j : ℕ, Integrable (fun t : ℝ => t^j) ν)
    (hsμ : ∀ᵐ t ∂μ, (3:ℝ) ≤ t) (hsν : ∀ᵐ t ∂ν, (8:ℝ) ≤ t)
    {k : ℕ} (hk : 1 ≤ k) :
    0 ≤ growthTransferFunctional q (spectralPowerMoment (measureMoment (μ+ν)) k)-
      growthTransferFunctional q (spectralPowerMoment (measureMoment μ) k) ∧
    growthTransferFunctional q (spectralPowerMoment (measureMoment (μ+ν)) k)-
      growthTransferFunctional q (spectralPowerMoment (measureMoment μ) k) ≤
        growthTransferLeadingCoefficient q*(spectralPowerMoment (measureMoment (μ+ν)) k 8-
          spectralPowerMoment (measureMoment μ) k 8) := by
  have hsum (j : ℕ) := (hμ j).add_measure (hν j)
  have hM : measureMoment (convolutionPower (μ+ν) k)=fun j =>
      measureMoment (convolutionPower μ k) j+measureMoment (mixedConvolutionRemainder μ ν k) j := by
    funext j
    rw [convolutionPower_add_split,measureMoment,integral_add_measure
      (integrable_pow_convolutionPower μ hμ k j) (integrable_pow_mixedConvolutionRemainder μ ν hμ hν k j)]
    rfl
  have hs := ae_lower_mixedConvolutionRemainder μ ν hsμ hsν k
  have h8 : ∀ᵐ t ∂mixedConvolutionRemainder μ ν k, (8:ℝ) ≤ t := by
    have hkr : (1:ℝ) ≤ k := by exact_mod_cast hk
    filter_upwards [hs] with t ht
    linarith
  have hi := integrable_pow_mixedConvolutionRemainder μ ν hμ hν k
  have hT : 0 ≤ growthTransferFunctional q (measureMoment (mixedConvolutionRemainder μ ν k)) ∧
      growthTransferFunctional q (measureMoment (mixedConvolutionRemainder μ ν k)) ≤
        growthTransferLeadingCoefficient q*measureMoment (mixedConvolutionRemainder μ ν k) 8 := by
    rw [←integral_growthTransferKernel q _ hi]
    constructor
    · apply integral_nonneg_of_ae
      filter_upwards [h8] with t ht
      exact (growthTransferKernel_pos hq ht).le
    · rw [measureMoment,←integral_const_mul]
      apply integral_mono_ae (integrable_growthTransferKernel q _ hi) ((hi 8).const_mul _)
      filter_upwards [h8] with t ht
      exact growthTransferKernel_le_monomial hq ht
  rw [←growthTransferFunctional_convolutionPower q (μ+ν) hsum,
    ←growthTransferFunctional_convolutionPower q μ hμ,
    ←measureMoment_convolutionPower (μ+ν) hsum k (by omega : 8 ≤ 8),
    ←measureMoment_convolutionPower μ hμ k (by omega : 8 ≤ 8),hM,growthTransferFunctional_add]
  simpa only [add_sub_cancel_left] using hT

theorem sourceMixedPower_transfer_bounds {q : ℝ} (hq : 3/2 ≤ q) {k : ℕ} (hk : 1 ≤ k) :
    0 ≤ rawTransferSector q k-growthTransferFunctional q (spectralPowerMoment (atomMoment 2 q) k) ∧
      rawTransferSector q k-growthTransferFunctional q (spectralPowerMoment (atomMoment 2 q) k) ≤
        growthTransferLeadingCoefficient q*
          (spectralPowerMoment (thetaCuspHigherLikelihoodSpectralMoment q) k 8-
            spectralPowerMoment (atomMoment 2 q) k 8) := by
  have hq0 : 0 < q := by linarith
  let A := componentTilt q thetaCuspSecondAtomSpectralMeasure
  let D := componentTilt q thetaCuspDeepTailSpectralMeasure
  have hiA := integrable_pow_componentTilt q thetaCuspSecondAtomSpectralMeasure
    (fun j => integrable_pow_mul_exp_neg_thetaCuspSecondAtomSpectralMeasure j hq0)
  have hiD := integrable_pow_componentTilt q thetaCuspDeepTailSpectralMeasure
    (fun j => integrable_pow_mul_exp_neg_thetaCuspDeepTailSpectralMeasure j hq0)
  letI : IsFiniteMeasure A := componentTilt_finite q thetaCuspSecondAtomSpectralMeasure
    (fun j => integrable_pow_mul_exp_neg_thetaCuspSecondAtomSpectralMeasure j hq0)
  letI : IsFiniteMeasure D := componentTilt_finite q thetaCuspDeepTailSpectralMeasure
    (fun j => integrable_pow_mul_exp_neg_thetaCuspDeepTailSpectralMeasure j hq0)
  have hA : measureMoment A=atomMoment 2 q := by
    funext j
    rw [measureMoment_componentTilt]
    simp only [atomMoment,thetaCuspSecondAtomSpectralMeasure,neg_mul]
  have hD : measureMoment D=thetaCuspDeepTailMoment q := by
    funext j
    exact measureMoment_componentTilt q _ j
  have hsum : measureMoment (A+D)=thetaCuspHigherLikelihoodSpectralMoment q := by
    funext j
    have he : measureMoment (A+D) j=measureMoment A j+measureMoment D j := by
      unfold measureMoment
      exact integral_add_measure (hiA j) (hiD j)
    rw [he,hA,hD]
    simpa only [atomMoment,thetaCuspSecondAtomMoment,thetaCuspSecondAtomSpectralMeasure,neg_mul] using
      (thetaCuspHigherLikelihoodSpectralMoment_eq_second_add_deep hq0 j).symm
  have hsA : ∀ᵐ t ∂A, (3:ℝ) ≤ t :=
    ae_lower_componentTilt q _ (ae_three_le_thetaCuspHigherLikelihoodSpectralMeasure.filter_mono
      (ae_mono thetaCuspSecondAtomSpectralMeasure_le))
  have hsD : ∀ᵐ t ∂D, (8:ℝ) ≤ t :=
    ae_lower_componentTilt q _ ae_eight_le_thetaCuspDeepTailSpectralMeasure
  have h := mixedPower_transfer_bounds hq A D hiA hiD hsA hsD hk
  rw [hsum,hA] at h
  exact h

def mixedPowerMoment (q : ℝ) (k j : ℕ) : ℝ :=
  spectralPowerMoment (thetaCuspHigherLikelihoodSpectralMoment q) k j-
    spectralPowerMoment (atomMoment 2 q) k j

theorem mixedPowerMoment_eight_nonneg {q : ℝ} (hq : 3/2 ≤ q) {k : ℕ} (hk : 1 ≤ k) :
    0 ≤ mixedPowerMoment q k 8 := by
  have h := sourceMixedPower_transfer_bounds hq hk
  have hc := growthTransferLeadingCoefficient_pos hq
  unfold mixedPowerMoment
  nlinarith [h.1,h.2]

theorem sourceCubic_transfer_le_exact_dominant_and_mixed {q : ℝ} (hq : 3/2 ≤ q) :
    normalizedTransferWeight q 3*rawTransferSector q 3 ≤
      ((2:ℝ)^8/3)*atomMoment 2 q 0*dominantPairTransfer q+
        (growthTransferLeadingCoefficient q/3)*mixedPowerMoment q 3 8 := by
  have hq0 : 0 < q := by linarith
  have hmix := (sourceMixedPower_transfer_bounds hq (k:=3) (by omega)).2
  change rawTransferSector q 3-growthTransferFunctional q (spectralPowerMoment (atomMoment 2 q) 3) ≤
    growthTransferLeadingCoefficient q*mixedPowerMoment q 3 8 at hmix
  have hcubic := dominantCubic_transfer_le_pair hq
  have hpair : 0 < dominantPairTransfer q := growthTransferFunctional_dominant_pair_pos hq
  have hc := growthTransferLeadingCoefficient_pos hq
  have he := mixedPowerMoment_eight_nonneg hq (k:=3) (by omega)
  have ha : 0 ≤ atomMoment 2 q 0 := by
    simpa only [atomMoment,thetaCuspSecondAtomMoment,thetaCuspSecondAtomSpectralMeasure,neg_mul] using
      thetaCuspSecondAtomMoment_nonneg q 0
  have hupper : rawTransferSector q 3 ≤ (2:ℝ)^8*atomMoment 2 q 0*dominantPairTransfer q+
      growthTransferLeadingCoefficient q*mixedPowerMoment q 3 8 := by linarith
  have hupper0 : 0 ≤ (2:ℝ)^8*atomMoment 2 q 0*dominantPairTransfer q+
      growthTransferLeadingCoefficient q*mixedPowerMoment q 3 8 := by positivity
  have h1 := mul_le_mul_of_nonneg_left hupper
    (normalizedTransferWeight_pos hq0 (k:=3) (by omega)).le
  have h2 := mul_le_mul_of_nonneg_right
    (normalizedTransferWeight_le hq0 (k:=3) (by omega)) hupper0
  norm_num at h1 h2 ⊢
  nlinarith only [h1,h2]

def cubicAbsorptionResidual (q : ℝ) : ℝ :=
  (1/(2*thetaCuspLikelihoodPartition q^2)-(2:ℝ)^8/3*atomMoment 2 q 0)*dominantPairTransfer q-
    growthTransferLeadingCoefficient q*(thetaCuspDeepTailMoment q 8+mixedPowerMoment q 3 8/3+
      ((5:ℝ)^7*thetaCuspHigherLikelihoodSpectralMoment q 0^4+
       (7:ℝ)^7*thetaCuspHigherLikelihoodSpectralMoment q 0^6)*thetaCuspHigherLikelihoodSpectralMoment q 8)

theorem sourceTransfer_le_neg_cubic_residual {q : ℝ} (hq : 3/2 ≤ q) :
    growthTransferFunctional q (likelihoodCumulantEight q) ≤ -cubicAbsorptionResidual q := by
  have hq0 : 0 < q := by linarith
  have hsingle : normalizedTransferWeight q 1*rawTransferSector q 1 ≤
      growthTransferLeadingCoefficient q*thetaCuspDeepTailMoment q 8 := by
    unfold rawTransferSector
    rw [sourceTransfer_single_eq_deep hq0]
    have hw : normalizedTransferWeight q 1 ≤ 1 := by
      simpa using normalizedTransferWeight_le hq0 (k:=1) (by omega)
    exact (mul_le_of_le_one_left (deepTransfer_bounds hq).1 hw).trans (deepTransfer_bounds hq).2
  have hpair0 : 0 < dominantPairTransfer q := growthTransferFunctional_dominant_pair_pos hq
  have hpair : dominantPairTransfer q/(2*thetaCuspLikelihoodPartition q^2) ≤
      normalizedTransferWeight q 2*rawTransferSector q 2 := by
    calc
      _=(1/(2*thetaCuspLikelihoodPartition q^2))*dominantPairTransfer q := by ring
      _≤normalizedTransferWeight q 2*dominantPairTransfer q :=
        mul_le_mul_of_nonneg_right (normalizedTransferWeight_pair_lower hq0) hpair0.le
      _≤_ := mul_le_mul_of_nonneg_left (sourceTransfer_pair_dominant_le hq)
        (normalizedTransferWeight_pos hq0 (k:=2) (by omega)).le
  have h3 := sourceCubic_transfer_le_exact_dominant_and_mixed hq
  have h5 := normalizedTransferSector_le hq (k:=5) (by omega)
  have h7 := normalizedTransferSector_le hq (k:=7) (by omega)
  have heven (k : ℕ) (hk : 3 ≤ k ∧ k ≤ 8) :
      0 ≤ normalizedTransferWeight q k*rawTransferSector q k :=
    mul_nonneg (normalizedTransferWeight_pos hq0 (by omega)).le
      (sourceConvolution_transfer_bounds hq hk.1).1
  have h4 := heven 4 (by omega)
  have h6 := heven 6 (by omega)
  have h8 := heven 8 (by omega)
  rw [sourceTransfer_raw_decomposition]
  unfold cubicAbsorptionResidual
  norm_num [div_eq_mul_inv,mul_inv_rev] at hpair h3 h5 h7 ⊢
  nlinarith only [hsingle,hpair,h3,h5,h7,h4,h6,h8]

/-- The actual source keeps a strictly positive pair coefficient after exact cubic absorption. -/
theorem cubic_pair_coefficient_pos {x : ℝ} (hx : 0 ≤ x) :
    0 < 1/(2*thetaCuspLikelihoodPartition (thetaCuspLikelihoodCoordinate x)^2)-
      (2:ℝ)^8/3*atomMoment 2 (thetaCuspLikelihoodCoordinate x) 0 := by
  let q := thetaCuspLikelihoodCoordinate x
  have hq0 : 0 < q := thetaCuspLikelihoodCoordinate_pos hx
  have hP := thetaCuspLikelihoodPartition_pos hq0
  have ha0 : 0 ≤ atomMoment 2 q 0 := by
    simpa only [atomMoment,thetaCuspSecondAtomMoment,thetaCuspSecondAtomSpectralMeasure,neg_mul] using
      thetaCuspSecondAtomMoment_nonneg q 0
  have hM : atomMoment 2 q 0 ≤ thetaCuspHigherLikelihoodSpectralMoment q 0 := by
    have he : thetaCuspHigherLikelihoodSpectralMoment q 0=
        atomMoment 2 q 0+thetaCuspDeepTailMoment q 0 := by
      simpa only [atomMoment,thetaCuspSecondAtomMoment,thetaCuspSecondAtomSpectralMeasure,neg_mul] using
        thetaCuspHigherLikelihoodSpectralMoment_eq_second_add_deep hq0 0
    rw [he]
    exact le_add_of_nonneg_right (thetaCuspDeepTailMoment_nonneg q 0)
  have hactivity := three_hundred_ninety_nine_mul_thetaCuspHigherLikelihoodSpectralResponse_lt_one hx
  change 399*thetaCuspHigherLikelihoodSpectralResponse q < 1 at hactivity
  rw [←thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hq0] at hactivity
  have hmass : atomMoment 2 q 0 < 1/399 := by linarith
  have hpartition : thetaCuspLikelihoodPartition q < 400/399 := by
    rw [thetaCuspLikelihoodPartition_eq_one_add_moment_zero hq0]
    linarith
  have hsq : thetaCuspLikelihoodPartition q^2 < (400/399:ℝ)^2 := by nlinarith
  change 0 < 1/(2*thetaCuspLikelihoodPartition q^2)-(2:ℝ)^8/3*atomMoment 2 q 0
  apply sub_pos.mpr
  apply (lt_div_iff₀ (by positivity : 0 < 2*thetaCuspLikelihoodPartition q^2)).mpr
  calc
    _ ≤ ((2:ℝ)^8/3*(1/399))*(2*(400/399:ℝ)^2) := by
      gcongr
    _ < 1 := by norm_num

end
end RHTower.ThetaCuspDefect


