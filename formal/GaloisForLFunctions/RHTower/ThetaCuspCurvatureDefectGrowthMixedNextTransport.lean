import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectGrowthCubicTailIsolation
import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectGrowthNextEnvelope
import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectGrowthMixedPairSource
import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectGrowthNextSourceFlow
import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectGrowthMarkedMoments
/-! Exact next-transfer transport of the positive mixed remainder,
source single/pair cancellations, and convolution moment flow. -/

namespace RHTower.ThetaCuspDefect
open scoped BigOperators
open MeasureTheory Filter Set
noncomputable section
theorem measureMoment_convolutionPower_nine (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : ∀ j : ℕ, Integrable (fun t : ℝ => t^j) μ) (k : ℕ) {j : ℕ} (hj : j ≤ 9) :
    measureMoment (convolutionPower μ k) j=spectralPowerMoment (measureMoment μ) k j := by
  induction k generalizing j with
  | zero =>
      by_cases hj0 : j=0
      · subst j; norm_num [convolutionPower,measureMoment,spectralPowerMoment]
      · simp [convolutionPower,measureMoment,spectralPowerMoment,PowerSeries.coeff_one,hj0]
  | succ k ih =>
      letI := convolutionPower_finite μ k
      rw [convolutionPower,measureMoment_conv _ _ hμ (integrable_pow_convolutionPower μ hμ k),
        spectralPowerMoment_succ_nine _ k hj]
      unfold momentConvolution
      apply Finset.sum_congr rfl
      intro i hi
      rw [ih (by omega : j-i ≤ 9)]

theorem pairRelativeTransferFunctional_convolutionPower (q : ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : ∀ j : ℕ, Integrable (fun t : ℝ => t^j) μ) (k : ℕ) :
    pairRelativeTransferFunctional q (measureMoment (convolutionPower μ k))=
      pairRelativeTransferFunctional q (spectralPowerMoment (measureMoment μ) k) := by
  unfold pairRelativeTransferFunctional
  apply Finset.sum_congr rfl
  intro i hi
  have hi5 : i ≤ 5 := by have := Finset.mem_range.mp hi; omega
  rw [measureMoment_convolutionPower_nine μ hμ k (by omega : i+2 ≤ 9),
    measureMoment_convolutionPower_nine μ hμ k (by omega : i+3 ≤ 9),
    measureMoment_convolutionPower_nine μ hμ k (by omega : i+4 ≤ 9)]

theorem mixedPower_pairRelative_bounds {q : ℝ} (hq : 3/2 ≤ q) (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ j : ℕ, Integrable (fun t : ℝ => t^j) μ)
    (hν : ∀ j : ℕ, Integrable (fun t : ℝ => t^j) ν)
    (hsμ : ∀ᵐ t ∂μ, (3:ℝ) ≤ t) (hsν : ∀ᵐ t ∂ν, (8:ℝ) ≤ t)
    {k : ℕ} (hk : 2 ≤ k) :
    0 ≤ pairRelativeTransferFunctional q (spectralPowerMoment (measureMoment (μ+ν)) k)-
      pairRelativeTransferFunctional q (spectralPowerMoment (measureMoment μ) k) ∧
    pairRelativeTransferFunctional q (spectralPowerMoment (measureMoment (μ+ν)) k)-
      pairRelativeTransferFunctional q (spectralPowerMoment (measureMoment μ) k) ≤
        pairRelativeLeadingCoefficient q*(spectralPowerMoment (measureMoment (μ+ν)) k 9-
          spectralPowerMoment (measureMoment μ) k 9) := by
  have hsum (j : ℕ) := (hμ j).add_measure (hν j)
  have hM : measureMoment (convolutionPower (μ+ν) k)=fun j =>
      measureMoment (convolutionPower μ k) j+measureMoment (mixedConvolutionRemainder μ ν k) j := by
    funext j
    rw [convolutionPower_add_split,measureMoment,integral_add_measure
      (integrable_pow_convolutionPower μ hμ k j) (integrable_pow_mixedConvolutionRemainder μ ν hμ hν k j)]
    rfl
  have hs := ae_lower_mixedConvolutionRemainder μ ν hsμ hsν k
  have h9 : ∀ᵐ t ∂mixedConvolutionRemainder μ ν k, (9:ℝ) ≤ t := by
    have hkr : (2:ℝ) ≤ k := by exact_mod_cast hk
    filter_upwards [hs] with t ht
    linarith
  have hi := integrable_pow_mixedConvolutionRemainder μ ν hμ hν k
  have hT : 0 ≤ pairRelativeTransferFunctional q (measureMoment (mixedConvolutionRemainder μ ν k)) ∧
      pairRelativeTransferFunctional q (measureMoment (mixedConvolutionRemainder μ ν k)) ≤
        pairRelativeLeadingCoefficient q*measureMoment (mixedConvolutionRemainder μ ν k) 9 := by
    rw [←integral_pairRelativeTransferKernel q _ hi]
    constructor
    · apply integral_nonneg_of_ae
      filter_upwards [h9] with t ht
      exact (pairRelativeTransferKernel_pos hq ht).le
    · rw [measureMoment,←integral_const_mul]
      apply integral_mono_ae (integrable_pairRelativeTransferKernel q _ hi) ((hi 9).const_mul _)
      filter_upwards [h9] with t ht
      exact (pairRelativeTransferKernel_lt_monomial hq ht).le
  rw [←pairRelativeTransferFunctional_convolutionPower q (μ+ν) hsum,
    ←pairRelativeTransferFunctional_convolutionPower q μ hμ,
    ←measureMoment_convolutionPower_nine (μ+ν) hsum k (by omega : 9 ≤ 9),
    ←measureMoment_convolutionPower_nine μ hμ k (by omega : 9 ≤ 9),hM,pairRelativeTransferFunctional_add]
  simpa only [add_sub_cancel_left] using hT

theorem sourceMixedPower_pairRelative_bounds {q : ℝ} (hq : 3/2 ≤ q) {k : ℕ} (hk : 2 ≤ k) :
    0 ≤ rawPairRelativeSector q k-pairRelativeTransferFunctional q (spectralPowerMoment (atomMoment 2 q) k) ∧
      rawPairRelativeSector q k-pairRelativeTransferFunctional q (spectralPowerMoment (atomMoment 2 q) k) ≤
        pairRelativeLeadingCoefficient q*
          (spectralPowerMoment (thetaCuspHigherLikelihoodSpectralMoment q) k 9-
            spectralPowerMoment (atomMoment 2 q) k 9) := by
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
  have h := mixedPower_pairRelative_bounds hq A D hiA hiD hsA hsD hk
  rw [hsum,hA] at h
  exact h

theorem pairRelativeTransferFunctional_congr_nine (q : ℝ) (m n : ℕ → ℝ)
    (he : ∀ j, j ≤ 9 → m j=n j) :
    pairRelativeTransferFunctional q m=pairRelativeTransferFunctional q n := by
  unfold pairRelativeTransferFunctional
  apply Finset.sum_congr rfl
  intro i hi
  have hi5 : i ≤ 5 := by have := Finset.mem_range.mp hi; omega
  rw [he (i+2) (by omega),he (i+3) (by omega),he (i+4) (by omega)]

theorem pairRelativeTransferFunctional_power_one (q : ℝ) (m : ℕ → ℝ) :
    pairRelativeTransferFunctional q (spectralPowerMoment m 1)=pairRelativeTransferFunctional q m :=
  pairRelativeTransferFunctional_congr_nine q _ _ (fun _ hj => spectralPowerMoment_one_nine m hj)

theorem pairRelativeTransferFunctional_power_two (q : ℝ) (m : ℕ → ℝ) :
    pairRelativeTransferFunctional q (spectralPowerMoment m 2)=
      pairRelativeTransferFunctional q (momentConvolution m m) := by
  apply pairRelativeTransferFunctional_congr_nine
  intro j hj
  rw [show 2=1+1 by omega,spectralPowerMoment_succ_nine m 1 hj]
  unfold momentConvolution
  apply Finset.sum_congr rfl
  intro i hi
  rw [spectralPowerMoment_one_nine m (by omega : j-i ≤ 9)]

theorem momentConvolution_comm_nine (m n : ℕ → ℝ) {j : ℕ} (hj : j ≤ 9) :
    momentConvolution m n j=momentConvolution n m j := by
  interval_cases j <;> norm_num [momentConvolution,Finset.sum_range_succ,Nat.choose] <;> ring

theorem momentConvolution_add_left (a b c : ℕ → ℝ) :
    momentConvolution (fun j => a j+b j) c=
      fun j => momentConvolution a c j+momentConvolution b c j := by
  funext j
  unfold momentConvolution
  simp only [mul_add,add_mul,Finset.sum_add_distrib]

theorem rawPairRelativeSector_one_deep {q : ℝ} (hq : 0 < q) :
    rawPairRelativeSector q 1=pairRelativeTransferFunctional q (thetaCuspDeepTailMoment q) := by
  have he : thetaCuspHigherLikelihoodSpectralMoment q=fun j => atomMoment 2 q j+thetaCuspDeepTailMoment q j := by
    funext j
    exact fullMoment_eq_atom_add_deep hq j
  unfold rawPairRelativeSector
  rw [pairRelativeTransferFunctional_power_one,he,pairRelativeTransferFunctional_add,
    pairRelativeTransferFunctional_dominant_zero hq,zero_add]

theorem rawPairRelativeSector_two_split {q : ℝ} (hq : 0 < q) :
    rawPairRelativeSector q 2=
      2*pairRelativeTransferFunctional q (momentConvolution (atomMoment 2 q) (thetaCuspDeepTailMoment q))+
      pairRelativeTransferFunctional q (momentConvolution (thetaCuspDeepTailMoment q) (thetaCuspDeepTailMoment q)) := by
  have he : thetaCuspHigherLikelihoodSpectralMoment q=fun j => atomMoment 2 q j+thetaCuspDeepTailMoment q j := by
    funext j
    exact fullMoment_eq_atom_add_deep hq j
  have hc : pairRelativeTransferFunctional q (momentConvolution (thetaCuspDeepTailMoment q) (atomMoment 2 q))=
      pairRelativeTransferFunctional q (momentConvolution (atomMoment 2 q) (thetaCuspDeepTailMoment q)) :=
    pairRelativeTransferFunctional_congr_nine q _ _ (fun _ hj => momentConvolution_comm_nine _ _ hj)
  unfold rawPairRelativeSector
  rw [pairRelativeTransferFunctional_power_two,he,momentConvolution_add_left]
  simp_rw [momentConvolution_add_right,pairRelativeTransferFunctional_add]
  rw [pairRelativeTransferFunctional_dominant_pair_zero hq,hc]
  ring

theorem hasDerivAt_powerMoment_of_flow (m : ℝ → ℕ → ℝ) (q c : ℝ)
    (hm : ∀ j, j ≤ 8 → HasDerivAt (fun r => m r j) (c*m q j-m q (j+1)) q)
    (k : ℕ) {j : ℕ} (hj : j ≤ 8) :
    HasDerivAt (fun r => spectralPowerMoment (m r) k j)
      (c*(k:ℝ)*spectralPowerMoment (m q) k j-spectralPowerMoment (m q) k (j+1)) q := by
  induction k generalizing j with
  | zero =>
      have he : (fun r => spectralPowerMoment (m r) 0 j)=
          fun _ : ℝ => (j.factorial:ℝ)*PowerSeries.coeff j (1:PowerSeries ℝ) := by
        funext r
        simp only [spectralPowerMoment,pow_zero]
      rw [he]
      simpa [spectralPowerMoment,PowerSeries.coeff_one] using
        hasDerivAt_const q ((j.factorial:ℝ)*PowerSeries.coeff j (1:PowerSeries ℝ))
  | succ k ih =>
      have hs := HasDerivAt.fun_sum (u := Finset.range (j+1)) (fun i hi =>
        ((hm i (by have := Finset.mem_range.mp hi; omega)).mul
          (ih (j := j-i) (by omega))).const_mul (j.choose i:ℝ))
      have he : (fun r => spectralPowerMoment (m r) (k+1) j)=
          fun r => momentConvolution (m r)
            (spectralPowerMoment (m r) k) j := by
        funext r
        exact spectralPowerMoment_succ_nine _ k (by omega)
      rw [he]
      convert! hs using 1
      · funext r
        unfold momentConvolution
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Pi.mul_apply,mul_assoc]
      · rw [spectralPowerMoment_succ_nine (m q) k (by omega : j ≤ 9),
          spectralPowerMoment_succ_nine (m q) k (by omega : j+1 ≤ 9),
          ←momentConvolution_shift _ _ j hj]
        unfold momentConvolution
        simp only [Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        push_cast
        ring

theorem hasDerivAt_barePowerMoment {q : ℝ} (hq : 0 < q) (d : ℝ) (k : ℕ)
    {j : ℕ} (hj : j ≤ 8) :
    HasDerivAt (fun r => spectralPowerMoment (bareMoment r d) k j)
      (d*(k:ℝ)*spectralPowerMoment (bareMoment q d) k j-
        spectralPowerMoment (bareMoment q d) k (j+1)) q :=
  hasDerivAt_powerMoment_of_flow (fun r => bareMoment r d) q d
    (fun j hj => hasDerivAt_bareMoment hq d j hj) k hj

end
end RHTower.ThetaCuspDefect
