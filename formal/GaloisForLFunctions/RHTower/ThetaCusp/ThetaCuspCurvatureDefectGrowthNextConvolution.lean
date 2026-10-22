import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCurvatureDefectGrowthNextKernel
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCurvatureDefectGrowthWeightDerivative
/-!
# Actual convolution signs and moment flow for the next transfer

The ninth-order moment extension identifies the next kernel integral
with its finite source-sector functional. Every actual convolution
sector of order at least three is nonnegative in this operator.
The exact raw-sector derivative is also established from the actual
moment chain. Signed even-sector absorption remains a separate gap.
-/

namespace RHTower.ThetaCuspDefect
open scoped BigOperators
open MeasureTheory Filter Set Topology
noncomputable section

theorem spectralPowerMoment_succ_nine (m : ℕ → ℝ) (k : ℕ) {j : ℕ} (hj : j ≤ 9) :
    spectralPowerMoment m (k+1) j=momentConvolution m (spectralPowerMoment m k) j := by
  by_cases h8 : j ≤ 8
  · exact spectralPowerMoment_succ m k h8
  · have h9 : j=9 := by omega
    subst j
    unfold spectralPowerMoment momentConvolution
    rw [pow_succ',PowerSeries.coeff_mul]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [momentSeries,Finset.sum_range_succ,Nat.choose,Nat.factorial]
    ring

theorem momentConvolution_shift (m n : ℕ → ℝ) (j : ℕ) (hj : j ≤ 8) :
    momentConvolution (fun i => m (i+1)) n j+momentConvolution m (fun i => n (i+1)) j=
      momentConvolution m n (j+1) := by
  interval_cases j <;> norm_num [momentConvolution,Finset.sum_range_succ,Nat.choose] <;> ring

theorem hasDerivAt_sourcePowerMoment {q : ℝ} (hq : 0 < q) (k : ℕ) {j : ℕ} (hj : j ≤ 8) :
    HasDerivAt (fun r => spectralPowerMoment (thetaCuspHigherLikelihoodSpectralMoment r) k j)
      (-spectralPowerMoment (thetaCuspHigherLikelihoodSpectralMoment q) k (j+1)) q := by
  induction k generalizing j with
  | zero =>
      have he : (fun r => spectralPowerMoment (thetaCuspHigherLikelihoodSpectralMoment r) 0 j)=
          fun _ : ℝ => (j.factorial:ℝ)*PowerSeries.coeff j (1:PowerSeries ℝ) := by
        funext r
        simp only [spectralPowerMoment,pow_zero]
      rw [he]
      simpa [spectralPowerMoment,PowerSeries.coeff_one] using
        hasDerivAt_const q ((j.factorial:ℝ)*PowerSeries.coeff j (1:PowerSeries ℝ))
  | succ k ih =>
      have hs := HasDerivAt.fun_sum (u := Finset.range (j+1)) (fun i hi =>
        ((hasDerivAt_thetaCuspHigherLikelihoodSpectralMoment i hq).mul
          (ih (j := j-i) (by omega))).const_mul (j.choose i:ℝ))
      have he : (fun r => spectralPowerMoment (thetaCuspHigherLikelihoodSpectralMoment r) (k+1) j)=
          fun r => momentConvolution (thetaCuspHigherLikelihoodSpectralMoment r)
            (spectralPowerMoment (thetaCuspHigherLikelihoodSpectralMoment r) k) j := by
        funext r
        exact spectralPowerMoment_succ_nine _ k (by omega)
      rw [he]
      convert! hs using 1
      · funext r
        unfold momentConvolution
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Pi.mul_apply,mul_assoc]
      · rw [spectralPowerMoment_succ_nine _ k (by omega),←momentConvolution_shift _ _ j hj]
        unfold momentConvolution
        simp only [←Finset.sum_add_distrib,←Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring

def transferLowCoefficient (q : ℝ) (i : ℕ) : ℝ :=
  growthCoefficient q (i+2)*slopeNumerator q 3-q*growthCoefficientJet q (i+2)*growthNumerator q 3

def transferHighCoefficient (q : ℝ) (i : ℕ) : ℝ :=
  q*growthCoefficient q (i+2)*growthNumerator q 3

def transferLowCoefficientJet (q : ℝ) (i : ℕ) : ℝ :=
  growthCoefficientJet q (i+2)*slopeNumerator q 3+growthCoefficient q (i+2)*slopeNumeratorJet q 3-
    (growthCoefficientJet q (i+2)*growthNumerator q 3+
      q*growthCoefficientJetTwo q (i+2)*growthNumerator q 3+
      q*growthCoefficientJet q (i+2)*growthNumeratorJet q 3)

def transferHighCoefficientJet (q : ℝ) (i : ℕ) : ℝ :=
  growthCoefficient q (i+2)*growthNumerator q 3+q*growthCoefficientJet q (i+2)*growthNumerator q 3+
    q*growthCoefficient q (i+2)*growthNumeratorJet q 3

theorem hasDerivAt_transferLowCoefficient (q : ℝ) {i : ℕ} (hi : i ≤ 5) :
    HasDerivAt (fun r => transferLowCoefficient r i) (transferLowCoefficientJet q i) q := by
  exact (((hasDerivAt_growthCoefficient q (i+2) (by omega)).mul (hasDerivAt_slopeNumerator q 3)).sub
    (((hasDerivAt_id q).mul (hasDerivAt_growthCoefficientJet q (i+2) (by omega))).mul
      (hasDerivAt_growthNumerator q 3))).congr_deriv
      (by unfold transferLowCoefficientJet; simp only [Pi.mul_apply,id_eq,one_mul]; ring)

theorem hasDerivAt_transferHighCoefficient (q : ℝ) {i : ℕ} (hi : i ≤ 5) :
    HasDerivAt (fun r => transferHighCoefficient r i) (transferHighCoefficientJet q i) q := by
  exact (((hasDerivAt_id q).mul (hasDerivAt_growthCoefficient q (i+2) (by omega))).mul
    (hasDerivAt_growthNumerator q 3)).congr_deriv
    (by unfold transferHighCoefficientJet; simp only [Pi.mul_apply,id_eq,one_mul]; ring)

def transferFlowFunctional (q : ℝ) (m : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range 6,
    (transferLowCoefficientJet q i*m (i+2)+transferHighCoefficientJet q i*m (i+3)-
      transferLowCoefficient q i*m (i+3)-transferHighCoefficient q i*m (i+4))

theorem hasDerivAt_rawTransferSector {q : ℝ} (hq : 0 < q) (k : ℕ) :
    HasDerivAt (fun r => rawTransferSector r k)
      (transferFlowFunctional q (spectralPowerMoment (thetaCuspHigherLikelihoodSpectralMoment q) k)) q := by
  unfold rawTransferSector growthTransferFunctional transferFlowFunctional
  apply HasDerivAt.fun_sum
  intro i hi
  have hi5 : i ≤ 5 := by have := Finset.mem_range.mp hi; omega
  exact (((hasDerivAt_transferLowCoefficient q hi5).mul
    (hasDerivAt_sourcePowerMoment hq k (by omega : i+2 ≤ 8))).add
    ((hasDerivAt_transferHighCoefficient q hi5).mul
      (hasDerivAt_sourcePowerMoment hq k (by omega : i+3 ≤ 8)))).congr_deriv
      (by norm_num only [Nat.add_assoc,Nat.reduceAdd]; ring)

def pairRelativeTransferFunctional (q : ℝ) (m : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range 6,
    ((((q*dominantPairPolynomialJet q-(6*q+9)*dominantPairPolynomial q)*transferLowCoefficient q i-
      q*dominantPairPolynomial q*transferLowCoefficientJet q i)*m (i+2)+
    (q*dominantPairPolynomial q*transferLowCoefficient q i+
      (q*dominantPairPolynomialJet q-(6*q+9)*dominantPairPolynomial q)*transferHighCoefficient q i-
      q*dominantPairPolynomial q*transferHighCoefficientJet q i)*m (i+3))+
    q*dominantPairPolynomial q*transferHighCoefficient q i*m (i+4))

theorem pairRelativeTransferFunctional_flow (q : ℝ) (m : ℕ → ℝ) :
    pairRelativeTransferFunctional q m=
      -q*dominantPairPolynomial q*transferFlowFunctional q m+
        (q*dominantPairPolynomialJet q-(6*q+9)*dominantPairPolynomial q)*growthTransferFunctional q m := by
  unfold pairRelativeTransferFunctional transferFlowFunctional growthTransferFunctional
  simp only [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  unfold transferLowCoefficient transferHighCoefficient
  ring

theorem pairRelativeTransferFunctional_point (q t : ℝ) :
    pairRelativeTransferFunctional q (fun j => t^j)=pairRelativeTransferKernel q t := by
  rw [pairRelativeTransferFunctional_flow,growthTransferFunctional_point]
  unfold transferFlowFunctional pairRelativeTransferKernel growthTransferKernelJet
    growthTransferKernel growthScore growthScoreJet growthScoreJetTwo
  simp only [Finset.sum_mul,Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  unfold transferLowCoefficient transferHighCoefficient transferLowCoefficientJet transferHighCoefficientJet
  rw [show i+3=(i+2)+1 by omega,show i+4=(i+2)+2 by omega,pow_add]
  ring

theorem measureMoment_sourceConvolutionMeasure_nine {q : ℝ} (hq : 0 < q) (k : ℕ)
    {j : ℕ} (hj : j ≤ 9) :
    measureMoment (sourceConvolutionMeasure q k) j=
      spectralPowerMoment (thetaCuspHigherLikelihoodSpectralMoment q) k j := by
  letI := thetaCuspHigherLikelihoodTiltedMeasure_finite hq
  induction k generalizing j with
  | zero =>
      by_cases hj0 : j=0
      · subst j; norm_num [sourceConvolutionMeasure,measureMoment,spectralPowerMoment]
      · simp [sourceConvolutionMeasure,measureMoment,spectralPowerMoment,PowerSeries.coeff_one,hj0]
  | succ k ih =>
      letI := sourceConvolutionMeasure_finite hq k
      rw [sourceConvolutionMeasure,measureMoment_conv _ _
        (fun i => integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure i hq)
        (integrable_pow_sourceConvolutionMeasure hq k),spectralPowerMoment_succ_nine _ k hj]
      unfold momentConvolution
      apply Finset.sum_congr rfl
      intro i hi
      rw [ih (by omega : j-i ≤ 9)]
      rfl

theorem integral_pairRelativeTransferKernel (q : ℝ) (μ : Measure ℝ)
    (hμ : ∀ j : ℕ, Integrable (fun t : ℝ => t^j) μ) :
    (∫ t : ℝ, pairRelativeTransferKernel q t ∂μ)=pairRelativeTransferFunctional q (measureMoment μ) := by
  simp_rw [←pairRelativeTransferFunctional_point]
  unfold pairRelativeTransferFunctional
  erw [integral_finsetSum (Finset.range 6) (fun i _ =>
    (((hμ (i+2)).const_mul _).add ((hμ (i+3)).const_mul _)).add ((hμ (i+4)).const_mul _))]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Pi.add_apply]
  erw [integral_add (((hμ (i+2)).const_mul _).add ((hμ (i+3)).const_mul _)) ((hμ (i+4)).const_mul _),
    integral_add ((hμ (i+2)).const_mul _) ((hμ (i+3)).const_mul _)]
  simp only [integral_const_mul,measureMoment]

theorem integral_pairRelativeTransferKernel_source {q : ℝ} (hq : 0 < q) (k : ℕ) :
    (∫ t : ℝ, pairRelativeTransferKernel q t ∂sourceConvolutionMeasure q k)=
      pairRelativeTransferFunctional q (spectralPowerMoment (thetaCuspHigherLikelihoodSpectralMoment q) k) := by
  rw [integral_pairRelativeTransferKernel q _ (integrable_pow_sourceConvolutionMeasure hq k)]
  unfold pairRelativeTransferFunctional
  apply Finset.sum_congr rfl
  intro i hi
  have hi5 : i ≤ 5 := by have := Finset.mem_range.mp hi; omega
  rw [measureMoment_sourceConvolutionMeasure_nine hq k (by omega : i+2 ≤ 9),
    measureMoment_sourceConvolutionMeasure_nine hq k (by omega : i+3 ≤ 9),
    measureMoment_sourceConvolutionMeasure_nine hq k (by omega : i+4 ≤ 9)]

theorem sourceConvolution_pairRelativeTransfer_nonneg {q : ℝ} (hq : 3/2 ≤ q) {k : ℕ} (hk : 3 ≤ k) :
    0 ≤ pairRelativeTransferFunctional q (spectralPowerMoment (thetaCuspHigherLikelihoodSpectralMoment q) k) := by
  have hq0 : 0 < q := by linarith
  rw [←integral_pairRelativeTransferKernel_source hq0 k]
  apply integral_nonneg_of_ae
  filter_upwards [ae_lower_sourceConvolutionMeasure hq0 k] with t ht
  have hkr : (3:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  exact (pairRelativeTransferKernel_pos hq (by linarith)).le

end
end RHTower.ThetaCuspDefect
