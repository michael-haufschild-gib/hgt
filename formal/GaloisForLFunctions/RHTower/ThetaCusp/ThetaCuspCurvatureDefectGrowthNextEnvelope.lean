import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCurvatureDefectGrowthNextEnvelopePolynomial
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCurvatureDefectGrowthNextConvolution
/-! Exact ninth-moment envelope for the pair-relative source transfer,
with integral transport to every stable component and source sector. -/

namespace RHTower.ThetaCuspDefect
open scoped BigOperators
open MeasureTheory Filter Set
noncomputable section

def pairRelativeLeadingCoefficient (q : ℝ) : ℝ :=
  q*dominantPairPolynomial q*growthTransferLeadingCoefficient q

theorem pairRelativeLeadingCoefficient_pos {q : ℝ} (hq : 3/2 ≤ q) :
    0 < pairRelativeLeadingCoefficient q := by
  have hq0 : 0 < q := by linarith
  exact mul_pos (mul_pos hq0 (dominantPairPolynomial_pos hq)) (growthTransferLeadingCoefficient_pos hq)

theorem shiftedTransferCoeff_eight (q : ℝ) :
    shiftedTransferCoeff q 8=growthTransferLeadingCoefficient q := by
  norm_num [shiftedTransferCoeff,growthTransferLeadingCoefficient,Finset.sum_range_succ,Nat.choose]

theorem pairRelativeShiftCoeff_nine (y : ℝ) :
    pairRelativeShiftCoeff 9 y=pairRelativeLeadingCoefficient (3/2+y) := by
  unfold pairRelativeShiftCoeff
  norm_num only [Nat.reduceSub,OfNat.zero_ne_ofNat,ite_false,
    pairKernelShiftValue_nine,pairKernelShiftJet_nine,mul_zero,zero_mul,add_zero,sub_zero]
  rw [←dominantPairPolynomial_gap_shift_eq y,←shiftedTransferCoeff_shift_8 y,shiftedTransferCoeff_eight]
  rfl

theorem pairRelativeTransferKernel_monomial_difference (y v : ℝ) :
    pairRelativeLeadingCoefficient (3/2+y)*(9+v)^9-pairRelativeTransferKernel (3/2+y) (9+v)=
      ∑ k ∈ Finset.range 9, pairRelativeMonomialReserve k y*v^k := by
  rw [pairRelativeTransferKernel_shift_expansion,←pairRelativeShiftCoeff_nine y]
  unfold pairRelativeMonomialReserve
  norm_num [Finset.sum_range_succ,Nat.choose]
  ring

theorem pairRelativeTransferKernel_lt_monomial {q t : ℝ} (hq : 3/2 ≤ q) (ht : 9 ≤ t) :
    pairRelativeTransferKernel q t < pairRelativeLeadingCoefficient q*t^9 := by
  have hy : 0 ≤ q-3/2 := by linarith
  have hv : 0 ≤ t-9 := by linarith
  have hs : 0 < ∑ k ∈ Finset.range 9, pairRelativeMonomialReserve k (q-3/2)*(t-9)^k := by
    apply Finset.sum_pos'
    · intro k hk
      exact mul_nonneg (pairRelativeMonomialReserve_pos _ hy k
        (by have := Finset.mem_range.mp hk; omega)).le (pow_nonneg hv k)
    · exact ⟨0,by simp,by simpa using pairRelativeMonomialReserve_pos _ hy 0 (by omega)⟩
  rw [←pairRelativeTransferKernel_monomial_difference,
    show (3/2:ℝ)+(q-3/2)=q by ring,show (9:ℝ)+(t-9)=t by ring] at hs
  exact sub_pos.mp hs

theorem integrable_pairRelativeTransferKernel (q : ℝ) (μ : Measure ℝ)
    (hμ : ∀ j : ℕ, Integrable (fun t : ℝ => t^j) μ) :
    Integrable (fun t => pairRelativeTransferKernel q t) μ := by
  simp_rw [←pairRelativeTransferFunctional_point]
  unfold pairRelativeTransferFunctional
  exact integrable_finsetSum (Finset.range 6) (fun i _ =>
    (((hμ (i+2)).const_mul _).add ((hμ (i+3)).const_mul _)).add ((hμ (i+4)).const_mul _))

theorem component_pairRelativeTransfer_upper {q : ℝ} (hq : 3/2 ≤ q) (μ : Measure ℝ)
    (hμ : ∀ j : ℕ, Integrable (fun t : ℝ => t^j) μ)
    (hs : ∀ᵐ t ∂μ, 9 ≤ t) :
    pairRelativeTransferFunctional q (measureMoment μ) ≤ pairRelativeLeadingCoefficient q*measureMoment μ 9 := by
  rw [←integral_pairRelativeTransferKernel q μ hμ]
  calc
    _ ≤ ∫ t : ℝ, pairRelativeLeadingCoefficient q*t^9 ∂μ := by
      apply integral_mono_ae (integrable_pairRelativeTransferKernel q μ hμ) ((hμ 9).const_mul _)
      filter_upwards [hs] with t ht
      exact (pairRelativeTransferKernel_lt_monomial hq ht).le
    _ = _ := by simp only [integral_const_mul,measureMoment]

theorem sourceConvolution_pairRelativeTransfer_upper {q : ℝ} (hq : 3/2 ≤ q)
    {k : ℕ} (hk : 3 ≤ k) :
    pairRelativeTransferFunctional q (spectralPowerMoment (thetaCuspHigherLikelihoodSpectralMoment q) k) ≤
      pairRelativeLeadingCoefficient q*spectralPowerMoment (thetaCuspHigherLikelihoodSpectralMoment q) k 9 := by
  have hq0 : 0 < q := by linarith
  have hs : ∀ᵐ t ∂sourceConvolutionMeasure q k, 9 ≤ t := by
    filter_upwards [ae_lower_sourceConvolutionMeasure hq0 k] with t ht
    have hkr : (3:ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have h := component_pairRelativeTransfer_upper hq (sourceConvolutionMeasure q k)
    (integrable_pow_sourceConvolutionMeasure hq0 k) hs
  rw [←integral_pairRelativeTransferKernel q _ (integrable_pow_sourceConvolutionMeasure hq0 k),
    integral_pairRelativeTransferKernel_source hq0 k,
    measureMoment_sourceConvolutionMeasure_nine hq0 k (by omega : 9 ≤ 9)] at h
  exact h

end
end RHTower.ThetaCuspDefect
