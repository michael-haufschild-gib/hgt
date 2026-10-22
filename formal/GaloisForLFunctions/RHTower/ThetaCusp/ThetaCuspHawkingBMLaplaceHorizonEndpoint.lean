import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLaplaceGaussFactors
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSecondHarmonicGaussSquareRootEndpoint

/-! Actual horizon solution's AdS value and derivative edge at independent frequency. -/

open Complex Set Filter Topology
namespace RHTower.D4BMLaplaceRadial
noncomputable section

attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- The convergent horizon series has its actual Gamma-normalized boundary
value, with frequency and angular momentum independent. -/
theorem horizonFactor_boundary {w chi : ℂ} (h : Chamber w chi) :
    Tendsto (fun z : ℝ => gaussFactor w chi false z) (𝓝[<] (1:ℝ)) (𝓝 (connection w chi)) := by
  obtain ⟨ha,hb,hc,hca,hcb⟩ := chamber_parameters h
  have ha' := avoidsNegNat_of_re_pos ha
  have hb' := avoidsNegNat_of_re_pos hb
  have hc' := avoidsNegNat_of_re_pos hc
  have hg : 0 < (gaussC w-gaussA w chi-gaussB w chi).re := by rw [gauss_gap]; norm_num
  have hs := gaussSummation _ _ _ ha' hb' hc'
    (avoidsNegNat_of_re_pos hca) (avoidsNegNat_of_re_pos hcb) hg
  rw [GaussSummationFormula,gauss_gap] at hs
  have ht := tendsto_tsum_ordinaryHypergeometricCoefficient_mul_pow_one _ _ _ ha' hb' hc' hg
  rw [hs] at ht
  simpa [gaussFactor,radialSeries,horizonSeries,ordinaryHypergeometric_sum_eq,smul_eq_mul,connection] using ht

/-- The horizon derivative has a controlled square-root edge. This actual
derivative limit fixes the endpoint Wronskian without assuming connection data. -/
theorem horizonFirst_boundary {w chi : ℂ} (h : Chamber w chi) :
    Tendsto (fun z : ℝ => (Real.sqrt (1-z):ℂ)*gaussFirst w chi false z)
      (𝓝[Ico (0:ℝ) 1] (1:ℝ))
      (𝓝 ((Real.sqrt Real.pi:ℂ)*(Complex.Gamma (gaussC w)/
        (Complex.Gamma (gaussA w chi)*Complex.Gamma (gaussB w chi))))) := by
  let a := gaussA w chi
  let b := gaussB w chi
  let c := gaussC w
  let u : ℕ → ℂ := fun n => ((n+1:ℕ):ℂ)*ordinaryHypergeometricCoefficient a b c (n+1)
  let L := Complex.Gamma c/(Complex.Gamma a*Complex.Gamma b)
  obtain ⟨ha,hb,hc,-⟩ := chamber_parameters h
  have ht : Tendsto (fun n : ℕ => (Real.sqrt n:ℂ)*u n) atTop (𝓝 L) := by
    simpa only [u,L,mul_assoc] using tendsto_sqrtNat_mul_shifted_ordinaryHypergeometricCoefficient_of_gap_half
      a b c (avoidsNegNat_of_re_pos ha) (avoidsNegNat_of_re_pos hb)
      (avoidsNegNat_of_re_pos hc) (gauss_gap w chi)
  have hr : (ordinaryHypergeometricSeries ℂ a b c).radius=1 := horizonSeries_radius h
  have hs (z : ℝ) (hz : z ∈ Ico (0:ℝ) 1) :
      HasSum (fun n => u n*(z:ℂ)^n) (gaussFirst w chi false z) := by
    have hnorm : ‖(z:ℂ)‖ₑ < 1 := by
      rw [← ofReal_norm,Complex.norm_real,Real.norm_of_nonneg hz.1]
      exact ENNReal.ofReal_lt_one.mpr hz.2
    have hh := (ordinaryHypergeometric_hasSum_value_first_second a b c z (by rw [hr]; exact hnorm)).2.1
    simpa [u,gaussFirst,radialSeries,horizonSeries,ordinaryHypergeometricFirstDerivativeSeriesValue,
      a,b,c,ordinaryHypergeometricFormalCoefficient] using hh
  have hab := tendsto_sqrt_one_sub_mul_tsum_of_sqrtNat_mul_complex ht (fun z hz => (hs z hz).summable)
  apply hab.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [(hs z hz).tsum_eq]

end
end RHTower.D4BMLaplaceRadial
