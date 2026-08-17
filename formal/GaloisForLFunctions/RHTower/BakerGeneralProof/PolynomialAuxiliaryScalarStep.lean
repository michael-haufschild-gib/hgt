import GaloisForLFunctions.RHTower.BakerGeneralProof.PolynomialAuxiliaryScalarBounds
import GaloisForLFunctions.RHTower.BakerGeneralProof.PolynomialAuxiliaryExtrapolation

/-!
# Scalar one-step extrapolation for full Baker component jets

The generic extrapolation step consumes a boundary bound, a node-polynomial lower bound, and a
conjugate bound.  Each is replaced here by its closed scalar majorant, so a single inequality
between explicit powers of the construction parameters produces an exact new zero of the component
jet at a later natural sample.
-/

open scoped Classical
open BigOperators NumberField

namespace GaloisForLFunctions.RHTower.BakerGeneralProof

/-- One exact extrapolation step for a full component jet, with every analytic and conjugate
quantity replaced by its closed scalar majorant. -/
theorem SolvedRelation.polynomialComponentJetAuxiliaryFunction_eq_zero_one_step_scalar
    (R : SolvedRelation) (c d : ℤ) (hc : c ≠ 0)
    (hcomp : ∀ dir, IsIntegral ℤ (R.scaledComponentCoeff c dir))
    (hbase : ∀ i, IsIntegral ℤ (R.scaledBase d i))
    {U V S T : ℕ} (hU : 1 ≤ U)
    (eta : R.AuxiliaryColumn U V → 𝓞 R.CoefficientField)
    (hker : Matrix.mulVec (R.polynomialAuxiliaryMatrix c d hcomp hbase U V S T) eta = 0)
    (hd : d ≠ 0) (nu : R.Direction → ℕ) (q : ℕ) (hnuq : ∀ dir, nu dir + q ≤ T)
    {Heta : ℝ} (hHeta : 0 ≤ Heta)
    (hEta : ∀ col, house ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (eta col)) ≤
      Heta)
    {radius : ℝ} (hradius1 : 1 ≤ radius) (hradiusS : (S : ℝ) < radius)
    (sample : ℕ) (hsample : (sample : ℝ) ≤ radius)
    (hsmall :
      (|(d : ℝ)| ^ (sample * (R.n * V)) *
        (((sample + S : ℕ) : ℝ) ^ (q * S) *
          (R.jetScalarBound c U V nu Heta radius / (radius - S) ^ (q * S)))) *
        R.jetHouseScalarBound c d U V nu Heta sample ^
          (Module.finrank ℚ R.CoefficientField - 1) < 1) :
    R.polynomialComponentJetAuxiliaryFunction c nu eta (sample : ℂ) = 0 := by
  have hrad0 : (0 : ℝ) < radius := lt_of_lt_of_le zero_lt_one hradius1
  have hden : (0 : ℝ) < (radius - S) ^ (q * S) := pow_pos (sub_pos.mpr hradiusS) _
  have hA0 : 0 ≤ R.jetAnalyticBound c nu eta radius :=
    R.jetAnalyticBound_nonneg c nu eta hrad0.le
  have hA := R.jetAnalyticBound_le_scalar c hU nu eta hradius1 hHeta hEta
  have hH := R.polynomialComponentJetHouseBound_le_scalar c d hU nu eta sample hHeta hEta
  have hH0 := R.polynomialComponentJetHouseBound_nonneg c d nu eta sample
  apply R.polynomialComponentJetAuxiliaryFunction_eq_zero_one_step_extrapolation
    c d hc hcomp hbase eta hker hd nu q hnuq
    (radius := radius) (M := R.jetAnalyticBound c nu eta radius)
    (D := (radius - S) ^ (q * S)) hrad0 hden
  · intro w hw
    apply R.norm_polynomialComponentJetAuxiliaryFunction_le
    simp only [mem_sphere_iff_norm] at hw
    exact le_of_eq (by simpa using hw)
  · exact BakerProof.initialSamplePoints_boundary_factor_lower hradiusS
  · simpa [Metric.mem_closedBall, Complex.dist_eq] using hsample
  · refine lt_of_le_of_lt ?_ hsmall
    have hnode : ‖∏ z ∈ BakerProof.initialSamplePoints S, ((sample : ℂ) - z) ^ q‖ ≤
        ((sample + S : ℕ) : ℝ) ^ (q * S) :=
      BakerProof.initialSamplePoints_sample_factor_upper S q sample
    have hnodenn : (0 : ℝ) ≤ ‖∏ z ∈ BakerProof.initialSamplePoints S, ((sample : ℂ) - z) ^ q‖ :=
      norm_nonneg _
    have hdnorm : ‖(d : ℂ) ^ (sample * (R.n * V))‖ = |(d : ℝ)| ^ (sample * (R.n * V)) := by
      rw [norm_pow]
      congr 1
      simp
    have hpow : house ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField)
        (R.polynomialComponentJetInteger c d hcomp hbase nu eta sample)) ^
          (Module.finrank ℚ R.CoefficientField - 1) ≤
        R.jetHouseScalarBound c d U V nu Heta sample ^
          (Module.finrank ℚ R.CoefficientField - 1) := by
      refine pow_le_pow_left₀ (house_nonneg _) ?_ _
      exact le_trans
        (R.polynomialComponentJetInteger_house_le c d hcomp hbase nu eta sample) hH
    have hleft : ‖(d : ℂ) ^ (sample * (R.n * V))‖ *
        (‖∏ z ∈ BakerProof.initialSamplePoints S, ((sample : ℂ) - z) ^ q‖ *
          (R.jetAnalyticBound c nu eta radius / (radius - S) ^ (q * S))) ≤
        |(d : ℝ)| ^ (sample * (R.n * V)) *
          (((sample + S : ℕ) : ℝ) ^ (q * S) *
            (R.jetScalarBound c U V nu Heta radius / (radius - S) ^ (q * S))) := by
      rw [hdnorm]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine mul_le_mul hnode ?_ (div_nonneg hA0 hden.le) (by positivity)
      exact div_le_div_of_nonneg_right hA hden.le
    refine mul_le_mul hleft hpow (pow_nonneg (house_nonneg _) _) ?_
    refine mul_nonneg (by positivity) (mul_nonneg (by positivity) ?_)
    exact div_nonneg (hA0.trans hA) hden.le

end GaloisForLFunctions.RHTower.BakerGeneralProof
