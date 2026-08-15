import GaloisForLFunctions.RHTower.BakerGeneralProof.PolynomialAuxiliaryArithmetic
import GaloisForLFunctions.RHTower.BakerProof.AuxiliaryExtrapolation

/-!
# One-step extrapolation for full Baker component jets

The full polynomial--exponential auxiliary function has the initial analytic-order box supplied
by its integral Siegel kernel.  This module combines that order bound with the generic multipoint
Schwarz theorem and the exact algebraic-integer representative of a later jet.  Thus one strict,
explicit real inequality promotes the later analytic value to an exact algebraic zero.
-/

open scoped Classical
open BigOperators NumberField

namespace GaloisForLFunctions.RHTower.BakerGeneralProof

/-- One exact full-jet extrapolation step.  Boundary estimates and the final strict numerical
inequality are intentionally parameters here; later quantitative modules discharge them. -/
theorem SolvedRelation.polynomialComponentJetAuxiliaryFunction_eq_zero_one_step_extrapolation
    (R : SolvedRelation) (c d : ℤ) (hc : c ≠ 0)
    (hcomp : ∀ dir, IsIntegral ℤ (R.scaledComponentCoeff c dir))
    (hbase : ∀ i, IsIntegral ℤ (R.scaledBase d i))
    {U V S T : ℕ} (eta : R.AuxiliaryColumn U V → 𝓞 R.CoefficientField)
    (hker : Matrix.mulVec (R.polynomialAuxiliaryMatrix c d hcomp hbase U V S T) eta = 0)
    (hd : d ≠ 0) (nu : R.Direction → ℕ) (q : ℕ)
    (hnuq : ∀ dir, nu dir + q ≤ T)
    {radius M D : ℝ} (hradius : 0 < radius) (hD : 0 < D)
    (hboundary_component : ∀ w ∈ Metric.sphere 0 radius,
      ‖R.polynomialComponentJetAuxiliaryFunction c nu eta w‖ ≤ M)
    (hboundary_factor : ∀ w ∈ Metric.sphere 0 radius,
      D ≤ ‖∏ z ∈ BakerProof.initialSamplePoints S, (w - z) ^ q‖)
    (sample : ℕ) (hsample : (sample : ℂ) ∈ Metric.closedBall 0 radius)
    (hsmall :
      (‖(d : ℂ) ^ (sample * (R.n * V))‖ *
        (‖∏ z ∈ BakerProof.initialSamplePoints S, ((sample : ℂ) - z) ^ q‖ * (M / D))) *
        house ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField)
          (R.polynomialComponentJetInteger c d hcomp hbase nu eta sample)) ^
          (Module.finrank ℚ R.CoefficientField - 1) < 1) :
    R.polynomialComponentJetAuxiliaryFunction c nu eta (sample : ℂ) = 0 := by
  have horder : ∀ z ∈ BakerProof.initialSamplePoints S,
      q ≤ analyticOrderAt (R.polynomialComponentJetAuxiliaryFunction c nu eta) z := by
    intro z hz
    obtain ⟨s, rfl⟩ := BakerProof.mem_initialSamplePoints.mp hz
    exact R.polynomialComponentJetAuxiliaryFunction_analyticOrderAt_ge
      c d hc hcomp hbase eta hker hd s nu q hnuq
  have hf : ∀ z, AnalyticAt ℂ (R.polynomialComponentJetAuxiliaryFunction c nu eta) z := by
    intro z
    exact R.analyticAt_polynomialComponentJetAuxiliaryFunction c nu eta z
  have hnorm := BakerProof.multipoint_schwarz_bound
    (R.polynomialComponentJetAuxiliaryFunction c nu eta) hf
    (BakerProof.initialSamplePoints S) q horder
    hradius hD hboundary_component hboundary_factor hsample
  apply R.polynomialComponentJetAuxiliaryFunction_eq_zero_of_distinguished_mul_house_pow_lt_one
    c d hcomp hbase nu eta sample hd
  apply lt_of_le_of_lt _ hsmall
  apply mul_le_mul_of_nonneg_right _
    (pow_nonneg (house_nonneg _) _)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)

end GaloisForLFunctions.RHTower.BakerGeneralProof
