import GaloisForLFunctions.RHTower.PrimeArchConjugatePairQuadraticConcentration
import GaloisForLFunctions.RHTower.RouteRResolutionCoreNoetherCharge

/-!
# Xi Noether--concentration quantization

An off-line Xi divisor carries two independently constructed defects:

* a source Noether orientation charge calibrated by its completion-core radius;
* a conjugate-pair Poisson profile whose signed mass vanishes but whose quadratic energy is positive.

At a fixed relative probe scale, their product is independent of zero height and horizontal
displacement.  It is quantized only by divisor multiplicity.  Thus source completion charge and
analytic concentration are quantitatively calibrated, rather than merely sharing an RH zero locus.

This is an unconditional bridge, not an RH proof: it measures a hypothetical off-line defect but
does not supply an arithmetic law excluding one.
-/

open Complex Filter MeasureTheory Topology

namespace RHTower

noncomputable section

/-- **Scale-normalized concentration action.**  At relative probe height `lambda`, quadratic
concentration energy scales exactly as the inverse transverse radius.  Multiplication by the
radius leaves the universal action `π lambda² / (1 - lambda²)`. -/
theorem scaleNormalized_integral_sq_lineConjugateCauchyConcentrationProfile
    {b lambda : ℝ} (hb : 0 < b) (hlambda : 0 < lambda) (hlambda_one : lambda < 1) :
    b * (∫ t : ℝ,
      lineConjugateCauchyConcentrationProfile b (lambda * b) t ^ 2) =
      Real.pi * lambda ^ 2 / (1 - lambda ^ 2) := by
  have hy : 0 < lambda * b := mul_pos hlambda hb
  have hyb : lambda * b < b := by nlinarith
  rw [integral_sq_lineConjugateCauchyConcentrationProfile hy hyb]
  have hbne : b ≠ 0 := ne_of_gt hb
  have hlambda_sq : 1 - lambda ^ 2 ≠ 0 := by nlinarith
  field_simp [hbne, hlambda_sq]

/-- **Xi Noether--concentration quantization.**  For one off-line Xi divisor copy, absolute
source Noether charge times conjugate-pair quadratic concentration energy at any fixed relative
probe scale is a universal multiplicity quantum.  Zero height and horizontal displacement cancel
exactly from the product. -/
theorem abs_routeRPrimeGammaXiNoetherOrientationCharge_mul_concentrationEnergy_eq
    (rho : XiDivisorSupport) {lambda : ℝ}
    (hoff : (rho : ℂ).re ≠ 1 / 2)
    (hlambda : 0 < lambda) (hlambda_one : lambda < 1) :
    let b := routeRPrimeGammaXiResolutionCoreRadius rho
    let m := (analyticOrderAt xi (rho : ℂ)).toNat
    |routeRPrimeGammaXiNoetherOrientationCharge rho| *
        (∫ t : ℝ,
          lineConjugateCauchyConcentrationProfile b (lambda * b) t ^ 2) =
      (m : ℝ) * Real.pi * lambda ^ 2 / (2 * (1 - lambda ^ 2)) := by
  dsimp only
  have hbne : routeRPrimeGammaXiResolutionCoreRadius rho ≠ 0 := by
    intro hb
    exact hoff ((routeRPrimeGammaXiResolutionCoreRadius_eq_zero_iff rho).mp hb)
  have hb : 0 < routeRPrimeGammaXiResolutionCoreRadius rho := by
    rw [routeRPrimeGammaXiResolutionCoreRadius]
    exact abs_pos.mpr (by
      intro h
      apply hoff
      linarith)
  rw [abs_routeRPrimeGammaXiNoetherOrientationCharge_eq]
  have hscale :=
    scaleNormalized_integral_sq_lineConjugateCauchyConcentrationProfile
      hb hlambda hlambda_one
  have hlambda_sq : 1 - lambda ^ 2 ≠ 0 := by nlinarith
  field_simp [hbne, hlambda_sq] at hscale ⊢
  nlinarith [hscale]

end

end RHTower
