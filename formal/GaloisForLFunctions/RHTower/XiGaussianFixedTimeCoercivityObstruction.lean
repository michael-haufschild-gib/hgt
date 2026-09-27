import GaloisForLFunctions.RHTower.XiGaussianAnnihilatorMass
import GaloisForLFunctions.RHTower.XiGaussianNativeMassScale
import GaloisForLFunctions.RHTower.XiScaledEvenGaussianEnergy

/-!
# No all-degree Gaussian-norm floor at a fixed positive heat time

This is an obstruction to continuous-norm coercivity, not to positivity of
the signed Hankel forms. The annihilators leave nonzero continuous mass while
their full positive sampled energy vanishes. Exact scaling transfers this
failure to the Gaussian norm used in the channel estimates.
-/

open Complex MeasureTheory GaloisForLFunctions
open scoped Real SchwartzMap NNReal
noncomputable section

namespace RHTower

/-- Exact native/scaled energy bridge for the whole polynomial. -/
theorem xiScaledEvenGaussianEnergy_unscale (Q : Polynomial ℝ)
    (r : {r : ℝ // 0 < r}) :
    xiScaledEvenGaussianEnergy (xiGaussianUnscalePolynomial Q r) r =
      ∑' q : XiZeroCopy, ‖xiPolynomialGaussianHeatTerm Q (xiGaussianScaleHeat r) q‖ := by
  unfold xiScaledEvenGaussianEnergy
  apply tsum_congr
  intro q
  rw [← norm_pow, xiScaledEvenGaussianAmplitude_sq,
    xiGaussianUnscalePolynomial_comp_scale]
  rfl

/-- Every fixed positive scale admits arbitrarily bad continuous-norm ratios. -/
theorem not_exists_xiScaledEvenGaussian_uniform_norm_floor
    (r : {r : ℝ // 0 < r}) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ P : Polynomial ℝ,
      c * ‖(polyGaussSchwartz (evenSquarePolynomial P)).toLp 2
        (volume : Measure ℝ)‖ ^ 2 ≤ xiScaledEvenGaussianEnergy P r := by
  rintro ⟨c, hc, hfloor⟩
  apply not_exists_xiGaussian_uniform_mass_floor (xiGaussianScaleHeat r)
  refine ⟨c * (r : ℝ), mul_pos hc r.property, fun Q => ?_⟩
  let P := xiGaussianUnscalePolynomial Q r
  have hm := routeUPolynomialGaussianMass_scale P r
  rw [xiGaussianUnscalePolynomial_comp_scale] at hm
  have hnorm : ‖(polyGaussSchwartz (evenSquarePolynomial P)).toLp 2
      (volume : Measure ℝ)‖ ^ 2 =
        (r : ℝ) * routeUPolynomialGaussianMass Q (xiGaussianScaleHeat r) := by
    rw [hm, ← mul_assoc, mul_inv_cancel₀ r.property.ne', one_mul]
  have h := hfloor P
  rw [hnorm, xiScaledEvenGaussianEnergy_unscale] at h
  simpa only [mul_assoc] using h

end RHTower
