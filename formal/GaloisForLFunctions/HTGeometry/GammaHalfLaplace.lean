import Mathlib.Probability.Distributions.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The Gamma-half Laplace law

This module records the exact half-line probability law selected by a square-root pole.  The
unit-rate Gamma law of shape `1 / 2` has Laplace transform `(1 + u) ^ (-1 / 2)`.  This is the
continuous target for Hausdorff-moment compactifications of nonnegative Dirichlet coefficients
whose generating series has a square-root singularity.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The unit-rate Gamma law of shape `1 / 2` charges no negative half-line. -/
theorem gammaMeasure_half_Iio_zero :
    gammaMeasure (1 / 2) 1 (Iio (0 : ℝ)) = 0 := by
  rw [gammaMeasure, withDensity_apply _ measurableSet_Iio]
  exact lintegral_gammaPDF_of_nonpos le_rfl

/-- The unit-rate Gamma law of shape `1 / 2` has no atoms. -/
theorem gammaMeasure_half_singleton (x : ℝ) :
    gammaMeasure (1 / 2) 1 {x} = 0 := by
  rw [gammaMeasure, withDensity_apply _ (measurableSet_singleton x),
    Measure.restrict_eq_zero.mpr Real.volume_singleton, lintegral_zero_measure]

/-- Exact Laplace transform of the unit-rate Gamma law of shape `1 / 2`. -/
theorem integral_exp_neg_mul_gammaMeasure_half (u : ℝ) (hu : 0 ≤ u) :
    (∫ x : ℝ, Real.exp (-(u * x)) ∂(gammaMeasure (1 / 2) 1)) =
      (1 + u) ^ (-(1 / 2 : ℝ)) := by
  unfold gammaMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    (show Measurable (gammaPDF (1 / 2) 1) by
      exact (measurable_gammaPDFReal (1 / 2) 1).ennreal_ofReal)
    (Filter.Eventually.of_forall (fun x => by
      rw [gammaPDF]
      exact ENNReal.ofReal_lt_top))]
  rw [show (fun x : ℝ =>
      (gammaPDF (1 / 2) 1 x).toReal • Real.exp (-(u * x))) =
      (Ici 0).indicator (fun x : ℝ =>
        (Real.sqrt Real.pi)⁻¹ * x ^ (-(1 / 2 : ℝ)) *
          Real.exp (-((1 + u) * x))) by
    funext x
    rw [gammaPDF_eq]
    by_cases hx : 0 ≤ x
    · have hxmem : x ∈ Ici (0 : ℝ) := hx
      rw [if_pos hx, indicator_of_mem hxmem]
      rw [ENNReal.toReal_ofReal]
      · rw [Real.Gamma_one_half_eq]
        norm_num
        calc
          (Real.sqrt Real.pi)⁻¹ * x ^ (-(1 / 2 : ℝ)) * Real.exp (-x) *
                Real.exp (-(u * x)) =
              (Real.sqrt Real.pi)⁻¹ * x ^ (-(1 / 2 : ℝ)) *
                (Real.exp (-x) * Real.exp (-(u * x))) := by ring
          _ = (Real.sqrt Real.pi)⁻¹ * x ^ (-(1 / 2 : ℝ)) *
                Real.exp (-((1 + u) * x)) := by
            rw [← Real.exp_add]
            congr 2
            ring
      · positivity
    · have hxmem : x ∉ Ici (0 : ℝ) := hx
      rw [if_neg hx, indicator_of_notMem hxmem]
      simp]
  rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]
  rw [show (fun t : ℝ =>
      (Real.sqrt Real.pi)⁻¹ * t ^ (-(1 / 2 : ℝ)) * Real.exp (-((1 + u) * t))) =
      (fun t : ℝ => (Real.sqrt Real.pi)⁻¹ *
        (t ^ (-(1 / 2 : ℝ)) * Real.exp (-((1 + u) * t)))) by
      funext t
      ring]
  have hexponent : -(1 / 2 : ℝ) = 1 / 2 - 1 := by norm_num
  rw [integral_const_mul, hexponent,
    Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num : (0 : ℝ) < 1 / 2)
      (by linarith : 0 < 1 + u)]
  rw [Real.Gamma_one_half_eq]
  field_simp
  rw [one_div]
  rw [Real.inv_rpow (by linarith : 0 ≤ 1 + u)]
  rw [← Real.rpow_neg (by linarith : 0 ≤ 1 + u)]
  norm_num

/-- Square-root form of the Gamma-half Laplace transform. -/
theorem integral_exp_neg_mul_gammaMeasure_half_eq_inv_sqrt (u : ℝ) (hu : 0 ≤ u) :
    (∫ x : ℝ, Real.exp (-(u * x)) ∂(gammaMeasure (1 / 2) 1)) =
      (Real.sqrt (1 + u))⁻¹ := by
  rw [integral_exp_neg_mul_gammaMeasure_half u hu,
    Real.sqrt_eq_rpow, Real.rpow_neg (by linarith : 0 ≤ 1 + u)]

end

end GaloisForLFunctions.HTGeometry
