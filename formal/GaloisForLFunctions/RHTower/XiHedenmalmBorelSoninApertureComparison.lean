import GaloisForLFunctions.RHTower.XiHedenmalmThetaBorelConditionNumber
import GaloisForLFunctions.RHTower.BurnolSoninCrossApertureRiesz

/-!
# The Borel holonomy and the Sonine evaluator have the same aperture exponent

Two independently constructed geometric-sample laws are compared here.

On the theta side, the two-sided condition number of the Borel dilation character on
`L²((0,T), b x dt)` at the samples `1 + t = r^(2 j)` has logarithmic growth rate
`|Re ρ - 1/2|`.

On the Sonine side, the completed Mellin evaluation vector of Burnol's extended Sonine space at the
apertures `a_N = r^(-N) a` has logarithmic growth rate `|Re w - 1/2|`.

Instantiating the completed variable at the centered spectral point `ρ = 1/2 + i α` makes the two
exponents the *same real number*, so the essential-tail holonomy of the theta boundary and the
aperture escape of the Gamma-completed Sonine evaluator measure one and the same displacement.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace

noncomputable section

namespace RHTower

theorem abs_re_centeredSpectralPoint_sub_half (alpha : ℂ) :
    |(1 / 2 + alpha * Complex.I).re - 1 / 2| = |alpha.im| := by
  rw [re_centeredSpectralPoint,
    show 1 / 2 - alpha.im - 1 / 2 = -alpha.im from by ring, abs_neg]

/-- **The two aperture exponents are one number.**  At a centered spectral point in the off-axis
right half strip, the Borel condition-number exponent of the theta tail and the aperture exponent of
the Gamma-completed Sonine evaluation vector are both the horizontal displacement `|Im α|`, and both
geometric-sample ratios converge to it. -/
theorem borel_and_sonin_aperture_exponents_agree
    {alpha : ℂ} (hlo : 1 / 2 < (1 / 2 + alpha * Complex.I).re)
    (hhi : (1 / 2 + alpha * Complex.I).re < 1)
    (x : ℝ) {a r : ℝ} (ha : 0 < a) (hr : 1 < r)
    (hk : burnolExtendedSoninEvaluationVector (1 / 2 + alpha * Complex.I) a hlo hhi ha ≠ 0) :
    Tendsto
        (fun j : ℕ =>
          Real.log
              ((essSup (fun t => ENNReal.ofReal ‖hedenmalmBorelCharacter alpha t‖)
                    ((hedenmalmBorelWeight x).restrict (Ioo 0 (r ^ (2 * j) - 1))) *
                  essSup (fun t => ENNReal.ofReal ‖hedenmalmBorelCharacter (-alpha) t‖)
                    ((hedenmalmBorelWeight x).restrict
                      (Ioo 0 (r ^ (2 * j) - 1)))).toReal) /
            ((j : ℝ) * Real.log r))
        atTop (𝓝 |alpha.im|) ∧
      Tendsto
        (fun N : ℕ =>
          Real.log
              ‖burnolExtendedSoninEvaluationVector (1 / 2 + alpha * Complex.I)
                ((r ^ N)⁻¹ * a) hlo hhi
                (mul_pos (inv_pos.mpr (pow_pos (lt_of_lt_of_le zero_lt_one hr.le) N)) ha)‖ /
            ((N : ℝ) * Real.log r))
        atTop (𝓝 |alpha.im|) := by
  constructor
  · have h := tendsto_log_condition_number_geometric_sample alpha x hr
    rwa [abs_re_centeredSpectralPoint_sub_half] at h
  · have h := tendsto_log_norm_burnolExtendedSoninEvaluationVector hlo hhi ha hr hk
    rwa [abs_re_centeredSpectralPoint_sub_half] at h

/-- The common exponent vanishes exactly on the critical line. -/
theorem borel_sonin_aperture_exponent_eq_zero_iff (alpha : ℂ) :
    |alpha.im| = 0 ↔ (1 / 2 + alpha * Complex.I).re = 1 / 2 := by
  rw [abs_eq_zero, re_centeredSpectralPoint]
  constructor
  · intro h
    rw [h]
    ring
  · intro h
    linarith

end RHTower
