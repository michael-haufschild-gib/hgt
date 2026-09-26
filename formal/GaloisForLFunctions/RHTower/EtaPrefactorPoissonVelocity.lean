import GaloisForLFunctions.HTGeometry.ExteriorEulerPoissonBridge
import GaloisForLFunctions.HTGeometry.GammaVerticalDecay
import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaDerivative

/-!
# Unconditional Poisson decomposition of the eta prefactor velocity

The logistic coordinate covers the whole open strip.  Both complementary
dyadic radii are exterior and their product is exactly two.  Their Poisson
decomposition gives a uniform bound stronger than minus log two, directly
for the existing eta-factor logarithmic derivative.  This concerns the
elementary prefactor only and makes no cancellation of zeta values.
-/

namespace RiemannGaussian

open Complex GaloisForLFunctions GaloisForLFunctions.HTGeometry

noncomputable section

/-- The left dyadic radius, expressed in the global exterior coordinate. -/
def etaPrefactorLeftCoordinate (x : ℝ) : ℝ :=
  Real.log (Real.exp ((1 - sigmoid x) * Real.log 2) - 1)

/-- The complementary dyadic radius in the same coordinate. -/
def etaPrefactorRightCoordinate (x : ℝ) : ℝ :=
  Real.log (Real.exp (sigmoid x * Real.log 2) - 1)

theorem exteriorEulerRadius_etaPrefactorLeftCoordinate (x : ℝ) :
    exteriorEulerRadius (etaPrefactorLeftCoordinate x) =
      Real.exp ((1 - sigmoid x) * Real.log 2) := by
  have hexp : 1 < Real.exp ((1 - sigmoid x) * Real.log 2) :=
    Real.one_lt_exp_iff.mpr (mul_pos (sub_pos.mpr (sigmoid_lt_one x))
      (Real.log_pos (by norm_num)))
  rw [exteriorEulerRadius, etaPrefactorLeftCoordinate, Real.exp_log (by linarith)]
  ring

theorem exteriorEulerRadius_etaPrefactorRightCoordinate (x : ℝ) :
    exteriorEulerRadius (etaPrefactorRightCoordinate x) =
      Real.exp (sigmoid x * Real.log 2) := by
  have hexp : 1 < Real.exp (sigmoid x * Real.log 2) :=
    Real.one_lt_exp_iff.mpr (mul_pos (sigmoid_pos x) (Real.log_pos (by norm_num)))
  rw [exteriorEulerRadius, etaPrefactorRightCoordinate, Real.exp_log (by linarith)]
  ring

/-- Complementary eta radii have a fixed radial product. -/
theorem etaPrefactor_radii_mul (x : ℝ) :
    exteriorEulerRadius (etaPrefactorLeftCoordinate x) *
      exteriorEulerRadius (etaPrefactorRightCoordinate x) = 2 := by
  rw [exteriorEulerRadius_etaPrefactorLeftCoordinate,
    exteriorEulerRadius_etaPrefactorRightCoordinate, ← Real.exp_add,
    show (1 - sigmoid x) * Real.log 2 + sigmoid x * Real.log 2 = Real.log 2 by ring,
    Real.exp_log (by norm_num)]

/-- Polar form of the dyadic multiplier, valid at every complex horizontal
coordinate before any restriction to the strip. -/
theorem two_mul_cpow_neg_horizontal (σ b : ℝ) :
    2 * (2 : ℂ) ^ (-((σ : ℂ) + (b : ℂ) * I)) =
      (Real.exp ((1 - σ) * Real.log 2) : ℂ) *
        Complex.exp (((-b * Real.log 2 : ℝ) : ℂ) * I) := by
  have htwo : (2 : ℂ) = Complex.exp (Real.log 2 : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log (by norm_num)]
    norm_num
  have hlog : Complex.log 2 = (Real.log 2 : ℂ) := by
    simp
  rw [Complex.cpow_def_of_ne_zero (by norm_num),
    hlog]
  conv_lhs => lhs; rw [htwo]
  rw [← Complex.exp_add, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The literal eta-factor velocity is the negative exterior speed times
log two. -/
theorem pairedEtaFactorLogDerivative_logistic_left (x b : ℝ) :
    (pairedEtaFactorLogDerivative ((sigmoid x : ℂ) + (b : ℂ) * I)).re =
      -Real.log 2 * exteriorEulerSpeed (etaPrefactorLeftCoordinate x)
        (-b * Real.log 2) := by
  have hu := two_mul_cpow_neg_horizontal (sigmoid x) b
  have hlog : Complex.log 2 = (Real.log 2 : ℂ) := by
    simp
  rw [← exteriorEulerRadius_etaPrefactorLeftCoordinate] at hu
  have hform : pairedEtaFactorLogDerivative ((sigmoid x : ℂ) + (b : ℂ) * I) =
      (Real.log 2 : ℂ) *
        (((exteriorEulerRadius (etaPrefactorLeftCoordinate x) : ℝ) : ℂ) *
          Complex.exp (((-b * Real.log 2 : ℝ) : ℂ) * I) /
        (1 - (exteriorEulerRadius (etaPrefactorLeftCoordinate x) : ℂ) *
          Complex.exp (((-b * Real.log 2 : ℝ) : ℂ) * I))) := by
    unfold pairedEtaFactorLogDerivative pairedEtaFactor
    rw [show 2 * Complex.log 2 * (2 : ℂ) ^ (-((sigmoid x : ℂ) + (b : ℂ) * I)) =
        Complex.log 2 * (2 * (2 : ℂ) ^ (-((sigmoid x : ℂ) + (b : ℂ) * I))) by ring,
      hu, hlog]
    ring
  rw [hform, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
    re_exteriorEuler_resolvent]
  ring

theorem pairedEtaFactorLogDerivative_logistic_right (x b : ℝ) :
    (pairedEtaFactorLogDerivative (((1 - sigmoid x : ℝ) : ℂ) + (b : ℂ) * I)).re =
      -Real.log 2 * exteriorEulerSpeed (etaPrefactorRightCoordinate x)
        (-b * Real.log 2) := by
  have hu := two_mul_cpow_neg_horizontal (1 - sigmoid x) b
  have hlog : Complex.log 2 = (Real.log 2 : ℂ) := by
    simp
  rw [show 1 - (1 - sigmoid x) = sigmoid x by ring,
    ← exteriorEulerRadius_etaPrefactorRightCoordinate] at hu
  have hform : pairedEtaFactorLogDerivative (((1 - sigmoid x : ℝ) : ℂ) + (b : ℂ) * I) =
      (Real.log 2 : ℂ) *
        ((exteriorEulerRadius (etaPrefactorRightCoordinate x) : ℂ) *
          Complex.exp (((-b * Real.log 2 : ℝ) : ℂ) * I) /
        (1 - (exteriorEulerRadius (etaPrefactorRightCoordinate x) : ℂ) *
          Complex.exp (((-b * Real.log 2 : ℝ) : ℂ) * I))) := by
    unfold pairedEtaFactorLogDerivative pairedEtaFactor
    rw [show 2 * Complex.log 2 * (2 : ℂ) ^ (-(((1 - sigmoid x : ℝ) : ℂ) + (b : ℂ) * I)) =
        Complex.log 2 * (2 * (2 : ℂ) ^ (-(((1 - sigmoid x : ℝ) : ℂ) + (b : ℂ) * I))) by ring,
      hu, hlog]
    ring
  rw [hform, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
    re_exteriorEuler_resolvent]
  ring

/-- Exact Poisson correction to the constant eta prefactor drift. -/
theorem pairedEtaFactorLogDerivative_sum_poisson (x b : ℝ) :
    (pairedEtaFactorLogDerivative ((sigmoid x : ℂ) + (b : ℂ) * I)).re +
      (pairedEtaFactorLogDerivative (((1 - sigmoid x : ℝ) : ℂ) + (b : ℂ) * I)).re =
      -Real.log 2 * (1 +
        (exteriorEulerPoisson (etaPrefactorLeftCoordinate x) (-b * Real.log 2) +
          exteriorEulerPoisson (etaPrefactorRightCoordinate x) (-b * Real.log 2)) / 2) := by
  rw [pairedEtaFactorLogDerivative_logistic_left,
    pairedEtaFactorLogDerivative_logistic_right,
    exteriorEulerSpeed_eq_half_add_poisson, exteriorEulerSpeed_eq_half_add_poisson]
  ring

/-- Complementary dyadic Poisson mass has a positive floor independent of
both the strip coordinate and height. -/
theorem etaPrefactor_poisson_pair_gt_third (x θ φ : ℝ) :
    1 / 3 < exteriorEulerPoisson (etaPrefactorLeftCoordinate x) θ +
      exteriorEulerPoisson (etaPrefactorRightCoordinate x) φ := by
  have h := exteriorEuler_pair_product_floor (etaPrefactorLeftCoordinate x)
    (etaPrefactorRightCoordinate x) θ φ
  rw [etaPrefactor_radii_mul, exteriorEulerSpeed_eq_half_add_poisson,
    exteriorEulerSpeed_eq_half_add_poisson] at h
  linarith

/-- The eta prefactor is uniformly more negative than `-(7/6) log 2` on
the entire open strip, including height zero. -/
theorem pairedEtaFactorLogDerivative_sum_lt_seven_sixths (x b : ℝ) :
    (pairedEtaFactorLogDerivative ((sigmoid x : ℂ) + (b : ℂ) * I)).re +
      (pairedEtaFactorLogDerivative (((1 - sigmoid x : ℝ) : ℂ) + (b : ℂ) * I)).re <
        -(7 / 6) * Real.log 2 := by
  rw [pairedEtaFactorLogDerivative_sum_poisson]
  have h := etaPrefactor_poisson_pair_gt_third x (-b * Real.log 2) (-b * Real.log 2)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

end

end RiemannGaussian
