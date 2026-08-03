import GaloisForLFunctions.RHTower.DeningerCalderonWittAllCrossPrimeGammaAdmissionOperator

/-!
# Quadratic Deninger mate curvature of Gamma-admitted Green provenance

The Deninger duality--adjunction fracture occurs once in completed Green
provenance and once in the actual Gamma/co-Poisson admission coefficient.
This module computes their composition exactly.  After bounded
normalization, Gamma admission applied to Green provenance is the square of
the fracture times a strictly positive gauge, the oriented Hodge value, and
the nonzero Calderon--Witt packet horizon.

Consequently the scalar mate curvature is nonnegative, strictly positive on
every off-line divisor copy, and has exactly the critical line as radical.
For the fixed reflected Gaussian this radical classification holds at every
individual cross-prime packet coordinate.

All statements are unconditional.  In particular, no source null-homotopy
is asserted: the calculation proves that such a null-homotopy would have to
kill a positive quadratic mate curvature rather than cancel two odd factors.
-/

open Complex Function Set Topology
open scoped ENNReal

namespace RHTower

noncomputable section

/-- Strictly positive residual gauge after bounded normalization of the
actual Gamma boundary coefficient. -/
def deningerCalderonWittGammaGreenMateGauge (r : XiZeroCopy) : ℝ :=
  deningerCalderonWittGammaBoundaryGreenGauge r /
    (1 + ‖deningerCalderonWittBaseGammaBoundaryDefectCoefficient r‖)

/-- Bounded normalization preserves strict positivity of the Gamma--Green
comparison gauge. -/
theorem deningerCalderonWittGammaGreenMateGauge_pos (r : XiZeroCopy) :
    0 < deningerCalderonWittGammaGreenMateGauge r := by
  exact div_pos (deningerCalderonWittGammaBoundaryGreenGauge_pos r) (by positivity)

/-- Exact normalized factorization: the bounded Gamma admission coefficient
is one copy of the Deninger duality--adjunction fracture times a strictly
positive residual gauge. -/
theorem
    deningerCalderonWittNormalizedBaseGammaBoundaryDefectCoefficient_eq_greenFracture_mul_mateGauge
    (r : XiZeroCopy) :
    deningerCalderonWittNormalizedBaseGammaBoundaryDefectCoefficient r =
      xiNearbyPoleDualityAdjunctionFracture (r.1 : ℂ) *
        (deningerCalderonWittGammaGreenMateGauge r : ℂ) := by
  rw [deningerCalderonWittNormalizedBaseGammaBoundaryDefectCoefficient,
    deningerCalderonWittGammaGreenMateGauge]
  rw [deningerCalderonWittBaseGammaBoundaryDefectCoefficient_eq_greenFracture_mul_gauge]
  push_cast
  ring

/-- Positive scalar curvature produced when Gamma admission meets completed
Green provenance.  The fracture is real, so its square is recorded in `ℝ`.
-/
def deningerCalderonWittGammaGreenMateCurvature (r : XiZeroCopy) : ℝ :=
  (xiNearbyPoleDualityAdjunctionFracture (r.1 : ℂ)).re ^ 2 *
    deningerCalderonWittGammaGreenMateGauge r

/-- The Gamma--Green mate curvature is nonnegative on every Xi-divisor
copy. -/
theorem deningerCalderonWittGammaGreenMateCurvature_nonneg (r : XiZeroCopy) :
    0 ≤ deningerCalderonWittGammaGreenMateCurvature r := by
  exact mul_nonneg (sq_nonneg _) (deningerCalderonWittGammaGreenMateGauge_pos r).le

/-- Exact radical of the positive mate curvature: precisely the critical
line. -/
theorem deningerCalderonWittGammaGreenMateCurvature_eq_zero_iff
    (r : XiZeroCopy) :
    deningerCalderonWittGammaGreenMateCurvature r = 0 ↔
      (r.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro h
    have hsq :
        (xiNearbyPoleDualityAdjunctionFracture (r.1 : ℂ)).re ^ 2 = 0 :=
      (mul_eq_zero.mp h).resolve_right
        (deningerCalderonWittGammaGreenMateGauge_pos r).ne'
    have hf : (xiNearbyPoleDualityAdjunctionFracture (r.1 : ℂ)).re = 0 := by
      nlinarith
    rw [xiNearbyPoleDualityAdjunctionFracture_eq_two_re] at hf
    simp only [ofReal_re] at hf
    linarith
  · intro hline
    rw [deningerCalderonWittGammaGreenMateCurvature,
      xiNearbyPoleDualityAdjunctionFracture_eq_two_re]
    simp only [ofReal_re]
    have : 2 * ((r.1 : ℂ).re - 1 / 2) = 0 := by
      linarith
    rw [this]
    simp

/-- The mate curvature is strictly positive at exactly the off-line divisor
copies. -/
theorem deningerCalderonWittGammaGreenMateCurvature_pos_iff
    (r : XiZeroCopy) :
    0 < deningerCalderonWittGammaGreenMateCurvature r ↔
      (r.1 : ℂ).re ≠ 1 / 2 := by
  constructor
  · intro hpos hline
    rw [(deningerCalderonWittGammaGreenMateCurvature_eq_zero_iff r).2 hline] at hpos
    exact lt_irrefl 0 hpos
  · intro hline
    exact lt_of_le_of_ne
      (deningerCalderonWittGammaGreenMateCurvature_nonneg r)
      (Ne.symm
        ((deningerCalderonWittGammaGreenMateCurvature_eq_zero_iff r).not.mpr hline))

/-- **Quadratic mate-curvature law.**  On arbitrary completed Green
provenance, the actual Gamma admission operator contributes the second copy
of the duality--adjunction fracture.  Its pointwise output is the positive
mate curvature times oriented Hodge transport and the actual all-cross-prime
incidence horizon. -/
theorem
    deningerCalderonWittAllCrossPrimeGammaAdmissionOperator_greenProvenance_apply_eq_mateCurvature
    (a : XiDivisorL2) (r : XiZeroCopy)
    (i : DeningerCalderonWittCrossPrimePacketIndex) :
    deningerCalderonWittAllCrossPrimeGammaAdmissionOperator
        (deningerCalderonWittAllCrossPrimeXiIncidenceComparison
          (DeningerMeyerGaussianGreen.deningerArithmeticCompletedGreenProvenance a)) r i =
      ((deningerCalderonWittGammaGreenMateCurvature r : ℝ) : ℂ) *
        deningerArithmeticOrientedHodgeLp
          (DeningerMeyerGaussianGreen.deningerArithmeticCompletedRieszConjugation a) r *
        deningerCalderonWittCrossPrimePacketHorizon i := by
  change
    deningerCalderonWittNormalizedBaseGammaBoundaryDefectCoefficient r *
        (DeningerMeyerGaussianGreen.deningerArithmeticCompletedGreenProvenance a r *
          deningerCalderonWittCrossPrimePacketHorizon i) = _
  rw [
    deningerCalderonWittNormalizedBaseGammaBoundaryDefectCoefficient_eq_greenFracture_mul_mateGauge,
    DeningerMeyerGaussianGreen.deningerArithmeticCompletedGreenProvenance_apply,
    deningerCalderonWittGammaGreenMateCurvature,
    xiNearbyPoleDualityAdjunctionFracture_eq_two_re]
  simp only [ofReal_re]
  push_cast
  ring

/-- For the fixed reflected Gaussian, every individual cross-prime packet
coordinate has exactly the critical line as its pointwise Gamma-admitted
Green radical.  No packet-level cancellation remains available. -/
theorem
    deningerCalderonWittAllCrossPrimeGammaAdmissionOperator_reflectedGaussianGreen_apply_eq_zero_iff
    (r : XiZeroCopy) (i : DeningerCalderonWittCrossPrimePacketIndex) :
    deningerCalderonWittAllCrossPrimeGammaAdmissionOperator
        (deningerCalderonWittAllCrossPrimeXiIncidenceComparison
          DeningerMeyerGaussianGreen.reflectedGaussianHorizonGreenProvenance) r i = 0 ↔
      (r.1 : ℂ).re = 1 / 2 := by
  change
    deningerCalderonWittAllCrossPrimeGammaAdmissionOperator
        (deningerCalderonWittAllCrossPrimeXiIncidenceComparison
          (DeningerMeyerGaussianGreen.deningerArithmeticCompletedGreenProvenance
            DeningerMeyerGaussianGreen.reflectedGaussianHorizonGradeL2)) r i = 0 ↔ _
  rw [
    deningerCalderonWittAllCrossPrimeGammaAdmissionOperator_greenProvenance_apply_eq_mateCurvature]
  have hhodge :
      deningerArithmeticOrientedHodgeLp
          (DeningerMeyerGaussianGreen.deningerArithmeticCompletedRieszConjugation
            DeningerMeyerGaussianGreen.reflectedGaussianHorizonGradeL2) r ≠ 0 := by
    rw [deningerArithmeticOrientedHodgeLp_apply,
      DeningerMeyerGaussianGreen.deningerArithmeticCompletedRieszConjugation_apply]
    apply mul_ne_zero
    · exact neg_ne_zero.mpr (deningerArithmeticFEOrientation_ne_zero r)
    · rw [starRingEnd_self_apply]
      exact DeningerMeyerGaussianGreen.reflectedGaussianHorizonGrade_ne_zero
        (xiZeroCopyReflectEquiv r)
  rw [mul_eq_zero, mul_eq_zero]
  simp only [hhodge,
    deningerCalderonWittCrossPrimePacketHorizon_apply_ne_zero, or_false]
  exact_mod_cast deningerCalderonWittGammaGreenMateCurvature_eq_zero_iff r

end

end RHTower
