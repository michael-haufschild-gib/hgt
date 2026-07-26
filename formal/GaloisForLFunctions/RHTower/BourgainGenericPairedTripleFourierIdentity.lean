/-
# Paired Fourier identity for a generic four-curve

This module identifies the paired triple cloud of the generic osculating
frequencies with the product of sixth powers of two literal exact curve
sums.  The identity is algebraic and introduces no approximation.
-/
import GaloisForLFunctions.RHTower.BourgainNormalizedGaussianDecoupling
import GaloisForLFunctions.RHTower.BourgainPairedTripleFourierIdentity

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Exact finite extension sum for the generic four-curve on an arithmetic
sample interval. -/
def bourgainGenericFourCurveExactLocalSum
    (H : ℕ) (φ₃ φ₄ : ℝ → ℝ) (D a : ℝ)
    (c : Fin H → ℂ) (x : BourgainPhaseSpace) : ℂ :=
  ∑ n : Fin H,
    c n * bourgainUnitCharacter
      (bourgainDot x
        (bourgainGenericFourCurve φ₃ φ₄
          (a + (bourgainIndex n : ℝ) / D)))

/-- Exact phase identity for the left generic osculating frequency. -/
theorem bourgainDot_genericExactLeftFrequency
    {H : ℕ} (φ₃ φ₄ : ℝ → ℝ) {scale a b : ℝ}
    (hscale : scale ≠ 0)
    (hunit : IsUnit (bourgainGenericPhaseCoordinateMatrix φ₃ φ₄ a b))
    (D : ℝ) (n : Fin H) (y : BourgainPhaseSpace) :
    bourgainDot y
        (bourgainGenericExactLeftFrequency
          φ₃ φ₄ hscale hunit D n) =
      bourgainGenericFourCurvePhase φ₃ φ₄
          ((bourgainGenericScaledPhaseContinuousLinearEquiv
            φ₃ φ₄ hscale hunit).symm y)
          (a + (bourgainIndex n : ℝ) / D) -
        bourgainGenericFourCurvePhase φ₃ φ₄
          ((bourgainGenericScaledPhaseContinuousLinearEquiv
            φ₃ φ₄ hscale hunit).symm y) a := by
  unfold bourgainGenericExactLeftFrequency
    bourgainGenericFourCurvePhase
  rw [bourgainDot_dualPullbackFrequency]
  unfold bourgainDot
  simp only [Pi.sub_apply]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  rfl

/-- Exact phase identity for the right generic osculating frequency. -/
theorem bourgainDot_genericExactRightFrequency
    {H : ℕ} (φ₃ φ₄ : ℝ → ℝ) {scale a b : ℝ}
    (hscale : scale ≠ 0)
    (hunit : IsUnit (bourgainGenericPhaseCoordinateMatrix φ₃ φ₄ a b))
    (D : ℝ) (n : Fin H) (y : BourgainPhaseSpace) :
    bourgainDot y
        (bourgainGenericExactRightFrequency
          φ₃ φ₄ hscale hunit D n) =
      bourgainGenericFourCurvePhase φ₃ φ₄
          ((bourgainGenericScaledPhaseContinuousLinearEquiv
            φ₃ φ₄ hscale hunit).symm y)
          (b + (bourgainIndex n : ℝ) / D) -
        bourgainGenericFourCurvePhase φ₃ φ₄
          ((bourgainGenericScaledPhaseContinuousLinearEquiv
            φ₃ φ₄ hscale hunit).symm y) b := by
  unfold bourgainGenericExactRightFrequency
    bourgainGenericFourCurvePhase
  rw [bourgainDot_dualPullbackFrequency]
  unfold bourgainDot
  simp only [Pi.sub_apply]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  rfl

/-- Left exact generic sum equals its osculating-frequency extension up to a
constant unit phase. -/
theorem bourgainGenericFourCurveExactLocalSum_eq_leftFrequencySum
    {H : ℕ} (φ₃ φ₄ : ℝ → ℝ) {scale a b D : ℝ}
    (hscale : scale ≠ 0)
    (hunit : IsUnit (bourgainGenericPhaseCoordinateMatrix φ₃ φ₄ a b))
    (L : BourgainPhaseSpace) (c : Fin H → ℂ)
    (x : BourgainPhaseSpace) :
    bourgainGenericFourCurveExactLocalSum H φ₃ φ₄ D a c
        ((bourgainGenericScaledPhaseContinuousLinearEquiv
          φ₃ φ₄ hscale hunit).symm (bourgainCoordinateScale L x)) =
      bourgainUnitCharacter
          (bourgainGenericFourCurvePhase φ₃ φ₄
            ((bourgainGenericScaledPhaseContinuousLinearEquiv
              φ₃ φ₄ hscale hunit).symm (bourgainCoordinateScale L x)) a) *
        bourgainWeightedFourierSum L
          (bourgainGenericExactLeftFrequency
            φ₃ φ₄ hscale hunit D) c x := by
  unfold bourgainGenericFourCurveExactLocalSum
    bourgainWeightedFourierSum
  rw [Finset.mul_sum]
  apply Fintype.sum_congr
  intro n
  rw [bourgainAdditiveCharacter_eq_unitCharacter,
    bourgainDot_genericExactLeftFrequency]
  change
    c n * bourgainUnitCharacter
        (bourgainGenericFourCurvePhase φ₃ φ₄
          ((bourgainGenericScaledPhaseContinuousLinearEquiv
            φ₃ φ₄ hscale hunit).symm (bourgainCoordinateScale L x))
          (a + (bourgainIndex n : ℝ) / D)) = _
  rw [show
    bourgainGenericFourCurvePhase φ₃ φ₄
          ((bourgainGenericScaledPhaseContinuousLinearEquiv
            φ₃ φ₄ hscale hunit).symm (bourgainCoordinateScale L x))
          (a + (bourgainIndex n : ℝ) / D) =
      bourgainGenericFourCurvePhase φ₃ φ₄
          ((bourgainGenericScaledPhaseContinuousLinearEquiv
            φ₃ φ₄ hscale hunit).symm (bourgainCoordinateScale L x)) a +
        (bourgainGenericFourCurvePhase φ₃ φ₄
            ((bourgainGenericScaledPhaseContinuousLinearEquiv
              φ₃ φ₄ hscale hunit).symm (bourgainCoordinateScale L x))
            (a + (bourgainIndex n : ℝ) / D) -
          bourgainGenericFourCurvePhase φ₃ φ₄
            ((bourgainGenericScaledPhaseContinuousLinearEquiv
              φ₃ φ₄ hscale hunit).symm (bourgainCoordinateScale L x)) a)
      by ring,
    bourgainUnitCharacter_add]
  ring

/-- Right exact generic sum equals its osculating-frequency extension up to a
constant unit phase. -/
theorem bourgainGenericFourCurveExactLocalSum_eq_rightFrequencySum
    {H : ℕ} (φ₃ φ₄ : ℝ → ℝ) {scale a b D : ℝ}
    (hscale : scale ≠ 0)
    (hunit : IsUnit (bourgainGenericPhaseCoordinateMatrix φ₃ φ₄ a b))
    (L : BourgainPhaseSpace) (c : Fin H → ℂ)
    (x : BourgainPhaseSpace) :
    bourgainGenericFourCurveExactLocalSum H φ₃ φ₄ D b c
        ((bourgainGenericScaledPhaseContinuousLinearEquiv
          φ₃ φ₄ hscale hunit).symm (bourgainCoordinateScale L x)) =
      bourgainUnitCharacter
          (bourgainGenericFourCurvePhase φ₃ φ₄
            ((bourgainGenericScaledPhaseContinuousLinearEquiv
              φ₃ φ₄ hscale hunit).symm (bourgainCoordinateScale L x)) b) *
        bourgainWeightedFourierSum L
          (bourgainGenericExactRightFrequency
            φ₃ φ₄ hscale hunit D) c x := by
  unfold bourgainGenericFourCurveExactLocalSum
    bourgainWeightedFourierSum
  rw [Finset.mul_sum]
  apply Fintype.sum_congr
  intro n
  rw [bourgainAdditiveCharacter_eq_unitCharacter,
    bourgainDot_genericExactRightFrequency]
  change
    c n * bourgainUnitCharacter
        (bourgainGenericFourCurvePhase φ₃ φ₄
          ((bourgainGenericScaledPhaseContinuousLinearEquiv
            φ₃ φ₄ hscale hunit).symm (bourgainCoordinateScale L x))
          (b + (bourgainIndex n : ℝ) / D)) = _
  rw [show
    bourgainGenericFourCurvePhase φ₃ φ₄
          ((bourgainGenericScaledPhaseContinuousLinearEquiv
            φ₃ φ₄ hscale hunit).symm (bourgainCoordinateScale L x))
          (b + (bourgainIndex n : ℝ) / D) =
      bourgainGenericFourCurvePhase φ₃ φ₄
          ((bourgainGenericScaledPhaseContinuousLinearEquiv
            φ₃ φ₄ hscale hunit).symm (bourgainCoordinateScale L x)) b +
        (bourgainGenericFourCurvePhase φ₃ φ₄
            ((bourgainGenericScaledPhaseContinuousLinearEquiv
              φ₃ φ₄ hscale hunit).symm (bourgainCoordinateScale L x))
            (b + (bourgainIndex n : ℝ) / D) -
          bourgainGenericFourCurvePhase φ₃ φ₄
            ((bourgainGenericScaledPhaseContinuousLinearEquiv
              φ₃ φ₄ hscale hunit).symm (bourgainCoordinateScale L x)) b)
      by ring,
    bourgainUnitCharacter_add]
  ring

/-- Pointwise bridge from the generic paired cloud to the exact bilinear
sixth moment. -/
theorem norm_sq_bourgainWeightedFourierSum_pairedTripleCloud_eq_genericExact
    {H : ℕ} (φ₃ φ₄ : ℝ → ℝ) {scale a b D : ℝ}
    (hscale : scale ≠ 0)
    (hunit : IsUnit (bourgainGenericPhaseCoordinateMatrix φ₃ φ₄ a b))
    (L : BourgainPhaseSpace) (c₁ c₂ : Fin H → ℂ)
    (x : BourgainPhaseSpace) :
    ‖bourgainWeightedFourierSum L
        (bourgainPairedTripleCloud
          (bourgainGenericExactLeftFrequency
            φ₃ φ₄ hscale hunit D)
          (bourgainGenericExactRightFrequency
            φ₃ φ₄ hscale hunit D))
        (bourgainPairedTripleWeight c₁ c₂) x‖ ^ (2 : ℕ) =
      ‖bourgainGenericFourCurveExactLocalSum H φ₃ φ₄ D a c₁
          ((bourgainGenericScaledPhaseContinuousLinearEquiv
            φ₃ φ₄ hscale hunit).symm
              (bourgainCoordinateScale L x))‖ ^ (6 : ℕ) *
        ‖bourgainGenericFourCurveExactLocalSum H φ₃ φ₄ D b c₂
          ((bourgainGenericScaledPhaseContinuousLinearEquiv
            φ₃ φ₄ hscale hunit).symm
              (bourgainCoordinateScale L x))‖ ^ (6 : ℕ) := by
  rw [bourgainWeightedFourierSum_pairedTripleCloud]
  rw [norm_mul, norm_pow, norm_pow]
  rw [bourgainGenericFourCurveExactLocalSum_eq_leftFrequencySum,
    bourgainGenericFourCurveExactLocalSum_eq_rightFrequencySum]
  simp only [norm_mul, norm_bourgainUnitCharacter, one_mul]
  ring

end

end RHTower
