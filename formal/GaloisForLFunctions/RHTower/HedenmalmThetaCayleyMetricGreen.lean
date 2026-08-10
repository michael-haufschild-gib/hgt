import GaloisForLFunctions.RHTower.HedenmalmThetaBoundaryCayleyFlow
import GaloisForLFunctions.RHTower.HedenmalmThetaMetricCommutator

/-!
# Singular-metric Green law for the theta Cayley clock

The canonical metric `G = M_{1/q}` exactly cancels the quantile speed in the compact theta source
inverse `B = i M_q V`.  Consequently its metric commutator is not zero: it is precisely the
rank-two pinned boundary operator,

`G B - B† G = i C`.

This is the operator-level Green identity behind the Route T Cayley receiver.  Squaring and rotating
the source inverse converts the same law into the boundary-work source for the discrete clock.
-/

open Complex MeasureTheory

namespace RHTower

noncomputable section

open HedenmalmQuantile HedenmalmThetaSource

private abbrev ThetaH := Lp ℂ 2 unitIntervalMeasure

/-- Adjoint of the rotated source square. -/
theorem adjoint_thetaBoundarySquareGenerator :
    thetaBoundarySquareGenerator.adjoint =
      Complex.I • (thetaKernelOperator.adjoint * thetaKernelOperator.adjoint) := by
  simp only [thetaBoundarySquareGenerator, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.adjoint.map_smulₛₗ, ContinuousLinearMap.adjoint_comp,
    RCLike.conj_neg, RCLike.conj_I, neg_neg]

/-- The rotated square has boundary-work source `C B + B† C` in the singular metric. -/
theorem thetaMetric_rotatedSquare_greenSource :
    thetaMetricOperator * thetaBoundarySquareGenerator +
        thetaBoundarySquareGenerator.adjoint * thetaMetricOperator =
      pinnedBoundaryCLM * thetaKernelOperator +
        thetaKernelOperator.adjoint * pinnedBoundaryCLM := by
  let B : ThetaH →L[ℂ] ThetaH := thetaKernelOperator
  let G : ThetaH →L[ℂ] ThetaH := thetaMetricOperator
  let C : ThetaH →L[ℂ] ThetaH := pinnedBoundaryCLM
  have hcomm : G * B - B.adjoint * G = Complex.I • C := by
    simpa only [B, G, C] using thetaMetric_commutator_thetaKernelOperator
  have hsource :
      G * (B * B) - (B.adjoint * B.adjoint) * G =
        Complex.I • (C * B + B.adjoint * C) := by
    calc
      G * (B * B) - (B.adjoint * B.adjoint) * G =
          (G * B - B.adjoint * G) * B +
            B.adjoint * (G * B - B.adjoint * G) := by noncomm_ring
      _ = (Complex.I • C) * B + B.adjoint * (Complex.I • C) := by rw [hcomm]
      _ = Complex.I • (C * B + B.adjoint * C) := by
        simp only [smul_mul_assoc, mul_smul_comm, smul_add]
  rw [thetaBoundarySquareGenerator, adjoint_thetaBoundarySquareGenerator]
  change G * ((-Complex.I) • (B * B)) +
      (Complex.I • (B.adjoint * B.adjoint)) * G = C * B + B.adjoint * C
  rw [mul_smul_comm, smul_mul_assoc]
  calc
    (-Complex.I) • (G * (B * B)) +
        Complex.I • ((B.adjoint * B.adjoint) * G) =
        (-Complex.I) •
          (G * (B * B) - (B.adjoint * B.adjoint) * G) := by module
    _ = (-Complex.I) • (Complex.I • (C * B + B.adjoint * C)) := by rw [hsource]
    _ = C * B + B.adjoint * C := by
      rw [smul_smul]
      norm_num

end

end RHTower
