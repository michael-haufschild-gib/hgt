import GaloisForLFunctions.RHTower.HedenmalmThetaSourceDifferentialPencil
import GaloisForLFunctions.RHTower.HedenmalmThetaMetricCommutator

/-!
# Green law for the closed source-faithful theta differential pencil

The literal theta source inverse satisfies a singular-metric two-port commutator.  The closed
source-faithful differential pencil replaces its centered inverse coordinate by
`k + z • (B k - mean(B k) • 1)`.  This file transports the Green identity exactly through that
closed-graph coordinate.  The two monopole terms remain visible; omitting either would recover a
different pencil and lose the literal Xi divisor.
-/

open Complex Function MeasureTheory Set Filter Topology Module
open scoped ENNReal

namespace RHTower.HedenmalmThetaSource

noncomputable section

open HedenmalmQuantile HedenmalmHilbertSchmidt HedenmalmClosedWeightedDerivative
  HedenmalmFredholmRange GaloisForLFunctions.HTGeometry

private abbrev H := Lp ℂ 2 unitIntervalMeasure

/-- On the centered coordinate hyperplane, the closed-pencil inverse coordinate is the literal
theta source inverse. -/
theorem thetaCenteredSourceInverse_eq_thetaKernelOperator (k : thetaCentered) :
    thetaCenteredSourceInverse k = thetaKernelOperator (k : H) := by
  rw [thetaCenteredSourceInverse, ContinuousLinearMap.comp_apply]
  change thetaCompactSourceInverse (k : H) = thetaKernelOperator (k : H)
  rw [← thetaKernelOperator_eq_thetaCompactSourceInverse]

/-- Green identity in the bounded coordinates that parameterize the closed differential domain. -/
theorem thetaCenteredSourceInverse_metricGreen (k l : thetaCentered) :
    (inner ℂ (thetaMetricOperator (thetaCenteredSourceInverse k)) (l : H) : ℂ) -
      inner ℂ (thetaMetricOperator (k : H)) (thetaCenteredSourceInverse l) =
        -Complex.I * inner ℂ (pinnedBoundaryCLM (k : H)) (l : H) := by
  have hgreen := congrArg (fun T : H →L[ℂ] H =>
      (inner ℂ (T (k : H)) (l : H) : ℂ))
    thetaMetric_commutator_thetaKernelOperator
  have hsub :
      (thetaMetricOperator * thetaKernelOperator -
        ContinuousLinearMap.adjoint thetaKernelOperator * thetaMetricOperator) (k : H) =
        (thetaMetricOperator * thetaKernelOperator) (k : H) -
          (ContinuousLinearMap.adjoint thetaKernelOperator * thetaMetricOperator) (k : H) := by
    change
      ((↑(thetaMetricOperator * thetaKernelOperator -
        ContinuousLinearMap.adjoint thetaKernelOperator * thetaMetricOperator) : H →ₗ[ℂ] H)
        (k : H)) = _
    rw [ContinuousLinearMap.toLinearMap_sub, LinearMap.sub_apply]
    rfl
  rw [hsub, mul_apply_eq_comp, mul_apply_eq_comp, inner_sub_left,
    smul_apply, inner_smul_left, ContinuousLinearMap.adjoint_inner_left] at hgreen
  rw [← thetaCenteredSourceInverse_eq_thetaKernelOperator k,
    ← thetaCenteredSourceInverse_eq_thetaKernelOperator l] at hgreen
  have hconjI : (starRingEnd ℂ) Complex.I = -Complex.I := by
    exact Complex.conj_I
  rw [hconjI] at hgreen
  simpa only [neg_mul] using hgreen

/-- The bounded Green defect is exactly the difference of its incoming and outgoing scalar-port
pairings. -/
theorem inner_pinnedBoundaryCLM_eq_twoPort_pair (k l : H) :
    (inner ℂ (pinnedBoundaryCLM k) l : ℂ) =
      (starRingEnd ℂ) (pinnedBoundaryInPort k) * pinnedBoundaryInPort l -
        (starRingEnd ℂ) (pinnedBoundaryOutPort k) * pinnedBoundaryOutPort l := by
  have hsub :
      (pinnedBoundaryInPort.adjoint.comp pinnedBoundaryInPort -
        pinnedBoundaryOutPort.adjoint.comp pinnedBoundaryOutPort) k =
        (pinnedBoundaryInPort.adjoint.comp pinnedBoundaryInPort) k -
          (pinnedBoundaryOutPort.adjoint.comp pinnedBoundaryOutPort) k := by
    change
      ((↑(pinnedBoundaryInPort.adjoint.comp pinnedBoundaryInPort -
        pinnedBoundaryOutPort.adjoint.comp pinnedBoundaryOutPort) : H →ₗ[ℂ] H) k) = _
    rw [ContinuousLinearMap.toLinearMap_sub, LinearMap.sub_apply]
    rfl
  have hports := congrArg (fun T : H →L[ℂ] H =>
      (inner ℂ (T k) l : ℂ)) pinnedBoundaryCLM_eq_port_difference
  rw [hsub, ContinuousLinearMap.comp_apply,
    inner_sub_left, ContinuousLinearMap.adjoint_inner_left] at hports
  rw [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left] at hports
  simpa only [RCLike.inner_apply'] using hports

/-- Green identity in the literal incoming/outgoing coordinates on the closed-pencil graph. -/
theorem thetaCenteredSourceInverse_twoPortGreen (k l : thetaCentered) :
    (inner ℂ (thetaMetricOperator (thetaCenteredSourceInverse k)) (l : H) : ℂ) -
      inner ℂ (thetaMetricOperator (k : H)) (thetaCenteredSourceInverse l) =
        -Complex.I *
          ((starRingEnd ℂ) (pinnedBoundaryInPort (k : H)) *
              pinnedBoundaryInPort (l : H) -
            (starRingEnd ℂ) (pinnedBoundaryOutPort (k : H)) *
              pinnedBoundaryOutPort (l : H)) := by
  rw [thetaCenteredSourceInverse_metricGreen,
    inner_pinnedBoundaryCLM_eq_twoPort_pair]

/-- Exact parameterized Green law for the closed source-faithful differential pencil.  The
additional two terms are its required monopole correction; they are not a removable boundary
normalization. -/
theorem thetaSourceDifferentialRangeMap_metricGreen
    (z w : ℂ) (k l : thetaCentered) :
    (inner ℂ (thetaMetricOperator (thetaCenteredSourceInverse k))
        (thetaSourceDifferentialRangeMap w l) : ℂ) -
      inner ℂ (thetaMetricOperator (thetaSourceDifferentialRangeMap z k))
        (thetaCenteredSourceInverse l) =
      -Complex.I * inner ℂ (pinnedBoundaryCLM (k : H)) (l : H) +
        w * inner ℂ (thetaMetricOperator (thetaCenteredSourceInverse k))
          (thetaCenteredSourceInverse l -
            pinnedMean (thetaCenteredSourceInverse l) • pinnedOne) -
        (starRingEnd ℂ) z *
          inner ℂ (thetaMetricOperator
            (thetaCenteredSourceInverse k -
              pinnedMean (thetaCenteredSourceInverse k) • pinnedOne))
            (thetaCenteredSourceInverse l) := by
  rw [thetaSourceDifferentialRangeMap_apply,
    thetaSourceDifferentialRangeMap_apply,
    map_add, map_smul, inner_add_right, inner_smul_right,
    inner_add_left, inner_smul_left]
  linear_combination thetaCenteredSourceInverse_metricGreen k l

end

end RHTower.HedenmalmThetaSource
