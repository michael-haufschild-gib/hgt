import GaloisForLFunctions.HTGeometry.BoundedPhaseNPlusToeplitz
import GaloisForLFunctions.HTGeometry.SmirnovBoundaryCircleL1Algebra

open Complex MeasureTheory Filter Topology Set
open scoped Real ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem integrable_circleBoundary_boundedPhaseHalfForward_half
    (b : Circle → ℝ) (hb : Measurable b)
    (hbound : ∀ z, |b z| ≤ Real.pi / 2) :
    Integrable
      (boundedPhaseHalfForward (halfBoundedPhase b)
        (measurable_halfBoundedPhase hb)
        (abs_halfBoundedPhase_le hbound)).circleBoundary
      circleLebesgue := by
  let c := halfBoundedPhase b
  let hc := measurable_halfBoundedPhase hb
  let hcbound := abs_halfBoundedPhase_le hbound
  let A := oneSubDiskMultiplierFourth
  let D := boundedPhaseMinus c hc hcbound
  let P := boundedPhasePlus c hc hcbound
  let R := boundedPhaseReciprocal c hc hcbound
  let F := boundedPhaseHalfForward c hc hcbound
  have hR : Integrable R.circleBoundary circleLebesgue :=
    integrable_circleBoundary_boundedPhaseReciprocal_half b hb hbound
  have hAmeas : AEStronglyMeasurable (diskMultiplierBoundaryFun A)
      circleLebesgue :=
    Lp.aestronglyMeasurable (hardyDiskBoundary (hardyOf A))
  have hprod : Integrable (fun z => diskMultiplierBoundaryFun A z *
      R.circleBoundary z) circleLebesgue :=
    hR.bdd_mul hAmeas (ae_norm_diskMultiplierBoundaryFun_le A)
  have heq : F.circleBoundary =ᵐ[circleLebesgue]
      fun z => diskMultiplierBoundaryFun A z * R.circleBoundary z := by
    filter_upwards [diskMultiplierBoundaryFun_mul_ae A D,
      R.denominator_circle_ne_zero_ae] with z hmul hP
    change diskMultiplierBoundaryFun (A.mul D) z /
        diskMultiplierBoundaryFun P z =
      diskMultiplierBoundaryFun A z *
        (diskMultiplierBoundaryFun D z / diskMultiplierBoundaryFun P z)
    rw [hmul]
    field_simp
  exact hprod.congr heq.symm

theorem integrable_circleBoundary_boundedPhaseNPlusOne_forward
    (b : Circle → ℝ) (hb : Measurable b)
    (hbound : ∀ z, |b z| ≤ Real.pi / 2) :
    Integrable
      (boundedPhaseSmirnovToeplitzNPlusOneElement b hb hbound).toKernelElement.forward.circleBoundary
      circleLebesgue := by
  exact integrable_circleBoundary_boundedPhaseHalfForward_half b hb hbound

theorem SmirnovToeplitzNPlusElement.integrable_forward_circleBoundary_mul_left_multiplier
    {U : ℝ → ℂ} (K : SmirnovToeplitzNPlusElement U)
    (A : DiskMultiplier)
    (hA : ∃ z ∈ Metric.ball (0 : ℂ) 1, A.fn z ≠ 0)
    (hK : Integrable K.toKernelElement.forward.circleBoundary circleLebesgue) :
    Integrable
      ((K.mul_left_multiplier A hA).toKernelElement.forward.circleBoundary)
      circleLebesgue := by
  exact K.toKernelElement.forward.integrable_circleBoundary_ofMultiplier_mul A hK

end

end GaloisForLFunctions.HTGeometry
