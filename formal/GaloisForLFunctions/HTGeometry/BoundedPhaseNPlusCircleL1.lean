import GaloisForLFunctions.HTGeometry.BoundedPhaseNPlusToeplitz
import GaloisForLFunctions.HTGeometry.SmirnovBoundaryCircleL1Algebra

/-!
# Circle-boundary `L¹` integrability for bounded-phase `N⁺` Toeplitz kernel elements

For a measurable circle phase `b` with `|b| ≤ π/2`, the half-phase construction gives a Smirnov quotient
`F = (1 - z)^4 (1 - S) / (1 + S)`, where `S` is the Schur function built from the Herglotz transform of
`b / 2`. This module proves that the boundary values of `F` on the unit circle are Lebesgue integrable:
`F` is the bounded multiplier `(1 - z)^4` times the reciprocal quotient `(1 - S) / (1 + S)`, whose boundary
function is already known to be integrable. The same integrability passes to the forward element of the
bounded-phase `N⁺` Toeplitz kernel element and is preserved under left multiplication by a disk
multiplier.

## Main results

- `integrable_circleBoundary_boundedPhaseHalfForward_half`: the circle boundary of the half-phase
  forward quotient is integrable for `circleLebesgue`.
- `integrable_circleBoundary_boundedPhaseNPlusOne_forward`: the same for the forward element of
  `boundedPhaseSmirnovToeplitzNPlusOneElement b`.
- `SmirnovToeplitzNPlusElement.integrable_forward_circleBoundary_mul_left_multiplier`: circle-boundary
  integrability of the forward element survives multiplication by a disk multiplier not identically
  zero on the disk.

## Hypotheses

Unconditional. The phase results assume `b` measurable with `|b z| ≤ π/2` for all `z`. The last result
takes as hypotheses that the multiplier `A` is nonzero at some point of the unit disk and that the
forward circle boundary of `K` is already integrable.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- For measurable `b` with `|b| ≤ π/2`, the half-phase forward quotient `(1 - z)^4 (1 - S) / (1 + S)` has
an integrable boundary function on the unit circle: almost everywhere it is the bounded factor
`(1 - z)^4` times the integrable reciprocal quotient. -/
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

/-- The forward element of the bounded-phase `N⁺` Toeplitz kernel element has an integrable boundary
function on the unit circle, for measurable `b` with `|b| ≤ π/2`. -/
theorem integrable_circleBoundary_boundedPhaseNPlusOne_forward
    (b : Circle → ℝ) (hb : Measurable b)
    (hbound : ∀ z, |b z| ≤ Real.pi / 2) :
    Integrable
      (boundedPhaseSmirnovToeplitzNPlusOneElement b hb hbound).toKernelElement.forward.circleBoundary
      circleLebesgue := by
  exact integrable_circleBoundary_boundedPhaseHalfForward_half b hb hbound

/-- If the forward circle boundary of an `N⁺[U]` kernel element `K` is integrable and `A` is a disk
multiplier with a nonzero value in the unit disk, then the forward circle boundary of `A · K` is
integrable. -/
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
