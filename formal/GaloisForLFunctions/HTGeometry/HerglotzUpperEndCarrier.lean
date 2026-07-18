import GaloisForLFunctions.HTGeometry.RegularizedHerglotzTransform
import GaloisForLFunctions.HTGeometry.UpperEndMeromorphicField

/-!
# The Herglotz Cauchy transform as an upper-end carrier

The freeness statements about translation orbits live in the upper-end meromorphic field, whose
elements are germs admitting an analytic representative on some sufficiently high half-plane.
This module places the Cauchy transform of a finite measure into that field.

The only input is holomorphy off the real axis, which is proved by differentiating under the
integral in `RegularizedHerglotzTransform`.  Every upper half-plane avoids the axis, so the
transform is an upper-end analytic germ with height `0`.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter

noncomputable section

/-- The Cauchy transform of a finite measure is analytic on the open upper half-plane. -/
theorem analyticOnNhd_cauchyTransform_upperTail_zero
    (ν : Measure ℝ) [IsFiniteMeasure ν] :
    AnalyticOnNhd ℂ (cauchyTransform ν) (upperTail 0) := by
  apply analyticOnNhd_cauchyTransform ν (upperTail_isOpen 0)
  intro z hz
  have hpos : (0 : ℝ) < z.im := hz
  exact ne_of_gt hpos

/-- The Cauchy transform of a finite measure, as an upper-end analytic germ. -/
def cauchyTransformUpperEndAnalytic (ν : Measure ℝ) [IsFiniteMeasure ν] :
    upperEndAnalyticSubring :=
  ⟨((cauchyTransform ν : ℂ → ℂ) : Germ upperEndFilter ℂ),
    cauchyTransform ν, 0, analyticOnNhd_cauchyTransform_upperTail_zero ν, rfl⟩

@[simp]
theorem cauchyTransformUpperEndAnalytic_coe (ν : Measure ℝ) [IsFiniteMeasure ν] :
    ((cauchyTransformUpperEndAnalytic ν : upperEndAnalyticSubring) :
      Germ upperEndFilter ℂ) =
      ((cauchyTransform ν : ℂ → ℂ) : Germ upperEndFilter ℂ) :=
  rfl

/-- The Cauchy transform of a finite measure, as an element of the upper-end meromorphic field. -/
def cauchyTransformUpperEndMero (ν : Measure ℝ) [IsFiniteMeasure ν] :
    upperEndMeroField :=
  letI := isDomain_upperEndAnalyticSubring
  algebraMap upperEndAnalyticSubring upperEndMeroField
    (cauchyTransformUpperEndAnalytic ν)

end

end GaloisForLFunctions.HTGeometry
