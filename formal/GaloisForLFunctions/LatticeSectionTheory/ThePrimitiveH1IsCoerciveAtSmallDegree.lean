import GaloisForLFunctions.LatticeSectionTheory.RiemannRochOutsideAFiniteDivisorAtEveryDegree
import GaloisForLFunctions.LatticeSectionTheory.HeckeCorrespondencesAreSimilitudesOfThePrimitiveH1
import GaloisForLFunctions.SelectivePositivityAndThresholdLaws.SemilocalPrimeTwoTrace.IntrinsicWeilTraceAndWindowCorollaries

/-!
# The primitive `h¹` at small degree

Outside the finite divisor the primitive `h¹` is coercive at every degree. At small degree nothing has to be removed:
for `a ≤ 181/500` it is coercive on all real tests, including the directions of the finite divisor and the pole. So
the Künneth count satisfies the Riemann inequality on the whole scaling subsurface at these degrees, and the finite
divisor of `ℤ` obstructs nothing there.
-/

noncomputable section

open MeasureTheory

namespace GaloisForLFunctions.LatticeSectionTheory

open ArithmeticCastelnuovoSeveri ArithmeticEffectivityTheory ArithmeticOrientationGeometry
open GaloisForLFunctions.SelectivePositivityAndThresholdLaws.SemilocalPrimeTwoTrace

/-- **Coercivity at small degree.** For `a ≤ 181/500`, the primitive `h¹` is at least `∫ f²/10000` on all real tests. -/
theorem primitiveH1_ge_of_small_degree {a : ℝ} (ha : a ≤ 181 / 500) (x : ℝ × ℝ × realTestsAt a) :
    (1 / 10000 : ℝ) * ∫ u : ℝ, (x.2.2.1.1 u) ^ 2 ≤ primitiveH1 (scalingSubsurface (realTestsAt a)) x := by
  rw [primitiveH1_eq, scalingSubsurface_defect_self]
  have h := weilPair_ge_of_mem_realTestsAt_threeHundredSixtyTwoThousandths ha x.2.2
  linarith only [h]

/-- **Effectivity at small degree.** For `a ≤ 181/500` the Künneth count is an effectivity function on the whole
scaling subsurface. -/
theorem kunneth_effectivity_of_small_degree {a : ℝ} (ha : a ≤ 181 / 500) :
    RiemannInequality (scalingSubsurface (realTestsAt a)) 0 0
        (kunnethH0 (scalingSubsurface (realTestsAt a))) ∧
      DegreeBounded (scalingSubsurface (realTestsAt a))
        (kunnethH0 (scalingSubsurface (realTestsAt a))) := by
  refine (kunneth_effectivity_scalingSubsurface_iff _).mpr fun f => ?_
  have h := weilPair_ge_of_mem_realTestsAt_threeHundredSixtyTwoThousandths ha f
  have hi : 0 ≤ ∫ u : ℝ, ((f.1 : ℝ → ℝ) u) ^ 2 := integral_nonneg fun u => sq_nonneg _
  linarith only [h, hi]

end GaloisForLFunctions.LatticeSectionTheory

#print axioms GaloisForLFunctions.LatticeSectionTheory.primitiveH1_ge_of_small_degree
#print axioms GaloisForLFunctions.LatticeSectionTheory.kunneth_effectivity_of_small_degree
