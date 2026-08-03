import GaloisForLFunctions.HTGeometry.PuncturedRepresentativePieces
import GaloisForLFunctions.HTGeometry.TranslationStableDifferentialAlgebraicity

/-!
# A correction with a rational punctured representative is differentially algebraic

A ladder correction is proved rational off the poles.  Since a punctured representative determines
the field element, such a correction *is* the corresponding element of the coordinate field, and
every element of the coordinate field is differentially algebraic over it.

This is the step that discharges the corrections accumulated by iterating a ladder.
-/

open Filter Set Topology Complex
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

/-- **A rational punctured representative makes an element differentially algebraic.** -/
theorem differentialAlgebraicOver_of_hasPuncturedMeromorphicRep_ratio
    {x : meroField (Set.univ : Set ℂ)} {p q : Polynomial ℂ} (hq : q ≠ 0)
    (hx : HasPuncturedMeromorphicRep x (fun z => p.eval z / q.eval z)) :
    DifferentialAlgebraicOver (RatFunc ℂ) x := by
  have hval := eq_ratfuncToMero_of_hasPuncturedMeromorphicRep_ratio hq hx
  rw [hval]
  exact differentialAlgebraicOver_algebraMap _

end

end GaloisForLFunctions.HTGeometry
