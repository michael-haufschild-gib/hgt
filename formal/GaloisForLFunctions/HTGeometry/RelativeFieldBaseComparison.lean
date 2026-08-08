/-
The family-relative and field-relative differential algebra are the same notion.

Two relative theories coexist.  `RelativeDifferentialAlgebraicity` grades differential algebraicity
by a base *family* of functions and is used in two modules; `DifferentialAlgebraicOver` grades it by
a differential *subfield* and carries the rest of the corpus, always over `ℂ(z)` inside
`meroField univ`.  No declaration mentioned both, so the family layer was an island.

The jet bridge closes the gap on entire functions: the coordinate base is the one-element family
`{z}`, and an entire function is differentially algebraic over it exactly when its meromorphic
realization is differentially algebraic over the rational coordinate field.  Hence the two relative
hypertranscendence notions agree there, and either one yields ordinary hypertranscendence.
-/
import GaloisForLFunctions.HTGeometry.RelativeCoordinateBaseComparison
import GaloisForLFunctions.HTGeometry.BesselOrderMeromorphic

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

/-- **The family-relative and field-relative notions agree at the coordinate base.**  For an entire
function, differential algebraicity over the one-element base `{z}` is differential algebraicity of
its meromorphic realization over the rational coordinate field. -/
theorem differentiallyAlgebraicOver_coordinateBase_iff_meroField {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Set.univ : Set ℂ)) :
    RelativeDifferentialAlgebraicity.DifferentiallyAlgebraicOver
        RelativeDifferentialAlgebraicity.coordinateBase f ↔
      DifferentialAlgebraicOver (RatFunc ℂ) (analyticMeroElement f hf) := by
  rw [RelativeDifferentialAlgebraicity.differentiallyAlgebraicOver_coordinateBase_iff]
  constructor
  · exact differentialAlgebraicOver_analyticMeroElement_of_differentiallyAlgebraic hf
  · exact differentiallyAlgebraic_of_differentialAlgebraicOver_analyticMeroElement hf

/-- **The two relative hypertranscendence notions agree at the coordinate base.** -/
theorem hypertranscendentalOver_coordinateBase_iff_meroField {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Set.univ : Set ℂ)) :
    RelativeDifferentialAlgebraicity.HypertranscendentalOver
        RelativeDifferentialAlgebraicity.coordinateBase f ↔
      GaloisForLFunctions.HypertranscendentalOver (RatFunc ℂ) (analyticMeroElement f hf) :=
  not_congr (differentiallyAlgebraicOver_coordinateBase_iff_meroField hf)

/-- **Field-relative hypertranscendence of the realization is ordinary hypertranscendence.** -/
theorem hypertranscendental_of_hypertranscendentalOver_meroField {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Set.univ : Set ℂ))
    (h : GaloisForLFunctions.HypertranscendentalOver (RatFunc ℂ) (analyticMeroElement f hf)) :
    GaloisForLFunctions.Hypertranscendental f :=
  RelativeDifferentialAlgebraicity.hypertranscendentalOver_coordinateBase_iff.1
    ((hypertranscendentalOver_coordinateBase_iff_meroField hf).2 h)

end

end GaloisForLFunctions.HTGeometry
