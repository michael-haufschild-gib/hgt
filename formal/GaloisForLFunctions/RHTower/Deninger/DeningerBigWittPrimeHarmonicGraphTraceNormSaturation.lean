import GaloisForLFunctions.RHTower.Deninger.DeningerBigWittCrossPrimeHarmonicSingularGraphSource
import GaloisForLFunctions.HTGeometry.SchattenOneBanach
import GaloisForLFunctions.HTGeometry.PointedFisherCutoffWardTrace

/-!
# Trace-norm saturation of the prime-harmonic Big-Witt graph source

The normalized prime-two Big-Witt horizon rows are an actual arithmetic
source sequence.  Their ambient Calderón--Witt realizations disappear, while
their singular graph realizations converge to the vertical one-leg trace
generator.  Passing through the continuous positive rank-one embedding gives
a canonical ordinary Schatten-one operator limit.

That limit is invisible after ambient projection, but its ordinary operator
trace and its genuine approximation-number trace norm are both exactly one.
Thus ambient collapse cannot be promoted to a strict subunit nuclear bound:
the singular coordinate carrying unit charge pays the sharp unit trace-norm
cost.  This is the positive saturation law exposed by the failed singular
graph lift.  No RH, zero-location, positivity, spectral-synthesis, or
computation premise occurs.
-/

open Complex Filter Function Set Topology
open scoped BigOperators ENNReal InnerProductSpace

namespace RHTower

noncomputable section

/-- Canonical ordinary Schatten-one lift of the source-derived vertical
one-leg graph generator. -/
noncomputable def deningerBigWittPrimeHarmonicGraphTraceOneOperator :
    SchattenOneOperator DeningerBigWittCrossPairSingularOneLegGraph :=
  positiveRankOneSchattenOne
    deningerBigWittCrossPairOneLegGraphSingularVector

/-- The source-derived vertical graph generator is a unit vector. -/
@[simp] theorem norm_deningerBigWittCrossPairOneLegGraphSingularVector :
    ‖deningerBigWittCrossPairOneLegGraphSingularVector‖ = 1 := by
  exact (WithLp.norm_toLp_snd 2
    DeningerCalderonWittCrossPrimePacketHilbert ℂ (1 : ℂ)).trans norm_one

/-- Actual normalized prime-harmonic source rows converge, after the
positive rank-one lift, in genuine trace norm to the canonical operator. -/
theorem tendsto_deningerBigWittPrimeHarmonicGraphTraceOneOperator :
    Tendsto
      (fun n => positiveRankOneSchattenOne
        (deningerBigWittCrossPairFiniteOneLegGraphAdmission
          (deningerBigWittPrimeTwoRightEdgeNormalizedPacket n)))
      atTop (nhds deningerBigWittPrimeHarmonicGraphTraceOneOperator) := by
  exact continuous_positiveRankOneSchattenOne.continuousAt.tendsto.comp
    tendsto_deningerBigWittCrossPairFiniteOneLegGraphAdmission_primeTwoRightEdgeNormalizedPacket

/-- The canonical graph lift is genuinely Schatten one. -/
theorem deningerBigWittPrimeHarmonicGraphTraceOneOperator_memSchattenClass :
    MemSchattenClass 1
      ((deningerBigWittPrimeHarmonicGraphTraceOneOperator :
          SchattenOneOperator DeningerBigWittCrossPairSingularOneLegGraph) :
        DeningerBigWittCrossPairSingularOneLegGraph →L[ℂ]
          DeningerBigWittCrossPairSingularOneLegGraph) :=
  deningerBigWittPrimeHarmonicGraphTraceOneOperator.property

/-- Its bundled Schatten-one norm is exactly one. -/
@[simp] theorem norm_deningerBigWittPrimeHarmonicGraphTraceOneOperator :
    ‖deningerBigWittPrimeHarmonicGraphTraceOneOperator‖ = 1 := by
  rw [deningerBigWittPrimeHarmonicGraphTraceOneOperator,
    norm_positiveRankOneSchattenOne,
    norm_deningerBigWittCrossPairOneLegGraphSingularVector]
  norm_num

/-- Its genuine approximation-number trace norm is exactly one. -/
@[simp] theorem traceNorm_deningerBigWittPrimeHarmonicGraphTraceOneOperator :
    traceNorm DeningerBigWittCrossPairSingularOneLegGraph
      ((deningerBigWittPrimeHarmonicGraphTraceOneOperator :
          SchattenOneOperator DeningerBigWittCrossPairSingularOneLegGraph) :
        DeningerBigWittCrossPairSingularOneLegGraph →L[ℂ]
          DeningerBigWittCrossPairSingularOneLegGraph) = 1 := by
  simpa only [SchattenOneOperator.norm_def] using
    norm_deningerBigWittPrimeHarmonicGraphTraceOneOperator

/-- Its ordinary operator trace is exactly one. -/
@[simp] theorem opTrace_deningerBigWittPrimeHarmonicGraphTraceOneOperator :
    ContinuousLinearMap.opTrace
      ((deningerBigWittPrimeHarmonicGraphTraceOneOperator :
          SchattenOneOperator DeningerBigWittCrossPairSingularOneLegGraph) :
        DeningerBigWittCrossPairSingularOneLegGraph →L[ℂ]
          DeningerBigWittCrossPairSingularOneLegGraph) = 1 := by
  change ContinuousLinearMap.opTrace
    (InnerProductSpace.rankOne ℂ
      deningerBigWittCrossPairOneLegGraphSingularVector
      deningerBigWittCrossPairOneLegGraphSingularVector) = 1
  rw [GaloisForLFunctions.HTGeometry.opTrace_rankOne]
  rw [inner_self_eq_norm_sq_to_K,
    norm_deningerBigWittCrossPairOneLegGraphSingularVector]
  norm_num

/-- Ambient Calderón--Witt shadow of the canonical graph lift. -/
noncomputable def deningerBigWittPrimeHarmonicGraphTraceOneAmbientShadow :
    DeningerBigWittCrossPairSingularOneLegGraph →L[ℂ]
      DeningerCalderonWittCrossPrimePacketHilbert :=
  deningerBigWittCrossPairOneLegGraphAmbientProjection.comp
    (deningerBigWittPrimeHarmonicGraphTraceOneOperator :
      DeningerBigWittCrossPairSingularOneLegGraph →L[ℂ]
        DeningerBigWittCrossPairSingularOneLegGraph)

/-- The ambient shadow vanishes: all unit charge lies in the singular graph
coordinate erased by the ambient projection. -/
@[simp] theorem deningerBigWittPrimeHarmonicGraphTraceOneAmbientShadow_eq_zero :
    deningerBigWittPrimeHarmonicGraphTraceOneAmbientShadow = 0 := by
  ext z
  simp [deningerBigWittPrimeHarmonicGraphTraceOneAmbientShadow,
    deningerBigWittPrimeHarmonicGraphTraceOneOperator,
    positiveRankOneSchattenOne, rankOneSchattenOne,
    InnerProductSpace.rankOne_apply]

/-- **Sharp saturation.** The source-derived trace-one graph lift cannot be
strictly subunit in nuclear norm. -/
theorem not_traceNorm_deningerBigWittPrimeHarmonicGraphTraceOneOperator_lt_one :
    ¬ traceNorm DeningerBigWittCrossPairSingularOneLegGraph
      ((deningerBigWittPrimeHarmonicGraphTraceOneOperator :
          SchattenOneOperator DeningerBigWittCrossPairSingularOneLegGraph) :
        DeningerBigWittCrossPairSingularOneLegGraph →L[ℂ]
          DeningerBigWittCrossPairSingularOneLegGraph) < 1 := by
  rw [traceNorm_deningerBigWittPrimeHarmonicGraphTraceOneOperator]
  norm_num

end


end RHTower
