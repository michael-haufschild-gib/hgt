import GaloisForLFunctions.WindowedLandauTheory.RankGapBounds.GridNumericalHypotheses
import GaloisForLFunctions.WindowedLandauTheory.FrobeniusOrbits.ThickFrames

namespace WindowedLandauTheory.RankGapBounds.V4

open FrobeniusOrbits

/-- The Bernoulli subset theorem supplies the required thick set with controlled marked weight. -/
theorem tops_lemma_sixteen_holds : RankGapPrintedLemma := by
  intro α ι _ _ _ δ β ω BAD _ hδ₀ hδ₁ hcard hβ hω hBAD
  apply hostTops α ι δ β ω BAD hδ₀ hδ₁ hβ hω hcard
  intro p t
  rw [← Finset.sum_filter]
  exact hBAD p t

end WindowedLandauTheory.RankGapBounds.V4
