import GaloisForLFunctions.WindowedLandauTheory.RankGapBounds.GridNumericalHypotheses
import GaloisForLFunctions.WindowedLandauTheory.FrobeniusOrbits.ThickFrames

namespace WindowedLandauTheory.RankGapBounds.V4

open FrobeniusOrbits

/-- The Bernoulli subset theorem supplies the required thick set with controlled marked weight. -/
theorem tops_lemma_sixteen_holds : RankGapPrintedLemma := by
  intro α ι _ _ _ δ β ω BAD _ hδ₀ hδ₁ hcard hβ hω hBAD
  obtain ⟨T, hlo, hhi, hsum⟩ := hostTops α ι δ β ω BAD hδ₀ hδ₁ hβ hω hcard
    (fun p t => by
      have hp := hBAD p t
      rw [Finset.sum_filter] at hp
      convert hp using 1
      apply Finset.sum_congr rfl
      intro S _
      exact congrArg (fun d => @ite ℝ (t ∈ S ∧ BAD p t S) d (bern δ S) 0)
        (Subsingleton.elim _ _))
  have hfilter (p : ι) :
      @Finset.filter α (fun t => BAD p t T) (fun _ => Classical.propDecidable _) T =
        T.filter (fun t => BAD p t T) := by
    ext t
    simp only [Finset.mem_filter]
  refine ⟨T, hlo, hhi, ?_⟩
  simpa only [hfilter] using hsum

end WindowedLandauTheory.RankGapBounds.V4
