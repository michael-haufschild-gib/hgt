import GaloisForLFunctions.HTGeometry.HellingerAffinityFactorization

/-! # Bhattacharyya affinity under measurable embeddings -/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

/-- An injective measurable relabelling preserves affinity, including for measures
that are not absolutely continuous with respect to one another. -/
theorem bhattacharyya_map_measurableEmbedding {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {f : α → β}
    (hf : MeasurableEmbedding f) (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    bhattacharyya (μ.map f) (ν.map f) = bhattacharyya μ ν := by
  simp only [bhattacharyya, ← Measure.map_add μ ν hf.measurable]
  rw [hf.lintegral_map]
  refine lintegral_congr_ae ?_
  filter_upwards [hf.rnDeriv_map μ (μ + ν), hf.rnDeriv_map ν (μ + ν)] with x hμ hν
  rw [hμ, hν]

end GaloisForLFunctions.HTGeometry
