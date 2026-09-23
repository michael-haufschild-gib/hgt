import GaloisForLFunctions.HTGeometry.RandomMixedGraphCore
import GaloisForLFunctions.HTGeometry.FiniteBuresComparisonLaw

open Matrix Set
open scoped ComplexOrder MatrixOrder

namespace GaloisForLFunctions.HTGeometry.RandomMixedGraph

noncomputable section

structure CompactBuresCorrelationData (n : ℕ) where
  source : Matrix (Fin n) (Fin n) ℂ
  source_posSemidef : source.PosSemidef
  source_trace : source.trace.re = 1
  targets : Set (Matrix (Fin n) (Fin n) ℂ)
  targets_nonempty : targets.Nonempty
  targets_compact : IsCompact targets
  targets_posSemidef : targets ⊆ {M | M.PosSemidef}
  targets_trace : ∀ M ∈ targets, M.trace.re = 1

def compactBuresDualCorrelation {n : ℕ}
    (data : CompactBuresCorrelationData n) : CorrelationCoefficient := by
  refine ⟨compactBuresDualCapacity data.source data.targets, ?_, ?_⟩
  · have hnonneg : 0 ≤ compactBuresDualCapacity data.source data.targets := by
      obtain ⟨M, hM, hcap⟩ := exists_compactBuresRootFidelity_eq_dualCapacity
        data.source data.targets_nonempty data.targets_compact data.targets_posSemidef
      rw [hcap]
      exact finiteBuresRootFidelity_nonneg (data.targets_posSemidef hM)
    linarith
  · exact compactBuresDualCapacity_le_one
      data.source_posSemidef data.source_trace data.targets_nonempty
      data.targets_compact data.targets_posSemidef data.targets_trace

/-- Paper's market correlation distance is exactly compact Bures distance when correlation is
interpreted as optimal root fidelity. -/
theorem correlationDistance_compactBuresDualCorrelation {n : ℕ}
    (data : CompactBuresCorrelationData n) :
    correlationDistance (compactBuresDualCorrelation data) =
      compactBuresDistance data.source data.targets := by
  exact (compactBuresDistance_eq_sqrt_one_sub_dualCapacity data.source
    data.targets_nonempty data.targets_compact data.targets_posSemidef).symm

theorem correlationDistance_compactBuresDualCorrelation_sq {n : ℕ}
    (data : CompactBuresCorrelationData n) :
    correlationDistance (compactBuresDualCorrelation data) ^ (2 : ℕ) =
      2 * (1 - compactBuresDualCapacity data.source data.targets) := by
  exact correlationDistance_sq (compactBuresDualCorrelation data)

end

end GaloisForLFunctions.HTGeometry.RandomMixedGraph

