import GaloisForLFunctions.RHTower.PaperWoldFiniteColumnEnergy
import GaloisForLFunctions.RHTower.PaperWoldWalshDomain

/-! # Unbounded norm at the full Walsh admission boundary

The actual compact Walsh operators have divergent norms as their exponent
approaches three quarters. Every member of an explicit approaching sequence
still has zero paper compact-ideal cost.
-/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions.HTGeometry

def paperWoldWalshBoundaryFilter : Filter {t : ℝ // t < 3 / 4} :=
  comap Subtype.val (𝓝 (3 / 4 : ℝ))

theorem paperWoldWalshFullOperator_norm_tendsto_at_boundary :
    Tendsto (fun t : {t : ℝ // t < 3 / 4} => ‖paperWoldWalshFullOperator t‖)
      paperWoldWalshBoundaryFilter atTop := by
  have hv : Tendsto (Subtype.val : {t : ℝ // t < 3 / 4} → ℝ)
      paperWoldWalshBoundaryFilter (𝓝 (3 / 4 : ℝ)) := tendsto_comap
  apply tendsto_atTop.mpr
  intro C
  filter_upwards [hv.eventually (paperWoldPhaseRealization_norm_eventually_large C)] with t ht
  exact (ht paperWoldFullWalshPhase (paperWoldWalshFullRealization t)).le

def paperWoldWalshBoundaryParameter (N : ℕ) : {t : ℝ // t < 3 / 4} :=
  ⟨3 / 4 - 1 / ((N : ℝ) + 1), by
    have hp : 0 < 1 / ((N : ℝ) + 1) := by positivity
    linarith⟩

theorem paperWoldWalshBoundaryParameter_tendsto :
    Tendsto paperWoldWalshBoundaryParameter atTop paperWoldWalshBoundaryFilter := by
  apply tendsto_comap_iff.mpr
  change Tendsto (fun N : ℕ => 3 / 4 - 1 / ((N : ℝ) + 1)) atTop (𝓝 (3 / 4 : ℝ))
  simpa only [sub_zero] using (tendsto_const_nhds (x := (3 / 4 : ℝ))).sub
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem paperWoldWalshBoundaryFilter_neBot : paperWoldWalshBoundaryFilter.NeBot :=
  paperWoldWalshBoundaryParameter_tendsto.neBot

def paperWoldWalshBoundaryOperator (N : ℕ) : PaperWoldHistory →L[ℂ] PaperWoldHistory :=
  paperWoldWalshFullOperator (paperWoldWalshBoundaryParameter N)

theorem paperWoldWalshBoundaryOperator_compact (N : ℕ) :
    IsCompactOperator (paperWoldWalshBoundaryOperator N) :=
  paperWoldWalshFullOperator_compact _

theorem paperWoldWalshBoundaryOperator_traceCost (N : ℕ) :
    compactOperatorTraceCost PaperWoldHistory (paperWoldWalshBoundaryOperator N) = 0 :=
  paperWoldWalshFullOperator_traceCost _

theorem paperWoldWalshBoundaryOperator_norm_tendsto :
    Tendsto (fun N => ‖paperWoldWalshBoundaryOperator N‖) atTop atTop :=
  paperWoldWalshFullOperator_norm_tendsto_at_boundary.comp paperWoldWalshBoundaryParameter_tendsto

/-- Exact compact-ideal membership persists along an unbounded native family. -/
theorem paperWoldWalshBoundary_compact_zeroCost_unbounded :
    (∀ N, IsCompactOperator (paperWoldWalshBoundaryOperator N)) ∧
    (∀ N, compactOperatorTraceCost PaperWoldHistory (paperWoldWalshBoundaryOperator N) = 0) ∧
    Tendsto (fun N => ‖paperWoldWalshBoundaryOperator N‖) atTop atTop :=
  ⟨paperWoldWalshBoundaryOperator_compact, paperWoldWalshBoundaryOperator_traceCost,
    paperWoldWalshBoundaryOperator_norm_tendsto⟩

end
end RHTower
