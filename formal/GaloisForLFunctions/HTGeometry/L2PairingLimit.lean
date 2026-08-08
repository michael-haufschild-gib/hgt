import Mathlib

/-!
# Passing a uniform pairing bound to a limit or a series

A bound on the pairing of a fixed vector against each term of a convergent sequence passes to the
limit, because the pairing is continuous.  A bound by a summable majorant against each term of a
summable series passes to the sum, because the pairing is a continuous linear map.

These are the two steps that carry a channel-by-channel estimate to the whole object: first sum the
channels, then take the limit of the truncations.  Neither step needs anything about the vectors
beyond convergence in norm.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **A uniform pairing bound passes to a norm limit.** -/
theorem norm_inner_le_of_tendsto {f : ℕ → E} {x g : E} {C : ℝ}
    (hf : Tendsto f atTop (𝓝 x)) (hC : ∀ n, ‖(inner 𝕜 g (f n) : 𝕜)‖ ≤ C) :
    ‖(inner 𝕜 g x : 𝕜)‖ ≤ C := by
  have h : Tendsto (fun n => (inner 𝕜 g (f n) : 𝕜)) atTop (𝓝 (inner 𝕜 g x : 𝕜)) :=
    (innerSL 𝕜 g).continuous.continuousAt.tendsto.comp hf
  exact le_of_tendsto h.norm (Eventually.of_forall hC)

/-- **A summable majorant of the channel pairings bounds the pairing against the sum.** -/
theorem norm_inner_tsum_le {f : ℕ → E} {g : E} {M : ℕ → ℝ}
    (hf : Summable f) (hM : Summable M) (hC : ∀ k, ‖(inner 𝕜 g (f k) : 𝕜)‖ ≤ M k) :
    ‖(inner 𝕜 g (∑' k, f k) : 𝕜)‖ ≤ ∑' k, M k := by
  have hsum : HasSum (fun k => (inner 𝕜 g (f k) : 𝕜)) (inner 𝕜 g (∑' k, f k) : 𝕜) :=
    (innerSL 𝕜 g).hasSum hf.hasSum
  have hnormsum : Summable fun k => ‖(inner 𝕜 g (f k) : 𝕜)‖ :=
    hM.of_nonneg_of_le (fun k => norm_nonneg _) hC
  calc ‖(inner 𝕜 g (∑' k, f k) : 𝕜)‖ = ‖∑' k, (inner 𝕜 g (f k) : 𝕜)‖ := by rw [hsum.tsum_eq]
    _ ≤ ∑' k, ‖(inner 𝕜 g (f k) : 𝕜)‖ := norm_tsum_le_tsum_norm hnormsum
    _ ≤ ∑' k, M k := hnormsum.tsum_le_tsum hC hM

/-- The two steps composed: a summable channel majorant bounds the pairing against any norm limit of
partial sums. -/
theorem norm_inner_le_tsum_of_tendsto {f : ℕ → E} {x g : E} {M : ℕ → ℝ}
    (hf : Summable f) (hM : Summable M) (hC : ∀ k, ‖(inner 𝕜 g (f k) : 𝕜)‖ ≤ M k)
    (hx : Tendsto (fun n => ∑ k ∈ Finset.range n, f k) atTop (𝓝 x)) :
    ‖(inner 𝕜 g x : 𝕜)‖ ≤ ∑' k, M k := by
  have hxeq : x = ∑' k, f k := tendsto_nhds_unique hx hf.hasSum.tendsto_sum_nat
  rw [hxeq]
  exact norm_inner_tsum_le hf hM hC

end GaloisForLFunctions.HTGeometry
