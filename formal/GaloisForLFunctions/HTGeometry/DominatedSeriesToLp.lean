import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Uniformly dominated series converge in `L²` of a finite measure

If a pointwise series of functions is dominated term by term by a summable numerical sequence, then
on a finite measure space its `Lᵖ` classes sum to the `Lᵖ` class of the pointwise sum.  The uniform
tail bound becomes an `Lᵖ` tail bound with the constant `μ(univ)^{1/p}`, so the `Finset` net of
partial sums converges.

This is the mechanism behind every `L²` Taylor expansion on a bounded window: no dominated
convergence and no almost-everywhere subsequence is used, and the conclusion is a genuine `HasSum`
in the Banach space.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option maxHeartbeats 1000000 in
/-- **A uniformly dominated pointwise series sums in `L²` of a finite measure.** -/
theorem hasSum_toLp_of_ae_dominated {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {𝕜 : Type*} [RCLike 𝕜]
    {f : ℕ → α → 𝕜} {F : α → 𝕜} {g : ℕ → ℝ}
    (hgsum : Summable g) (hgnn : ∀ n, 0 ≤ g n)
    (hbd : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ g n)
    (hpt : ∀ᵐ x ∂μ, HasSum (fun n => f n x) (F x))
    (hmem : ∀ n, MemLp (f n) 2 μ) (hMem : MemLp F 2 μ) :
    HasSum (fun n => (hmem n).toLp (f n)) (hMem.toLp F) := by
  set K : ℝ := (measureUnivNNReal μ : ℝ) ^ ((2 : ℝ≥0∞).toReal)⁻¹ with hKdef
  have hK : 0 ≤ K := Real.rpow_nonneg (by positivity) _
  have hbdall : ∀ᵐ x ∂μ, ∀ n, ‖f n x‖ ≤ g n := ae_all_iff.mpr hbd
  have hbound : ∀ s : Finset ℕ,
      ‖(∑ n ∈ s, (hmem n).toLp (f n)) - hMem.toLp F‖
        ≤ K * (∑' n : ↥((s : Set ℕ)ᶜ), g n) := by
    intro s
    have hae : ∀ᵐ x ∂μ,
        ‖((((∑ n ∈ s, (hmem n).toLp (f n)) - hMem.toLp F) : Lp 𝕜 2 μ) : α → 𝕜) x‖
          ≤ ∑' n : ↥((s : Set ℕ)ᶜ), g n := by
      filter_upwards [Lp.coeFn_sub (∑ n ∈ s, (hmem n).toLp (f n)) (hMem.toLp F),
        Lp.coeFn_finsetSum s (fun n => (hmem n).toLp (f n)), hMem.coeFn_toLp,
        (Filter.eventually_all_finset s).mpr (fun n _ => (hmem n).coeFn_toLp),
        hpt, hbdall] with x hsub hfs hF hterms hsum hdom
      rw [hsub, Pi.sub_apply, hfs, hF, Finset.sum_apply,
        Finset.sum_congr rfl (fun n hn => hterms n hn)]
      have hsplit := hsum.summable.sum_add_tsum_compl (s := s)
      rw [hsum.tsum_eq] at hsplit
      have heq : (∑ n ∈ s, f n x) - F x = -(∑' n : ↥((s : Set ℕ)ᶜ), f n x) := by
        rw [← hsplit]
        ring
      rw [heq, norm_neg]
      have hdom' : ∀ n : ↥((s : Set ℕ)ᶜ), ‖f n x‖ ≤ g n := fun n => hdom n
      have hFsub : Summable fun n : ↥((s : Set ℕ)ᶜ) => ‖f n x‖ :=
        Summable.of_nonneg_of_le (fun n => norm_nonneg _) hdom' (hgsum.subtype _)
      exact le_trans (norm_tsum_le_tsum_norm hFsub)
        (Summable.tsum_le_tsum hdom' hFsub (hgsum.subtype _))
    have hnn : (0 : ℝ) ≤ ∑' n : ↥((s : Set ℕ)ᶜ), g n := tsum_nonneg fun n => hgnn _
    exact Lp.norm_le_of_ae_bound (p := 2) hnn hae
  rw [HasSum, SummationFilter.unconditional_filter, tendsto_iff_norm_sub_tendsto_zero]
  have htail : Tendsto (fun s : Finset ℕ => K * ∑' n : ↥((s : Set ℕ)ᶜ), g n) atTop (𝓝 0) := by
    have h := tendsto_tsum_compl_atTop_zero g
    have h2 := h.const_mul K
    rw [mul_zero] at h2
    exact h2
  exact squeeze_zero (fun s => norm_nonneg _) hbound htail

end GaloisForLFunctions.HTGeometry
