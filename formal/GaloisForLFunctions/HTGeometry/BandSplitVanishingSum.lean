import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Vanishing of a family of sums by a band split

A family of nonnegative sums `i ↦ ∑' j, F j i` tends to zero as soon as

* every single term tends to zero,
* the terms are dominated by `G + H`, where the sums of `G` have a tail uniformly small outside a
  finite band, and the total sums of `H` tend to zero.

This is the standard `ε/4 + ε/2 + ε/4` argument, in `ℝ≥0∞` so that no summability side condition
is needed.  It is the shape every "fixed modes plus tail" estimate takes.
-/

open Filter Topology ENNReal

namespace GaloisForLFunctions

/-- **Band split.**  Pointwise vanishing plus a uniformly small tail and a vanishing remainder
force the whole sum to vanish. -/
theorem tendsto_tsum_zero_of_bandSplit {ι : Type*} {F G H : ι → ℕ → ℝ≥0∞}
    (hpt : ∀ j, Tendsto (F j) atTop (nhds 0))
    (hbound : ∀ j i, F j i ≤ G j i + H j i)
    (hGtail : ∀ ε : ℝ≥0∞, 0 < ε → ∃ S : Finset ι, ∀ i, ∑' j : ↥(S : Set ι)ᶜ, G j i ≤ ε)
    (hH : Tendsto (fun i => ∑' j, H j i) atTop (nhds 0)) :
    Tendsto (fun i => ∑' j, F j i) atTop (nhds 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hhalf : (0 : ℝ≥0∞) < ε / 2 := ENNReal.half_pos hε.ne'
  have hquarter : (0 : ℝ≥0∞) < ε / 2 / 2 := ENNReal.half_pos hhalf.ne'
  obtain ⟨S, hS⟩ := hGtail (ε / 2) hhalf
  have hfin : Tendsto (fun i => ∑ j ∈ S, F j i) atTop (nhds 0) := by
    have h := tendsto_finsetSum S (fun j _ => hpt j)
    simpa using h
  have hfin' : ∀ᶠ i in atTop, ∑ j ∈ S, F j i ≤ ε / 2 / 2 :=
    (ENNReal.tendsto_nhds_zero.mp hfin) (ε / 2 / 2) hquarter
  have hH' : ∀ᶠ i in atTop, ∑' j, H j i ≤ ε / 2 / 2 :=
    (ENNReal.tendsto_nhds_zero.mp hH) (ε / 2 / 2) hquarter
  filter_upwards [hfin', hH'] with i h1 h2
  have hcompl : ∑' j : ↥(S : Set ι)ᶜ, H j i ≤ ∑' j, H j i :=
    ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective (fun j => H j i)
  have hstep : ∑' j : ↥(S : Set ι)ᶜ, F j i
      ≤ ∑' j : ↥(S : Set ι)ᶜ, G j i + ∑' j : ↥(S : Set ι)ᶜ, H j i := by
    rw [← ENNReal.tsum_add]
    exact ENNReal.tsum_le_tsum fun j => hbound _ _
  have htotal : ∑' j, F j i ≤ ε / 2 / 2 + (ε / 2 + ε / 2 / 2) := by
    calc ∑' j, F j i
        = ∑ j ∈ S, F j i + ∑' j : ↥(S : Set ι)ᶜ, F j i :=
          (ENNReal.sum_add_tsum_compl S _).symm
      _ ≤ ε / 2 / 2 + (∑' j : ↥(S : Set ι)ᶜ, G j i + ∑' j : ↥(S : Set ι)ᶜ, H j i) :=
          add_le_add h1 hstep
      _ ≤ ε / 2 / 2 + (ε / 2 + ε / 2 / 2) :=
          add_le_add le_rfl (add_le_add (hS i) (le_trans hcompl h2))
  refine htotal.trans ?_
  have hrearrange : ε / 2 / 2 + (ε / 2 + ε / 2 / 2)
      = (ε / 2 / 2 + ε / 2 / 2) + ε / 2 := by ring
  rw [hrearrange, ENNReal.add_halves, ENNReal.add_halves]

end GaloisForLFunctions
