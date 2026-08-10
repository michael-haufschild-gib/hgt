import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Vanishing of a family of sums by a band split

A family of nonnegative sums `i ↦ ∑' j, F j i` tends to zero as soon as every single term tends to
zero and, outside a large enough finite band, the tail is eventually at most `ε`.  Nothing else is
needed: the finitely many modes inside the band vanish because each of them does.

Working in `ℝ≥0∞` removes every summability side condition.  A convenient sufficient form of the
tail hypothesis is also recorded: a domination `F ≤ G + H` where the `G`-tails are uniformly small
and the total `H`-sums vanish.
-/

open Filter Topology ENNReal

namespace GaloisForLFunctions

/-- **Band split.**  Pointwise vanishing plus an eventually small tail outside a finite band
force the whole sum to vanish. -/
theorem tendsto_tsum_zero_of_tail {ι : Type*} {F : ι → ℕ → ℝ≥0∞}
    (hpt : ∀ j, Tendsto (F j) atTop (nhds 0))
    (htail : ∀ ε : ℝ≥0∞, 0 < ε → ∃ S : Finset ι, ∀ᶠ i in atTop,
      ∑' j : ↥(S : Set ι)ᶜ, F (j : ι) i ≤ ε) :
    Tendsto (fun i => ∑' j, F j i) atTop (nhds 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hhalf : (0 : ℝ≥0∞) < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨S, hS⟩ := htail (ε / 2) hhalf
  have hfin : Tendsto (fun i => ∑ j ∈ S, F j i) atTop (nhds 0) := by
    have h := tendsto_finsetSum S (fun j _ => hpt j)
    simpa using h
  have hfin' : ∀ᶠ i in atTop, ∑ j ∈ S, F j i ≤ ε / 2 :=
    (ENNReal.tendsto_nhds_zero.mp hfin) (ε / 2) hhalf
  filter_upwards [hfin', hS] with i h1 h2
  calc ∑' j, F j i
      = ∑ j ∈ S, F j i + ∑' j : ↥(S : Set ι)ᶜ, F (j : ι) i :=
        (ENNReal.sum_add_tsum_compl S _).symm
    _ ≤ ε / 2 + ε / 2 := add_le_add h1 h2
    _ = ε := ENNReal.add_halves ε

/-- Sufficient form of the tail hypothesis: a domination whose first part has uniformly small
tails and whose second part has vanishing totals. -/
theorem tendsto_tsum_zero_of_dominated {ι : Type*} {F G H : ι → ℕ → ℝ≥0∞}
    (hpt : ∀ j, Tendsto (F j) atTop (nhds 0))
    (hbound : ∀ j i, F j i ≤ G j i + H j i)
    (hGtail : ∀ ε : ℝ≥0∞, 0 < ε → ∃ S : Finset ι, ∀ i, ∑' j : ↥(S : Set ι)ᶜ, G (j : ι) i ≤ ε)
    (hH : Tendsto (fun i => ∑' j, H j i) atTop (nhds 0)) :
    Tendsto (fun i => ∑' j, F j i) atTop (nhds 0) := by
  refine tendsto_tsum_zero_of_tail hpt ?_
  intro ε hε
  have hhalf : (0 : ℝ≥0∞) < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨S, hS⟩ := hGtail (ε / 2) hhalf
  refine ⟨S, ?_⟩
  filter_upwards [(ENNReal.tendsto_nhds_zero.mp hH) (ε / 2) hhalf] with i hi
  have hcompl : ∑' j : ↥(S : Set ι)ᶜ, H (j : ι) i ≤ ∑' j, H j i :=
    ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective (fun j => H j i)
  calc ∑' j : ↥(S : Set ι)ᶜ, F (j : ι) i
      ≤ ∑' j : ↥(S : Set ι)ᶜ, (G (j : ι) i + H (j : ι) i) :=
        ENNReal.tsum_le_tsum fun j => hbound _ _
    _ = ∑' j : ↥(S : Set ι)ᶜ, G (j : ι) i + ∑' j : ↥(S : Set ι)ᶜ, H (j : ι) i :=
        ENNReal.tsum_add
    _ ≤ ε / 2 + ε / 2 := add_le_add (hS i) (le_trans hcompl hi)
    _ = ε := ENNReal.add_halves ε

end GaloisForLFunctions
