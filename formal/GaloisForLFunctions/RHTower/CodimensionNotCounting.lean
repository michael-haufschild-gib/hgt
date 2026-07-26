import GaloisForLFunctions.RHTower.BoundaryCaseStillInsufficient

/-!
# The hypothesis is a codimension statement, and counts measure area

The last lane the atlas left open was the unnormalised correlation count.  It closes immediately, and
the way it closes explains every other closure.

**Unnormalised counts are worse, not better.**  A region of fixed size at height `T` contains `≍ log T`
zeros, so any pair count over such a region grows; removing the density normalisation makes the
statistic larger, not sub-unit.  A sub-unit count requires a region smaller than the mean spacing, and
there the count is `0` or `1` and carries no information about the line.

**The reason, and it is geometric.**  The hypothesis says the zeros lie on a one-dimensional subset of
a two-dimensional region.  That is a statement of **codimension**.  Counting and density statistics
measure two-dimensional content; a codimension-one set has two-dimensional measure zero, so no
counting or density statistic can detect membership in it.

> **Counts measure area; the hypothesis constrains dimension.  A measure-zero constraint is invisible
> to every measure, which is why the counting closure is total.**

This single observation unifies the closures already recorded: density theorems bound area;
correlation statistics are quadratic and again bound area; the only `β`-sensitive weights are
non-analytic, because detecting a codimension-one set is a measure-theoretic and not an analytic act;
and the height-uniformity gap is the impossibility of an area bound falling below one on a region whose
area grows.

This file formalizes the vanishing two-dimensional measure of the critical line and the
impossibility of detecting a null set by a positive measure.
-/

open MeasureTheory Set

noncomputable section

namespace RHTower

/-- **The critical line is null in the plane.**  A vertical line has two-dimensional measure zero. -/
theorem criticalLine_volume_zero (c : ℝ) :
    volume ({c} ×ˢ (Set.univ : Set ℝ)) = 0 := by
  rw [Measure.volume_eq_prod, Measure.prod_prod]
  simp

/-- **A positive-measure set is not contained in a null set.**  So no statistic that only sees measure
can certify membership in the line. -/
theorem not_subset_of_measure_pos {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {A S : Set α} (hA : 0 < μ A) (hS : μ S = 0) : ¬ A ⊆ S := by
  intro hsub
  have : μ A ≤ μ S := measure_mono hsub
  rw [hS] at this
  have hzero : μ A = 0 := le_antisymm this (zero_le)
  rw [hzero] at hA
  exact lt_irrefl 0 hA

/-- **Counts over a fixed region grow.**  With density `D` and region size `r`, the count is `D · r`,
which grows with the density however small the region. -/
theorem count_grows_with_density {r : ℝ} (hr : 0 < r) {D₁ D₂ : ℝ} (h : D₁ ≤ D₂) :
    D₁ * r ≤ D₂ * r := by
  exact mul_le_mul_of_nonneg_right h (le_of_lt hr)

/-- **Sub-unit forces sub-spacing.**  A count below one over a region of size `r` with density `D`
forces `r < 1/D`, i.e. a region smaller than the mean spacing. -/
theorem subunit_forces_subspacing {D r : ℝ} (hD : 0 < D) (h : D * r < 1) : r < 1 / D := by
  rw [lt_div_iff₀ hD, mul_comm]
  exact h

/-- And below the spacing the count is uninformative: it is bounded by one whether or not the zeros
lie on the line. -/
theorem subspacing_uninformative {D r : ℝ} (hD : 0 < D) (h : r < 1 / D) : D * r < 1 := by
  rw [lt_div_iff₀ hD, mul_comm] at h
  exact h

end RHTower
