/-
The four accountings of the critical sum, at every coherence scale.

At coherence scale `v` the sum of length `N` splits into `N^(1-v)` blocks, grouped into `N^(2v)` Farey
arcs, so each arc carries `N^(1-3v)` blocks.  A block admits the trivial bound `N^v` and, when its
Farey denominator is comparable to its length, square-root cancellation `N^(v/2)`.  Combining the two
levels — within an arc, and across arcs — in the four possible ways gives

    both coherent            **N^1**
    blocks incoherent only   **N^(1/2 + v)**
    arcs incoherent only     **N^(1 - v)**
    both incoherent          **N^(1/2)**

At the forced scale `v = 1/3` these are `1, 5/6, 2/3, 1/2` — the four values the campaign recorded
from the coherence argument, now obtained at every scale.

Two structural facts follow.  **The Lindelöf value is the only scale-invariant one**: the three partial
accountings all move with `v`, while "both incoherent" is `1/2` at every scale.  And the two partial
accountings are equally strong exactly at `v = 1/4`, where both give `N^(3/4)`; below that block-level
incoherence is worth more, above it arc-level is.  Since the dissection forces `v = 1/3 > 1/4`,
**arc-level incoherence is the more valuable half at the scale the problem actually occupies** — which
is why across-arc cancellation, not within-arc, carries the campaign's gap.
-/
import GaloisForLFunctions.HTGeometry.CoherenceScaleForced

namespace HTGeometry

/-! ### The four exponents -/

/-- Both levels summed by the triangle inequality. -/
def accountBothCoherent (_v : ℚ) : ℚ := 1

/-- Square-root cancellation among the blocks of an arc, triangle inequality across arcs. -/
def accountBlocksIncoherent (v : ℚ) : ℚ := 1 / 2 + v

/-- Triangle inequality within an arc, square-root cancellation across arcs. -/
def accountArcsIncoherent (v : ℚ) : ℚ := 1 - v

/-- Square-root cancellation at both levels. -/
def accountBothIncoherent (_v : ℚ) : ℚ := 1 / 2

/-! ### At the forced scale they are the recorded four values -/

theorem accounts_at_forced_scale :
    accountBothCoherent (1 / 3) = 1 ∧
      accountBlocksIncoherent (1 / 3) = 5 / 6 ∧
      accountArcsIncoherent (1 / 3) = 2 / 3 ∧
      accountBothIncoherent (1 / 3) = 1 / 2 := by
  refine ⟨rfl, ?_, ?_, rfl⟩
  · unfold accountBlocksIncoherent; norm_num
  · unfold accountArcsIncoherent; norm_num

/-- **The block-level accounting reproduces the classical exponent at the forced scale.** -/
theorem blocks_reproduce_classical :
    accountBlocksIncoherent (1 / 3) = withinArcTotalExponent (1 / 3) := by
  rw [withinArcTotal_at_forced]
  unfold accountBlocksIncoherent; norm_num

/-- **And the doubly-incoherent accounting is the Lindelöf target.** -/
theorem both_incoherent_is_target (v : ℚ) :
    accountBothIncoherent v = lindelofTargetExponent := rfl

/-! ### Scale invariance -/

/-- **The Lindelöf value does not move with the scale.** -/
theorem bothIncoherent_constant (v v' : ℚ) :
    accountBothIncoherent v = accountBothIncoherent v' := rfl

/-- The block-level accounting worsens as the scale grows. -/
theorem blocksIncoherent_mono {v v' : ℚ} (h : v < v') :
    accountBlocksIncoherent v < accountBlocksIncoherent v' := by
  unfold accountBlocksIncoherent; linarith

/-- The arc-level accounting improves as the scale grows. -/
theorem arcsIncoherent_antitone {v v' : ℚ} (h : v < v') :
    accountArcsIncoherent v' < accountArcsIncoherent v := by
  unfold accountArcsIncoherent; linarith

/-- **So the two partial accountings move in opposite directions.** -/
theorem partial_accounts_oppose {v v' : ℚ} (h : v < v') :
    accountBlocksIncoherent v < accountBlocksIncoherent v' ∧
      accountArcsIncoherent v' < accountArcsIncoherent v :=
  ⟨blocksIncoherent_mono h, arcsIncoherent_antitone h⟩

/-! ### Where they cross -/

/-- The scale at which the two partial accountings agree. -/
def partialCrossingScale : ℚ := 1 / 4

/-- **They agree exactly at `v = 1/4`.** -/
theorem partial_accounts_agree_iff (v : ℚ) :
    accountBlocksIncoherent v = accountArcsIncoherent v ↔ v = partialCrossingScale := by
  unfold accountBlocksIncoherent accountArcsIncoherent partialCrossingScale
  constructor <;> intro h <;> linarith

/-- **And the common value there is `3/4`.** -/
theorem partial_crossing_value :
    accountBlocksIncoherent partialCrossingScale = 3 / 4 ∧
      accountArcsIncoherent partialCrossingScale = 3 / 4 := by
  constructor
  · unfold accountBlocksIncoherent partialCrossingScale; norm_num
  · unfold accountArcsIncoherent partialCrossingScale; norm_num

/-- **Above the crossing, arc-level incoherence is the stronger half.** -/
theorem arcs_stronger_above_crossing {v : ℚ} (h : partialCrossingScale < v) :
    accountArcsIncoherent v < accountBlocksIncoherent v := by
  unfold accountArcsIncoherent accountBlocksIncoherent partialCrossingScale at *
  linarith

/-- **And the forced scale lies above it**, so across-arc cancellation is the more valuable half at
the scale the problem occupies. -/
theorem forced_scale_above_crossing :
    partialCrossingScale < 1 / 3 ∧
      accountArcsIncoherent (1 / 3) < accountBlocksIncoherent (1 / 3) := by
  refine ⟨by unfold partialCrossingScale; norm_num, ?_⟩
  exact arcs_stronger_above_crossing (by unfold partialCrossingScale; norm_num)

/-! ### The summary -/

/-- **The four-way summary at the forced scale**, matching the campaign's recorded values, together
with the scale-invariance of the Lindelöf value and the ordering of the two partial accountings. -/
theorem four_accountings_summary :
    accountBothCoherent (1 / 3) = 1 ∧
      accountBlocksIncoherent (1 / 3) = 5 / 6 ∧
      accountArcsIncoherent (1 / 3) = 2 / 3 ∧
      accountBothIncoherent (1 / 3) = 1 / 2 ∧
      accountArcsIncoherent (1 / 3) < accountBlocksIncoherent (1 / 3) := by
  obtain ⟨h1, h2, h3, h4⟩ := accounts_at_forced_scale
  exact ⟨h1, h2, h3, h4, forced_scale_above_crossing.2⟩

/-- **The gap between the two partial accountings at the forced scale.** -/
theorem partial_gap_at_forced :
    accountBlocksIncoherent (1 / 3) - accountArcsIncoherent (1 / 3) = 1 / 6 := by
  obtain ⟨-, h2, h3, -⟩ := accounts_at_forced_scale
  rw [h2, h3]; norm_num

end HTGeometry
