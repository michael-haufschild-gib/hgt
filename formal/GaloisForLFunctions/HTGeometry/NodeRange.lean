import GaloisForLFunctions.HTGeometry.ExtremeNode

/-!
# The node range expands

Every root of `Q_{n+1}` is at most the largest enumerated node, so the root above it produced by
`exists_root_above_last` — a node of level `n+1` — forces the largest node of level `n+1` to exceed
the largest node of level `n`.

The node ranges therefore grow with the level.  No parity bookkeeping enters: the statement concerns
only the upper end, where the monic leading behaviour is positive regardless of degree.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- Every root of `Q_{m+1}` is at most the largest enumerated node of level `m`. -/
theorem le_gaussNode_last (h : PositiveMomentForm s) (m : ℕ) {y : ℝ}
    (hy : (monicOrtho s (m + 1)).eval y = 0) : y ≤ gaussNode h m (Fin.last m) := by
  obtain ⟨j, hj⟩ := exists_gaussNode_eq h m hy
  rw [← hj]
  exact (gaussNode h m).monotone (Fin.le_last j)

/-- **The largest node strictly increases with the level.** -/
theorem gaussNode_last_lt_last (h : PositiveMomentForm s) (n : ℕ) :
    gaussNode h n (Fin.last n) < gaussNode h (n + 1) (Fin.last (n + 1)) := by
  obtain ⟨z, hz, hzroot⟩ := exists_root_above_last h n
  exact lt_of_lt_of_le hz (le_gaussNode_last h (n + 1) hzroot)

/-- The largest nodes form a strictly increasing sequence in the level. -/
theorem gaussNode_last_strictMono (h : PositiveMomentForm s) :
    StrictMono fun n => gaussNode h n (Fin.last n) :=
  strictMono_nat_of_lt_succ (gaussNode_last_lt_last h)

end HTGeometry
