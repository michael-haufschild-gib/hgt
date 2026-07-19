import GaloisForLFunctions.HTGeometry.ConfluentDarboux

/-!
# The gaps between consecutive nodes

The enumeration of link 93 is order-complete: it lists *all* roots of `Q_{n+1}` in increasing order,
so between two consecutive entries there is no further root.  Hence `Q_{n+1}` does not vanish on the
open gap, which is what lets sign arguments run there.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **No node lies strictly between consecutive enumerated nodes.** -/
theorem monicOrtho_ne_zero_of_mem_gap (h : PositiveMomentForm s) (n : ℕ) (i : Fin n) {x : ℝ}
    (h1 : gaussNode h n i.castSucc < x) (h2 : x < gaussNode h n i.succ) :
    (monicOrtho s (n + 1)).eval x ≠ 0 := by
  intro hx
  obtain ⟨j, hj⟩ := exists_gaussNode_eq h n hx
  rw [← hj] at h1 h2
  have hlt1 : i.castSucc < j := (gaussNode h n).lt_iff_lt.mp h1
  have hlt2 : j < i.succ := (gaussNode h n).lt_iff_lt.mp h2
  rw [Fin.lt_def] at hlt1 hlt2
  simp only [Fin.val_castSucc, Fin.val_succ] at hlt1 hlt2
  omega

/-- The cofactor at a node does not vanish anywhere on the gap above it. -/
theorem cofactor_ne_zero_on_gap (h : PositiveMomentForm s) (n : ℕ) (i : Fin n)
    {G : Polynomial ℝ} (hG : monicOrtho s (n + 1) = (X - C (gaussNode h n i.castSucc)) * G)
    {x : ℝ} (h1 : gaussNode h n i.castSucc < x) (h2 : x < gaussNode h n i.succ) :
    G.eval x ≠ 0 := by
  intro h0
  refine monicOrtho_ne_zero_of_mem_gap h n i h1 h2 ?_
  rw [hG]
  simp [h0]

end HTGeometry
