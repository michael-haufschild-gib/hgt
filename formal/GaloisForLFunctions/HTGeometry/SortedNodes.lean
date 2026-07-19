import GaloisForLFunctions.HTGeometry.InterlacingStep

/-!
# The Gauss nodes in increasing order

Interlacing is a statement about the *ordered* roots, so the node set needs an enumeration.  Since
`gaussNodes s n` has exactly `n+1` elements, `Finset.orderEmbOfFin` supplies an order embedding
`Fin (n+1) ↪o ℝ` whose range is the node set — the nodes listed in increasing order, with no
sorted-list bookkeeping and no subtype.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- The `n+1` Gauss nodes of level `n`, in increasing order. -/
noncomputable def gaussNode (h : PositiveMomentForm s) (n : ℕ) : Fin (n + 1) ↪o ℝ :=
  (gaussNodes s n).orderEmbOfFin (gaussNodes_card h n)

theorem gaussNode_mem (h : PositiveMomentForm s) (n : ℕ) (i : Fin (n + 1)) :
    gaussNode h n i ∈ gaussNodes s n :=
  Finset.orderEmbOfFin_mem _ _ i

/-- Each enumerated node is a root of `Q_{n+1}`. -/
theorem gaussNode_root (h : PositiveMomentForm s) (n : ℕ) (i : Fin (n + 1)) :
    (monicOrtho s (n + 1)).eval (gaussNode h n i) = 0 :=
  (mem_gaussNodes_iff n _).mp (gaussNode_mem h n i)

theorem gaussNode_strictMono (h : PositiveMomentForm s) (n : ℕ) :
    StrictMono (gaussNode h n) :=
  (gaussNode h n).strictMono

theorem gaussNode_lt_succ (h : PositiveMomentForm s) (n : ℕ) (i : Fin n) :
    gaussNode h n i.castSucc < gaussNode h n i.succ :=
  gaussNode_strictMono h n Fin.castSucc_lt_succ

/-- The enumeration exhausts the node set. -/
theorem range_gaussNode (h : PositiveMomentForm s) (n : ℕ) :
    Set.range (gaussNode h n) = ↑(gaussNodes s n) :=
  Finset.range_orderEmbOfFin _ _

/-- Every root of `Q_{n+1}` is one of the enumerated nodes. -/
theorem exists_gaussNode_eq (h : PositiveMomentForm s) (n : ℕ) {x : ℝ}
    (hx : (monicOrtho s (n + 1)).eval x = 0) : ∃ i, gaussNode h n i = x := by
  have hmem : x ∈ (gaussNodes s n : Set ℝ) := (mem_gaussNodes_iff n x).mpr hx
  rw [← range_gaussNode h n] at hmem
  exact hmem

end HTGeometry
