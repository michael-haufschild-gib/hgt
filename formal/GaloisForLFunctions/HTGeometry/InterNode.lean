import GaloisForLFunctions.HTGeometry.Interlacing

/-!
# The interlacing selection

Each gap between consecutive level-`n` nodes contains a level-`n+1` node.  Choosing one from each
gap
gives a map `Fin n → ℝ`, and it is strictly monotone because the `i`-th choice lies below
`gaussNode i.succ`, which is at most `gaussNode j.castSucc` whenever `i < j`, which in turn lies
below
the `j`-th choice.

So the level-`n+1` nodes contain a strictly increasing family indexed by the gaps — the interlacing
statement in the form a count can use.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- A level-`n+1` node chosen from the `i`-th gap. -/
noncomputable def interNode (h : PositiveMomentForm s) (n : ℕ) (i : Fin n) : ℝ :=
  Classical.choose (exists_gaussNode_between h n i)

theorem interNode_spec (h : PositiveMomentForm s) (n : ℕ) (i : Fin n) :
    interNode h n i ∈ gaussNodes s (n + 1) ∧
      gaussNode h n i.castSucc < interNode h n i ∧
        interNode h n i < gaussNode h n i.succ :=
  Classical.choose_spec (exists_gaussNode_between h n i)

theorem interNode_mem (h : PositiveMomentForm s) (n : ℕ) (i : Fin n) :
    interNode h n i ∈ gaussNodes s (n + 1) :=
  (interNode_spec h n i).1

theorem interNode_lt (h : PositiveMomentForm s) (n : ℕ) (i : Fin n) :
    interNode h n i < gaussNode h n i.succ :=
  (interNode_spec h n i).2.2

theorem lt_interNode (h : PositiveMomentForm s) (n : ℕ) (i : Fin n) :
    gaussNode h n i.castSucc < interNode h n i :=
  (interNode_spec h n i).2.1

/-- **The selection is strictly increasing.** -/
theorem interNode_strictMono (h : PositiveMomentForm s) (n : ℕ) :
    StrictMono (interNode h n) := by
  intro i j hij
  have hstep : gaussNode h n i.succ ≤ gaussNode h n j.castSucc := by
    refine (gaussNode h n).le_iff_le.mpr ?_
    rw [Fin.le_def]
    rw [Fin.lt_def] at hij
    simp only [Fin.val_succ, Fin.val_castSucc]
    omega
  calc interNode h n i < gaussNode h n i.succ := interNode_lt h n i
    _ ≤ gaussNode h n j.castSucc := hstep
    _ < interNode h n j := lt_interNode h n j

theorem interNode_injective (h : PositiveMomentForm s) (n : ℕ) :
    Function.Injective (interNode h n) :=
  (interNode_strictMono h n).injective

end HTGeometry
