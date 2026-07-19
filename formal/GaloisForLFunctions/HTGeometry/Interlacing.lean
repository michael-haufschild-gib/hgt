import GaloisForLFunctions.HTGeometry.Alternation

/-!
# Interlacing of the zeros

Between consecutive roots of `Q_{n+1}` there is a root of `Q_{n+2}`.  The alternation of `Qₙ` across
those roots is the hypothesis the interlacing step of link 92 was stated with, and it is now
available, so the two combine directly.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **Interlacing.**  Between consecutive nodes of level `n` lies a root of `Q_{n+2}`. -/
theorem exists_root_between_gaussNodes (h : PositiveMomentForm s) (n : ℕ) (i : Fin n) :
    ∃ z, gaussNode h n i.castSucc < z ∧ z < gaussNode h n i.succ ∧
      (monicOrtho s (n + 2)).eval z = 0 :=
  exists_root_between h n (gaussNode_lt_succ h n i)
    (gaussNode_root h n i.castSucc) (gaussNode_root h n i.succ)
    (monicOrtho_eval_alternates h n i)

/-- The interlacing root is a node of the next level. -/
theorem exists_gaussNode_between (h : PositiveMomentForm s) (n : ℕ) (i : Fin n) :
    ∃ z ∈ gaussNodes s (n + 1), gaussNode h n i.castSucc < z ∧ z < gaussNode h n i.succ := by
  obtain ⟨z, hz1, hz2, hz3⟩ := exists_root_between_gaussNodes h n i
  exact ⟨z, (mem_gaussNodes_iff (n + 1) z).mpr hz3, hz1, hz2⟩

end HTGeometry
