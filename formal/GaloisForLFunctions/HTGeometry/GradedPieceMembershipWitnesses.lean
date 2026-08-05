import GaloisForLFunctions.HTGeometry.HermitianFlagRealization

/-!
# Membership in a graded piece

A graded piece of a flag is the part of one step orthogonal to everything strictly below it.  The
zero vector is always there, membership is exactly the pair of conditions defining the meet, and at
the bottom step there is nothing below, so the piece is the whole step.
-/

namespace GaloisForLFunctions.HTGeometry

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {m : ℕ}

/-- The zero vector lies in every graded piece. -/
theorem zero_mem_gradedPiece (A : Fin (m + 2) → Submodule ℂ E) (j : Fin (m + 2)) :
    (0 : E) ∈ gradedPiece A j :=
  Submodule.zero_mem _

/-- **Membership in a graded piece is the step together with orthogonality to everything below.** -/
theorem mem_gradedPiece_iff {A : Fin (m + 2) → Submodule ℂ E} {j : Fin (m + 2)} {x : E} :
    x ∈ gradedPiece A j ↔
      x ∈ A j ∧ x ∈ (⨆ i ∈ {i : Fin (m + 2) | i < j}, A i)ᗮ := Iff.rfl

/-- Membership from the two conditions. -/
theorem mem_gradedPiece {A : Fin (m + 2) → Submodule ℂ E} {j : Fin (m + 2)} {x : E}
    (hx : x ∈ A j) (horth : x ∈ (⨆ i ∈ {i : Fin (m + 2) | i < j}, A i)ᗮ) :
    x ∈ gradedPiece A j := ⟨hx, horth⟩

/-- **At the bottom step nothing lies below, so the graded piece is the whole step.** -/
theorem mem_gradedPiece_zero {A : Fin (m + 2) → Submodule ℂ E} {x : E} (hx : x ∈ A 0) :
    x ∈ gradedPiece A 0 := by
  refine mem_gradedPiece hx ?_
  have hbot : (⨆ i ∈ {i : Fin (m + 2) | i < 0}, A i) = ⊥ := by
    refine iSup_eq_bot.mpr fun i => iSup_eq_bot.mpr fun hi => ?_
    exact absurd hi (by simp)
  rw [hbot]
  simp

end GaloisForLFunctions.HTGeometry
