import GaloisForLFunctions.HTGeometry.SubstitutionNonvanishing

/-!
# Triangular systems are solvable off the diagonal's zero set

A system whose `k`-th equation determines the `k`-th unknown from the earlier ones, with a common
nonzero diagonal coefficient, is solvable: read the equations in order and divide.

This is the surjectivity of the point map that the nonvanishing criterion consumes, and it is the
only place the diagonal's nonvanishing is used.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The solution of a triangular system, built by strong recursion: each unknown is determined by
the earlier ones. -/
def triangularSolve (d : ℂ) (L : ℕ → (ℕ → ℂ) → ℂ) (w : ℕ → ℂ) : ℕ → ℂ :=
  fun n => Nat.strongRecOn n fun k ih =>
    (w k - L k fun j => if h : j < k then ih j h else 0) / d

/-- **Triangular systems are solvable.**  If each equation's lower part depends only on the strictly
earlier unknowns and the diagonal is nonzero, the system has a solution. -/
theorem exists_triangular_solution {d : ℂ} (hd : d ≠ 0) (L : ℕ → (ℕ → ℂ) → ℂ)
    (hL : ∀ (k : ℕ) (v v' : ℕ → ℂ), (∀ j, j < k → v j = v' j) → L k v = L k v')
    (w : ℕ → ℂ) :
    ∃ v : ℕ → ℂ, ∀ k, d * v k + L k v = w k := by
  classical
  refine ⟨triangularSolve d L w, ?_⟩
  intro k
  have hval : triangularSolve d L w k
      = (w k - L k fun j => if h : j < k then triangularSolve d L w j else 0) / d := by
    rw [triangularSolve]
    rw [Nat.strongRecOn_eq]
    rfl
  have hagree : (L k fun j => if h : j < k then triangularSolve d L w j else 0)
      = L k (triangularSolve d L w) := by
    refine hL k _ _ ?_
    intro j hj
    rw [dif_pos hj]
  rw [hval, hagree]
  field_simp
  ring

end

end GaloisForLFunctions.HTGeometry
