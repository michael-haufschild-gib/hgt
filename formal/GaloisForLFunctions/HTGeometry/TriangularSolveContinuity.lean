import GaloisForLFunctions.HTGeometry.TriangularSolvability

/-!
# The triangular solution as a function of its data

Reading a triangular system in order and dividing produces a solution which is a continuous function
of the right-hand side, of the diagonal, and of any parameters the lower part depends on: each
unknown is obtained from the earlier ones by one subtraction and one division by the nonvanishing
diagonal.

This is what upgrades the algebraic solvability of a triangular jet system to a topological
statement -- that the inverse of a triangular jet map is continuous.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The defining recursion of the triangular solution. -/
theorem triangularSolve_eq (d : ℂ) (L : ℕ → (ℕ → ℂ) → ℂ) (w : ℕ → ℂ) (k : ℕ) :
    triangularSolve d L w k
      = (w k - L k fun j => if _ : j < k then triangularSolve d L w j else 0) / d := by
  rw [triangularSolve, Nat.strongRecOn_eq]
  rfl

/-- The triangular solution solves the system. -/
theorem triangularSolve_spec {d : ℂ} (hd : d ≠ 0) (L : ℕ → (ℕ → ℂ) → ℂ)
    (hL : ∀ (k : ℕ) (v v' : ℕ → ℂ), (∀ j, j < k → v j = v' j) → L k v = L k v')
    (w : ℕ → ℂ) (k : ℕ) :
    d * triangularSolve d L w k + L k (triangularSolve d L w) = w k := by
  have hval := triangularSolve_eq d L w k
  have hagree : (L k fun j => if _ : j < k then triangularSolve d L w j else 0)
      = L k (triangularSolve d L w) := by
    refine hL k _ _ ?_
    intro j hj
    rw [dif_pos hj]
  rw [hval, hagree]
  field_simp
  ring

/-- The triangular solution is the only solution. -/
theorem triangularSolve_unique {d : ℂ} (hd : d ≠ 0) (L : ℕ → (ℕ → ℂ) → ℂ)
    (hL : ∀ (k : ℕ) (v v' : ℕ → ℂ), (∀ j, j < k → v j = v' j) → L k v = L k v')
    (w v : ℕ → ℂ) (hv : ∀ k, d * v k + L k v = w k) (k : ℕ) :
    v k = triangularSolve d L w k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
      have hval := triangularSolve_eq d L w k
      have hagree : (L k fun j => if _ : j < k then triangularSolve d L w j else 0) = L k v := by
        refine hL k _ _ ?_
        intro j hj
        rw [dif_pos hj, ih j hj]
      rw [hval, hagree, ← hv k]
      field_simp
      ring

/-- **The triangular solution is continuous in its data.** -/
theorem continuousOn_triangularSolve {X : Type*} [TopologicalSpace X] {V : Set X}
    {d : X → ℂ} (hd : ContinuousOn d V) (hdne : ∀ x ∈ V, d x ≠ 0)
    {L : X → ℕ → (ℕ → ℂ) → ℂ} {w : X → ℕ → ℂ}
    (hL : ∀ (k : ℕ) (u : X → ℕ → ℂ), (∀ j, ContinuousOn (fun x => u x j) V) →
      ContinuousOn (fun x => L x k (u x)) V)
    (hw : ∀ k, ContinuousOn (fun x => w x k) V) (k : ℕ) :
    ContinuousOn (fun x => triangularSolve (d x) (L x) (w x) k) V := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
      have heq : ∀ x : X, triangularSolve (d x) (L x) (w x) k
          = (w x k - L x k fun j => if _ : j < k then triangularSolve (d x) (L x) (w x) j else 0)
              / d x := fun x => triangularSolve_eq _ _ _ k
      simp only [heq]
      refine ContinuousOn.div ((hw k).sub ?_) hd hdne
      refine hL k (fun x j => if _ : j < k then triangularSolve (d x) (L x) (w x) j else 0) ?_
      intro j
      by_cases hj : j < k
      · simpa [hj] using ih j hj
      · simpa [hj] using (continuousOn_const : ContinuousOn (fun _ : X => (0 : ℂ)) V)

end

end GaloisForLFunctions.HTGeometry
