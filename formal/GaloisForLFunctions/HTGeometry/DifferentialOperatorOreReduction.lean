import GaloisForLFunctions.HTGeometry.DifferentialOperatorOreColumn

/-!
# Simultaneous clearing of a row and a column

Combining the two elementary families of moves, a matrix over the operator ring can be brought to a
form in which some entry is nonzero and is the only nonzero entry both in its row and in its
column.

The descent is on the order of the pivot: one round of right division clears the pivot column
against the pivot, one round of left division clears the pivot row, and the second round does not
disturb the pivot column because column operations only modify columns other than the pivot one.
If anything is left over, it has strictly smaller order and becomes the next pivot.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- One elementary move: a row operation or a column operation. -/
def RowColStep (P P' : ι → κ → DiffOp K) : Prop := RowStep P P' ∨ ColStep P P'

/-- Equivalence under finitely many elementary moves of either kind. -/
def RowColEquiv : (ι → κ → DiffOp K) → (ι → κ → DiffOp K) → Prop :=
  Relation.ReflTransGen RowColStep

theorem RowColEquiv.refl (P : ι → κ → DiffOp K) : RowColEquiv P P := Relation.ReflTransGen.refl

theorem RowColEquiv.trans {P Q S : ι → κ → DiffOp K} (h₁ : RowColEquiv P Q)
    (h₂ : RowColEquiv Q S) : RowColEquiv P S := Relation.ReflTransGen.trans h₁ h₂

theorem RowColEquiv.of_rowEquiv {P P' : ι → κ → DiffOp K} (h : RowEquiv P P') :
    RowColEquiv P P' := by
  induction h with
  | refl => exact RowColEquiv.refl P
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (Or.inl hstep)

theorem RowColEquiv.of_colEquiv {P P' : ι → κ → DiffOp K} (h : ColEquiv P P') :
    RowColEquiv P P' := by
  induction h with
  | refl => exact RowColEquiv.refl P
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (Or.inr hstep)

theorem RowColEquiv.rowIndep {P P' : ι → κ → DiffOp K} (h : RowColEquiv P P')
    (hP : RowIndep P) : RowIndep P' := by
  induction h with
  | refl => exact hP
  | tail _ hstep ih =>
    rcases hstep with hrow | hcol
    · exact hrow.rowIndep ih
    · obtain ⟨j₀, k, q, hne, rfl⟩ := hcol
      exact rowIndep_colAdd hne q ih

/-- **Simultaneous clearing.**  Some equivalent matrix has an entry that is the only nonzero entry
of its row and of its column. -/
theorem exists_pivot_clear_both :
    ∀ (n : ℕ) (P : ι → κ → DiffOp K) (i₀ : ι) (j₀ : κ), P i₀ j₀ ≠ 0 → degree (P i₀ j₀) ≤ n →
      ∃ (P' : ι → κ → DiffOp K) (i₁ : ι) (j₁ : κ), RowColEquiv P P' ∧ P' i₁ j₁ ≠ 0 ∧
        (∀ i, i ≠ i₁ → P' i j₁ = 0) ∧ (∀ j, j ≠ j₁ → P' i₁ j = 0) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro P i₀ j₀ hpiv hdeg
    -- one round of column clearing by row operations
    obtain ⟨P₁, hequiv₁, hfix₁, hlow₁⟩ := exists_reduce_column j₀ P i₀ hpiv
    have hpiv₁ : P₁ i₀ j₀ ≠ 0 := by rw [hfix₁]; exact hpiv
    -- one round of row clearing by column operations; it leaves the pivot column untouched
    obtain ⟨P₂, hequiv₂, hfix₂, hlow₂⟩ := exists_reduce_row i₀ j₀ P₁ hpiv₁
    have hpiv₂ : P₂ i₀ j₀ ≠ 0 := by rw [hfix₂]; exact hpiv₁
    have hequiv : RowColEquiv P P₂ :=
      (RowColEquiv.of_rowEquiv hequiv₁).trans (RowColEquiv.of_colEquiv hequiv₂)
    by_cases hcol : ∀ i, i ≠ i₀ → P₂ i j₀ = 0
    · by_cases hrow : ∀ j, j ≠ j₀ → P₂ i₀ j = 0
      · exact ⟨P₂, i₀, j₀, hequiv, hpiv₂, hcol, hrow⟩
      · -- a leftover entry in the pivot row has strictly smaller order
        obtain ⟨j, hjne, hjnz⟩ : ∃ j, j ≠ j₀ ∧ P₂ i₀ j ≠ 0 := by
          by_contra hcon
          exact hrow fun j hj => by
            by_contra hz
            exact hcon ⟨j, hj, hz⟩
        have hjlt : degree (P₂ i₀ j) < degree (P₁ i₀ j₀) := (hlow₂ j hjne).resolve_left hjnz
        have hjlt' : degree (P₂ i₀ j) < degree (P i₀ j₀) := by rw [← hfix₁]; exact hjlt
        obtain ⟨P₃, i₁, j₁, hequiv₃, hnz₃, hcol₃, hrow₃⟩ :=
          ih (degree (P₂ i₀ j)) (by omega) P₂ i₀ j hjnz le_rfl
        exact ⟨P₃, i₁, j₁, hequiv.trans hequiv₃, hnz₃, hcol₃, hrow₃⟩
    · -- a leftover entry in the pivot column has strictly smaller order
      obtain ⟨i, hine, hinz⟩ : ∃ i, i ≠ i₀ ∧ P₂ i j₀ ≠ 0 := by
        by_contra hcon
        exact hcol fun i hi => by
          by_contra hz
          exact hcon ⟨i, hi, hz⟩
      have hcolfix : P₂ i j₀ = P₁ i j₀ := by
        rw [← hfix₂]
        exact (congrFun (congrFun rfl i) j₀)
      have hilt : degree (P₂ i j₀) < degree (P i₀ j₀) := by
        rcases hlow₁ i hine with hzero | hlt
        · exact absurd (by rw [hcolfix, hzero]) hinz
        · rw [hcolfix]
          exact hlt
      obtain ⟨P₃, i₁, j₁, hequiv₃, hnz₃, hcol₃, hrow₃⟩ :=
        ih (degree (P₂ i j₀)) (by omega) P₂ i j₀ hinz le_rfl
      exact ⟨P₃, i₁, j₁, hequiv.trans hequiv₃, hnz₃, hcol₃, hrow₃⟩

end

end DiffOp

end GaloisForLFunctions.HTGeometry
