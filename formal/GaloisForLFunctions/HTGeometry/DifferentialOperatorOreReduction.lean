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

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
/-- One elementary move: a row operation or a column operation. -/
def RowColStep (P P' : ι → κ → DiffOp K) : Prop := RowStep P P' ∨ ColStep P P'

/-- Equivalence under finitely many elementary moves of either kind. -/
def RowColEquiv : (ι → κ → DiffOp K) → (ι → κ → DiffOp K) → Prop :=
  Relation.ReflTransGen RowColStep

omit [Fintype ι] [Fintype κ] in
theorem RowColEquiv.refl (P : ι → κ → DiffOp K) : RowColEquiv P P := Relation.ReflTransGen.refl

omit [Fintype ι] [Fintype κ] in
theorem RowColEquiv.trans {P Q S : ι → κ → DiffOp K} (h₁ : RowColEquiv P Q)
    (h₂ : RowColEquiv Q S) : RowColEquiv P S := Relation.ReflTransGen.trans h₁ h₂

omit [Fintype ι] [Fintype κ] in
theorem RowColEquiv.of_rowEquiv {P P' : ι → κ → DiffOp K} (h : RowEquiv P P') :
    RowColEquiv P P' := by
  induction h with
  | refl => exact RowColEquiv.refl P
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (Or.inl hstep)

omit [Fintype ι] [Fintype κ] in
theorem RowColEquiv.of_colEquiv {P P' : ι → κ → DiffOp K} (h : ColEquiv P P') :
    RowColEquiv P P' := by
  induction h with
  | refl => exact RowColEquiv.refl P
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (Or.inr hstep)

omit [Fintype κ] in
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
    have hpiv₂ : P₂ i₀ j₀ ≠ 0 := by rw [hfix₂ i₀]; exact hpiv₁
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
      have hcolfix : P₂ i j₀ = P₁ i j₀ := hfix₂ i
      have hilt : degree (P₂ i j₀) < degree (P i₀ j₀) := by
        rcases hlow₁ i hine with hzero | hlt
        · exact absurd (by rw [hcolfix, hzero]) hinz
        · rw [hcolfix]
          exact hlt
      obtain ⟨P₃, i₁, j₁, hequiv₃, hnz₃, hcol₃, hrow₃⟩ :=
        ih (degree (P₂ i j₀)) (by omega) P₂ i j₀ hinz le_rfl
      exact ⟨P₃, i₁, j₁, hequiv.trans hequiv₃, hnz₃, hcol₃, hrow₃⟩


section Lifting

variable {i₁ : ι} {j₁ : κ}

/-- The restriction of a matrix to the indices complementary to a pivot position. -/
def restrictMat (i₁ : ι) (j₁ : κ) (P : ι → κ → DiffOp K) :
    {i : ι // i ≠ i₁} → {j : κ // j ≠ j₁} → DiffOp K := fun i j => P i.1 j.1

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
@[simp] theorem restrictMat_apply (i₁ : ι) (j₁ : κ) (P : ι → κ → DiffOp K)
    (i : {i : ι // i ≠ i₁}) (j : {j : κ // j ≠ j₁}) :
    restrictMat i₁ j₁ P i j = P i.1 j.1 := rfl

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
/-- A row operation among the complementary rows restricts to the corresponding row operation. -/
theorem restrictMat_rowAdd (i k : {i : ι // i ≠ i₁}) (q : DiffOp K) (P : ι → κ → DiffOp K) :
    restrictMat i₁ j₁ (rowAdd i.1 k.1 q P) = rowAdd i k q (restrictMat i₁ j₁ P) := by
  funext a j
  by_cases ha : a = i
  · subst ha
    rw [restrictMat_apply, rowAdd_apply_self, rowAdd_apply_self, restrictMat_apply,
      restrictMat_apply]
  · have ha' : (a : ι) ≠ (i : ι) := fun hcon => ha (Subtype.ext hcon)
    rw [restrictMat_apply, rowAdd_apply_of_ne _ q P _ ha', rowAdd_apply_of_ne _ q _ _ ha,
      restrictMat_apply]

omit [Fintype ι] [Fintype κ] [DecidableEq ι] in
/-- A column operation among the complementary columns restricts likewise. -/
theorem restrictMat_colAdd (j k : {j : κ // j ≠ j₁}) (q : DiffOp K) (P : ι → κ → DiffOp K) :
    restrictMat i₁ j₁ (colAdd j.1 k.1 q P) = colAdd j k q (restrictMat i₁ j₁ P) := by
  funext i a
  by_cases ha : a = j
  · subst ha
    rw [restrictMat_apply, colAdd_apply_self, colAdd_apply_self, restrictMat_apply,
      restrictMat_apply]
  · have ha' : (a : κ) ≠ (j : κ) := fun hcon => ha (Subtype.ext hcon)
    rw [restrictMat_apply, colAdd_apply_of_ne _ q P _ ha', colAdd_apply_of_ne _ q _ _ ha,
      restrictMat_apply]

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
/-- A row operation among the complementary rows leaves the pivot row untouched. -/
theorem rowAdd_pivot_row {i k : ι} (hi : i ≠ i₁) (q : DiffOp K) (P : ι → κ → DiffOp K) (j : κ) :
    rowAdd i k q P i₁ j = P i₁ j := rowAdd_apply_of_ne k q P j (fun hcon => hi hcon.symm)

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
/-- A row operation among the complementary rows keeps a cleared pivot column cleared. -/
theorem rowAdd_pivot_col {i k : ι} (hk : k ≠ i₁) {P : ι → κ → DiffOp K}
    (hclear : ∀ a, a ≠ i₁ → P a j₁ = 0) (q : DiffOp K) :
    ∀ a, a ≠ i₁ → rowAdd i k q P a j₁ = 0 := by
  intro a ha
  by_cases hai : a = i
  · subst hai
    rw [rowAdd_apply_self, hclear a ha, hclear k hk, mul_zero, add_zero]
  · rw [rowAdd_apply_of_ne k q P j₁ hai]
    exact hclear a ha

omit [Fintype ι] [Fintype κ] [DecidableEq ι] in
/-- A column operation among the complementary columns leaves the pivot column untouched. -/
theorem colAdd_pivot_col {j k : κ} (hj : j ≠ j₁) (q : DiffOp K) (P : ι → κ → DiffOp K) (i : ι) :
    colAdd j k q P i j₁ = P i j₁ := colAdd_apply_of_ne k q P i (fun hcon => hj hcon.symm)

omit [Fintype ι] [Fintype κ] [DecidableEq ι] in
/-- A column operation among the complementary columns keeps a cleared pivot row cleared. -/
theorem colAdd_pivot_row {j k : κ} (hk : k ≠ j₁) {P : ι → κ → DiffOp K}
    (hclear : ∀ a, a ≠ j₁ → P i₁ a = 0) (q : DiffOp K) :
    ∀ a, a ≠ j₁ → colAdd j k q P i₁ a = 0 := by
  intro a ha
  by_cases haj : a = j
  · subst haj
    rw [colAdd_apply_self, hclear a ha, hclear k hk, zero_mul, add_zero]
  · rw [colAdd_apply_of_ne k q P i₁ haj]
    exact hclear a ha

end Lifting

end

end DiffOp

end GaloisForLFunctions.HTGeometry
