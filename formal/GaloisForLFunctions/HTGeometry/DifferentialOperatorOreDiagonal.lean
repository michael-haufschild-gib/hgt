import GaloisForLFunctions.HTGeometry.DifferentialOperatorOreReduction

/-!
# Diagonal form of a matrix over the operator ring

Every matrix over `K[∂;δ]` can be brought, by finitely many elementary row and column operations,
to a form in which every nonzero entry is the only nonzero entry of its row and of its column.

The proof is a recursion on the number of rows.  One application of simultaneous clearing produces
a nonzero pivot alone in its row and column; the complementary submatrix is diagonalized by the
recursion, and the resulting moves are lifted back to the whole matrix.  Lifting is possible
because a row operation among the complementary rows does not touch the pivot row and keeps the
cleared pivot column cleared, and symmetrically for column operations.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]

section Lift

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
/-- A matrix is in diagonal form when every nonzero entry is the only nonzero entry of its row and
of its column. -/
def Diagonalized (P : ι → κ → DiffOp K) : Prop :=
  ∀ i j, P i j ≠ 0 → (∀ i', i' ≠ i → P i' j = 0) ∧ (∀ j', j' ≠ j → P i j' = 0)

omit [Fintype ι] [Fintype κ] in
/-- **Lifting.**  An equivalence of the complementary submatrix lifts to an equivalence of the
whole matrix which leaves a cleared pivot row and column untouched. -/
theorem exists_lift_rowColEquiv {i₁ : ι} {j₁ : κ} {P : ι → κ → DiffOp K}
    (hcol : ∀ i, i ≠ i₁ → P i j₁ = 0) (hrow : ∀ j, j ≠ j₁ → P i₁ j = 0)
    {Q : {i : ι // i ≠ i₁} → {j : κ // j ≠ j₁} → DiffOp K}
    (h : RowColEquiv (restrictMat i₁ j₁ P) Q) :
    ∃ P' : ι → κ → DiffOp K, RowColEquiv P P' ∧ restrictMat i₁ j₁ P' = Q ∧
      P' i₁ j₁ = P i₁ j₁ ∧ (∀ i, i ≠ i₁ → P' i j₁ = 0) ∧ (∀ j, j ≠ j₁ → P' i₁ j = 0) := by
  induction h with
  | refl => exact ⟨P, RowColEquiv.refl P, rfl, rfl, hcol, hrow⟩
  | tail _ hstep ih =>
    obtain ⟨P', hPP', hres, hpiv, hcol', hrow'⟩ := ih
    rcases hstep with ⟨i, k, q, hne, rfl⟩ | ⟨j, k, q, hne, rfl⟩
    · refine ⟨rowAdd i.1 k.1 q P', Relation.ReflTransGen.tail hPP'
        (Or.inl ⟨i.1, k.1, q, fun hcon => hne (Subtype.ext hcon), rfl⟩), ?_, ?_, ?_, ?_⟩
      · rw [restrictMat_rowAdd, hres]
      · rw [rowAdd_pivot_row i.2 q P' j₁]
        exact hpiv
      · exact rowAdd_pivot_col k.2 hcol' q
      · intro a ha
        rw [rowAdd_pivot_row i.2 q P' a]
        exact hrow' a ha
    · refine ⟨colAdd j.1 k.1 q P', Relation.ReflTransGen.tail hPP'
        (Or.inr ⟨j.1, k.1, q, fun hcon => hne (Subtype.ext hcon), rfl⟩), ?_, ?_, ?_, ?_⟩
      · rw [restrictMat_colAdd, hres]
      · rw [colAdd_pivot_col j.2 q P' i₁]
        exact hpiv
      · intro a ha
        rw [colAdd_pivot_col j.2 q P' a]
        exact hcol' a ha
      · exact colAdd_pivot_row k.2 hrow' q

end Lift

section Recursion

/-- **Diagonal form**, by recursion on the number of rows. -/
theorem exists_diagonalized_of_card_le :
    ∀ (n : ℕ) {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
      (P : ι → κ → DiffOp K), Fintype.card ι ≤ n →
      ∃ P' : ι → κ → DiffOp K, RowColEquiv P P' ∧ Diagonalized P' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ι κ _ _ _ _ P hcard
    by_cases hall : ∃ i j, P i j ≠ 0
    · obtain ⟨i₀, j₀, hi₀⟩ := hall
      obtain ⟨P₂, i₁, j₁, hequiv, hnz, hcolclear, hrowclear⟩ :=
        exists_pivot_clear_both (degree (P i₀ j₀)) P i₀ j₀ hi₀ le_rfl
      have hcard' : Fintype.card {a : ι // a ≠ i₁} < n := by
        have hc : Fintype.card {a : ι // a ≠ i₁} = Fintype.card ι - 1 := by
          rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
        have hpos : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i₁⟩
        omega
      obtain ⟨Q, hQ, hQdiag⟩ := ih _ hcard' (restrictMat i₁ j₁ P₂) le_rfl
      obtain ⟨P₃, hP₂₃, hres, _, hcol₃, hrow₃⟩ :=
        exists_lift_rowColEquiv hcolclear hrowclear hQ
      refine ⟨P₃, hequiv.trans hP₂₃, ?_⟩
      intro i j hij
      by_cases hi : i = i₁
      · subst hi
        have hj : j = j₁ := by
          by_contra hjne
          exact hij (hrow₃ j hjne)
        subst hj
        exact ⟨hcol₃, hrow₃⟩
      · have hj : j ≠ j₁ := by
          intro hjeq
          subst hjeq
          exact hij (hcol₃ i hi)
        have hQij : Q ⟨i, hi⟩ ⟨j, hj⟩ ≠ 0 := by
          rw [← hres]
          exact hij
        obtain ⟨hQcol, hQrow⟩ := hQdiag ⟨i, hi⟩ ⟨j, hj⟩ hQij
        refine ⟨fun a ha => ?_, fun b hb => ?_⟩
        · by_cases hai : a = i₁
          · subst hai
            exact hrow₃ j hj
          · have hz := hQcol ⟨a, hai⟩ fun hcon => ha (congrArg Subtype.val hcon)
            rw [← hres] at hz
            exact hz
        · by_cases hbj : b = j₁
          · subst hbj
            exact hcol₃ i hi
          · have hz := hQrow ⟨b, hbj⟩ fun hcon => hb (congrArg Subtype.val hcon)
            rw [← hres] at hz
            exact hz
    · refine ⟨P, RowColEquiv.refl P, fun i j hij => ?_⟩
      exact absurd ⟨i, j, hij⟩ hall

/-- **Diagonal form.**  Every matrix over the operator ring is equivalent, under elementary row
and column operations, to one whose nonzero entries are alone in their row and column. -/
theorem exists_diagonalized {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (P : ι → κ → DiffOp K) :
    ∃ P' : ι → κ → DiffOp K, RowColEquiv P P' ∧ Diagonalized P' :=
  exists_diagonalized_of_card_le (Fintype.card ι) P le_rfl

end Recursion

end

end DiffOp

end GaloisForLFunctions.HTGeometry
