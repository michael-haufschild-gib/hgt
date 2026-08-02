import GaloisForLFunctions.HTGeometry.DifferentialOperatorOreMatrix

/-!
# Column operations on operator matrices

Column operations multiply an operator matrix on the right by an elementary matrix.  Unlike row
operations they leave the coefficient vector untouched and act on the result instead:

`v · (P U) = (v · P) · U`.

Their inverses are again column operations, so both the independence of the rows and the bounded
distortion of the row map are unchanged by them.  Together with the row operations of
`DifferentialOperatorOreMatrix.lean` they are the moves of the diagonal reduction.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]

section ColumnOps

variable {ι κ : Type*} [Fintype ι] [DecidableEq κ]

/-- The column operation `colⱼ₀ ← colⱼ₀ + colₖ · q`. -/
def colAdd (j₀ k : κ) (q : DiffOp K) (P : ι → κ → DiffOp K) : ι → κ → DiffOp K :=
  fun i j => if j = j₀ then P i j₀ + P i k * q else P i j

/-- The matching operation on a row vector. -/
def colAddVec (j₀ k : κ) (q : DiffOp K) (w : κ → DiffOp K) : κ → DiffOp K :=
  fun j => if j = j₀ then w j₀ + w k * q else w j

omit [Fintype ι] in
theorem colAdd_apply_self (j₀ k : κ) (q : DiffOp K) (P : ι → κ → DiffOp K) (i : ι) :
    colAdd j₀ k q P i j₀ = P i j₀ + P i k * q := by
  simp [colAdd]

omit [Fintype ι] in
theorem colAdd_apply_of_ne {j j₀ : κ} (k : κ) (q : DiffOp K) (P : ι → κ → DiffOp K) (i : ι)
    (h : j ≠ j₀) : colAdd j₀ k q P i j = P i j := by
  simp only [colAdd, if_neg h]

theorem colAddVec_apply_self (j₀ k : κ) (q : DiffOp K) (w : κ → DiffOp K) :
    colAddVec j₀ k q w j₀ = w j₀ + w k * q := by
  simp [colAddVec]

theorem colAddVec_apply_of_ne (j₀ k : κ) (q : DiffOp K) (w : κ → DiffOp K) {j : κ}
    (h : j ≠ j₀) : colAddVec j₀ k q w j = w j := by
  simp only [colAddVec, if_neg h]

/-- A column operation acts on the result of the row map. -/
theorem vecMul_colAdd (j₀ k : κ) (q : DiffOp K) (P : ι → κ → DiffOp K) (v : ι → DiffOp K) :
    vecMul v (colAdd j₀ k q P) = colAddVec j₀ k q (vecMul v P) := by
  funext j
  by_cases hj : j = j₀
  · subst hj
    rw [colAddVec_apply_self]
    show ∑ i, v i * colAdd j k q P i j = (∑ i, v i * P i j) + (∑ i, v i * P i k) * q
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [colAdd_apply_self, mul_add, mul_assoc]
  · rw [colAddVec_apply_of_ne _ _ _ _ hj]
    show ∑ i, v i * colAdd j₀ k q P i j = ∑ i, v i * P i j
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [colAdd_apply_of_ne k q P i hj]

theorem colAddVec_cancel {j₀ k : κ} (h : j₀ ≠ k) (q : DiffOp K) (w : κ → DiffOp K) :
    colAddVec j₀ k (-q) (colAddVec j₀ k q w) = w := by
  funext j
  by_cases hj : j = j₀
  · subst hj
    rw [colAddVec_apply_self, colAddVec_apply_self,
      colAddVec_apply_of_ne j k q w (Ne.symm h), mul_neg]
    abel
  · rw [colAddVec_apply_of_ne _ _ _ _ hj, colAddVec_apply_of_ne _ _ _ _ hj]

theorem degVec_colAddVec_le [Fintype κ] (j₀ k : κ) (q : DiffOp K) (w : κ → DiffOp K) :
    degVec (colAddVec j₀ k q w) ≤ degVec w + degree q := by
  refine degVec_le_iff.mpr fun j => ?_
  by_cases hj : j = j₀
  · subst hj
    rw [colAddVec_apply_self]
    refine le_trans (degree_add_le (w j) (w k * q)) (max_le ?_ ?_)
    · exact le_trans (degree_le_degVec w j) (Nat.le_add_right _ _)
    · exact le_trans (degree_mul_le (w k) q)
        (Nat.add_le_add_right (degree_le_degVec w k) (degree q))
  · rw [colAddVec_apply_of_ne _ _ _ _ hj]
    exact le_trans (degree_le_degVec w j) (Nat.le_add_right _ _)

omit [Fintype ι] in
theorem colAdd_cancel {j₀ k : κ} (h : j₀ ≠ k) (q : DiffOp K) (P : ι → κ → DiffOp K) :
    colAdd j₀ k (-q) (colAdd j₀ k q P) = P := by
  funext i j
  by_cases hj : j = j₀
  · subst hj
    rw [colAdd_apply_self, colAdd_apply_self, colAdd_apply_of_ne k q P i (Ne.symm h), mul_neg]
    abel
  · rw [colAdd_apply_of_ne _ _ _ _ hj, colAdd_apply_of_ne _ _ _ _ hj]

/-- Column operations preserve independence of the rows. -/
theorem rowIndep_colAdd {j₀ k : κ} (h : j₀ ≠ k) (q : DiffOp K) {P : ι → κ → DiffOp K}
    (hP : RowIndep P) : RowIndep (colAdd j₀ k q P) := by
  intro v hv
  refine hP v ?_
  have hcol : colAddVec j₀ k q (vecMul v P) = 0 := by
    rw [← vecMul_colAdd]
    exact hv
  have hcancel := colAddVec_cancel h q (vecMul v P)
  rw [hcol] at hcancel
  rw [← hcancel]
  funext j
  by_cases hj : j = j₀ <;> simp [colAddVec, hj]

/-- Column operations preserve bounded distortion. -/
theorem boundedDistortion_colAdd [Fintype κ] {j₀ k : κ} (h : j₀ ≠ k) (q : DiffOp K)
    {P : ι → κ → DiffOp K} (hP : BoundedDistortion P) :
    BoundedDistortion (colAdd j₀ k q P) := by
  obtain ⟨B, hB⟩ := hP
  refine ⟨B + degree q, fun v => ?_⟩
  have hcol : vecMul v (colAdd j₀ k q P) = colAddVec j₀ k q (vecMul v P) := vecMul_colAdd _ _ _ _ _
  have h₁ : degVec v ≤ degVec (vecMul v P) + B := hB v
  have h₃ : degVec (vecMul v P) ≤ degVec (colAddVec j₀ k q (vecMul v P)) + degree q := by
    have hc := colAddVec_cancel h q (vecMul v P)
    have hle := degVec_colAddVec_le j₀ k (-q) (colAddVec j₀ k q (vecMul v P))
    rw [hc, degree_neg] at hle
    exact hle
  rw [hcol]
  omega


/-- One elementary column operation. -/
def ColStep (P P' : ι → κ → DiffOp K) : Prop :=
  ∃ (j₀ k : κ) (q : DiffOp K), j₀ ≠ k ∧ P' = colAdd j₀ k q P

/-- Equivalence of matrices under finitely many elementary column operations. -/
def ColEquiv : (ι → κ → DiffOp K) → (ι → κ → DiffOp K) → Prop := Relation.ReflTransGen ColStep

omit [Fintype ι] in
theorem ColEquiv.refl (P : ι → κ → DiffOp K) : ColEquiv P P := Relation.ReflTransGen.refl

omit [Fintype ι] in
theorem ColEquiv.tail {P Q P' : ι → κ → DiffOp K} (h : ColEquiv P Q) (hstep : ColStep Q P') :
    ColEquiv P P' := Relation.ReflTransGen.tail h hstep

omit [Fintype ι] in
theorem ColEquiv.trans {P Q S : ι → κ → DiffOp K} (h₁ : ColEquiv P Q) (h₂ : ColEquiv Q S) :
    ColEquiv P S := Relation.ReflTransGen.trans h₁ h₂

theorem ColEquiv.rowIndep {P P' : ι → κ → DiffOp K} (h : ColEquiv P P') (hP : RowIndep P) :
    RowIndep P' := by
  induction h with
  | refl => exact hP
  | tail _ hstep ih =>
    obtain ⟨j₀, k, q, hne, rfl⟩ := hstep
    exact rowIndep_colAdd hne q ih

theorem ColEquiv.boundedDistortion [Fintype κ] {P P' : ι → κ → DiffOp K} (h : ColEquiv P P')
    (hP : BoundedDistortion P) : BoundedDistortion P' := by
  induction h with
  | refl => exact hP
  | tail _ hstep ih =>
    obtain ⟨j₀, k, q, hne, rfl⟩ := hstep
    exact boundedDistortion_colAdd hne q ih

omit [Fintype ι] in
/-- Left division against a pivot lowers every other entry of a row below the pivot order. -/
theorem exists_reduce_row [Fintype κ] (i₀ : ι) (j₀ : κ) (P : ι → κ → DiffOp K)
    (hpiv : P i₀ j₀ ≠ 0) :
    ∃ P' : ι → κ → DiffOp K, ColEquiv P P' ∧ P' i₀ j₀ = P i₀ j₀ ∧
      ∀ j, j ≠ j₀ → (P' i₀ j = 0 ∨ degree (P' i₀ j) < degree (P i₀ j₀)) := by
  classical
  have key : ∀ T : Finset κ, j₀ ∉ T →
      ∃ P' : ι → κ → DiffOp K, ColEquiv P P' ∧ (∀ j, j ∉ T → P' i₀ j = P i₀ j) ∧
        ∀ j ∈ T, (P' i₀ j = 0 ∨ degree (P' i₀ j) < degree (P i₀ j₀)) := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact fun _ => ⟨P, ColEquiv.refl P, fun _ _ => rfl, fun j hj => absurd hj (by simp)⟩
    | insert a T ha ih =>
      intro hnot
      have hj₀T : j₀ ∉ T := fun h => hnot (Finset.mem_insert_of_mem h)
      have haj₀ : a ≠ j₀ := fun h => hnot (h ▸ Finset.mem_insert_self a T)
      obtain ⟨P₁, hequiv, hout, hin⟩ := ih hj₀T
      have hpiv₁ : P₁ i₀ j₀ = P i₀ j₀ := hout j₀ hj₀T
      obtain ⟨q, r, hqr, hr⟩ := exists_left_div (b := P₁ i₀ j₀) (by rw [hpiv₁]; exact hpiv)
        (P₁ i₀ a)
      refine ⟨colAdd a j₀ (-q) P₁, hequiv.tail ⟨a, j₀, -q, haj₀, rfl⟩, ?_, ?_⟩
      · intro j hj
        have hja : j ≠ a := fun h => hj (h ▸ Finset.mem_insert_self a T)
        have hjT : j ∉ T := fun h => hj (Finset.mem_insert_of_mem h)
        rw [colAdd_apply_of_ne j₀ (-q) P₁ i₀ hja]
        exact hout j hjT
      · intro j hj
        by_cases hja : j = a
        · subst hja
          have hval : colAdd j j₀ (-q) P₁ i₀ j = r := by
            rw [colAdd_apply_self, hqr, mul_neg]
            abel
          rw [hval, ← hpiv₁]
          exact hr
        · have hjT : j ∈ T := (Finset.mem_insert.mp hj).resolve_left hja
          rw [colAdd_apply_of_ne j₀ (-q) P₁ i₀ hja]
          exact hin j hjT
  obtain ⟨P', hequiv, hout, hin⟩ := key (Finset.univ.erase j₀) (Finset.notMem_erase j₀ _)
  refine ⟨P', hequiv, hout j₀ (Finset.notMem_erase j₀ _), fun j hj => hin j ?_⟩
  exact Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩

omit [Fintype ι] in
/-- A row with a nonzero entry can be cleared to a single pivot by column operations. -/
theorem exists_pivot_clear_row [Fintype κ] (i₀ : ι) :
    ∀ (n : ℕ) (P : ι → κ → DiffOp K) (j₀ : κ), P i₀ j₀ ≠ 0 → degree (P i₀ j₀) ≤ n →
      ∃ (P' : ι → κ → DiffOp K) (j₁ : κ), ColEquiv P P' ∧ P' i₀ j₁ ≠ 0 ∧
        ∀ j, j ≠ j₁ → P' i₀ j = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro P j₀ hpiv hdeg
    obtain ⟨P₁, hequiv, hfix, hlow⟩ := exists_reduce_row i₀ j₀ P hpiv
    by_cases hall : ∀ j, j ≠ j₀ → P₁ i₀ j = 0
    · exact ⟨P₁, j₀, hequiv, by rw [hfix]; exact hpiv, hall⟩
    · obtain ⟨k, hkj₀, hknz⟩ : ∃ k, k ≠ j₀ ∧ P₁ i₀ k ≠ 0 := by
        by_contra hcon
        exact hall fun j hj => by
          by_contra hz
          exact hcon ⟨j, hj, hz⟩
      have hklt : degree (P₁ i₀ k) < degree (P i₀ j₀) := (hlow k hkj₀).resolve_left hknz
      obtain ⟨P₂, j₁, hequiv₂, hnz₂, hclear₂⟩ :=
        ih (degree (P₁ i₀ k)) (by omega) P₁ k hknz le_rfl
      exact ⟨P₂, j₁, hequiv.trans hequiv₂, hnz₂, hclear₂⟩

end ColumnOps

end

end DiffOp

end GaloisForLFunctions.HTGeometry
