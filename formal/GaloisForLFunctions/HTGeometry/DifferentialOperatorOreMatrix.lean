import GaloisForLFunctions.HTGeometry.DifferentialOperatorOreDivision
import Mathlib.Tactic.NoncommRing

/-!
# Bounded distortion for operator matrices

Let `R = K[∂;δ]` be the Ore ring of linear differential operators over a differential field and let
`P` be a matrix over `R` whose rows are left linearly independent, i.e. `v · P = 0` forces `v = 0`.

The main theorem is that the injection `v ↦ v · P` distorts orders by at most an additive
constant:

`degVec v ≤ degVec (v · P) + B`.

Over the skew field of rational pseudodifferential operators this is the existence of a right
inverse `Q` with `P Q = 1` together with subadditivity of the order under matrix multiplication.
The proof given here stays inside `R`: an elementary row operation `rowᵢ ← rowᵢ + q · rowₖ`
changes the coefficient vector by a bounded amount in both directions, since its inverse is the
same operation with `-q`.  Division with remainder clears one column after finitely many such
operations, and the pivot row is then peeled off.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]

section Vectors

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The maximal order of a finite family of operators. -/
def degVec (v : ι → DiffOp K) : ℕ := Finset.univ.sup fun i => degree (v i)

theorem degree_le_degVec (v : ι → DiffOp K) (i : ι) : degree (v i) ≤ degVec v :=
  Finset.le_sup (f := fun i => degree (v i)) (Finset.mem_univ i)

theorem degVec_le_iff {v : ι → DiffOp K} {n : ℕ} : degVec v ≤ n ↔ ∀ i, degree (v i) ≤ n :=
  ⟨fun h i => le_trans (degree_le_degVec v i) h, fun h => Finset.sup_le fun i _ => h i⟩

@[simp] theorem degVec_zero : degVec (0 : ι → DiffOp K) = 0 :=
  le_antisymm (degVec_le_iff.mpr fun i => by rw [Pi.zero_apply, degree_zero]) (Nat.zero_le _)

omit [Fintype ι] in
theorem degree_sum_le (s : Finset ι) (f : ι → DiffOp K) :
    degree (∑ i ∈ s, f i) ≤ s.sup fun i => degree (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sup_insert]
    exact le_trans (degree_add_le _ _) (max_le_max le_rfl ih)

/-- Two sums whose summands agree off one index differ by the difference at that index. -/
theorem sum_eq_of_eq_except [DecidableEq ι] (f g : ι → DiffOp K) (a : ι)
    (h : ∀ i, i ≠ a → f i = g i) : ∑ i, f i = (∑ i, g i) + (f a - g a) := by
  rw [← Finset.add_sum_erase _ f (Finset.mem_univ a),
    ← Finset.add_sum_erase _ g (Finset.mem_univ a),
    Finset.sum_congr rfl fun i hi => h i (Finset.ne_of_mem_erase hi)]
  abel

/-- Left multiplication of a row vector by a matrix. -/
def vecMul (v : ι → DiffOp K) (P : ι → κ → DiffOp K) : κ → DiffOp K :=
  fun j => ∑ i, v i * P i j

/-- The maximal order of the entries of a matrix. -/
def matDeg (P : ι → κ → DiffOp K) : ℕ := Finset.univ.sup fun i => degVec (P i)

theorem degree_le_matDeg (P : ι → κ → DiffOp K) (i : ι) (j : κ) :
    degree (P i j) ≤ matDeg P :=
  le_trans (degree_le_degVec (P i) j)
    (Finset.le_sup (f := fun i => degVec (P i)) (Finset.mem_univ i))

theorem degVec_vecMul_le (v : ι → DiffOp K) (P : ι → κ → DiffOp K) :
    degVec (vecMul v P) ≤ degVec v + matDeg P := by
  refine degVec_le_iff.mpr fun j => ?_
  refine le_trans (degree_sum_le _ _) (Finset.sup_le fun i _ => ?_)
  exact le_trans (degree_mul_le _ _)
    (Nat.add_le_add (degree_le_degVec v i) (degree_le_matDeg P i j))

omit [Fintype κ] in
@[simp] theorem vecMul_zero (P : ι → κ → DiffOp K) : vecMul (0 : ι → DiffOp K) P = 0 := by
  funext j
  simp only [vecMul, Pi.zero_apply, zero_mul, Finset.sum_const_zero]

/-- The rows of `P` are left linearly independent. -/
def RowIndep (P : ι → κ → DiffOp K) : Prop := ∀ v : ι → DiffOp K, vecMul v P = 0 → v = 0

/-- The coefficient vector is recovered from its image with a bounded loss of order. -/
def BoundedDistortion (P : ι → κ → DiffOp K) : Prop :=
  ∃ B : ℕ, ∀ v : ι → DiffOp K, degVec v ≤ degVec (vecMul v P) + B

end Vectors

section RowOps

variable {ι κ : Type*} [DecidableEq ι]

/-- The row operation `rowᵢ₀ ← rowᵢ₀ + q · rowₖ`. -/
def rowAdd (i₀ k : ι) (q : DiffOp K) (P : ι → κ → DiffOp K) : ι → κ → DiffOp K :=
  fun i j => if i = i₀ then P i₀ j + q * P k j else P i j

/-- The matching change of coefficient vector, in the `k`-th slot. -/
def rowAddVec (i₀ k : ι) (q : DiffOp K) (v : ι → DiffOp K) : ι → DiffOp K :=
  fun i => if i = k then v k + v i₀ * q else v i

theorem rowAdd_apply_self (i₀ k : ι) (q : DiffOp K) (P : ι → κ → DiffOp K) (j : κ) :
    rowAdd i₀ k q P i₀ j = P i₀ j + q * P k j := by
  simp [rowAdd]

theorem rowAdd_apply_of_ne {i i₀ : ι} (k : ι) (q : DiffOp K) (P : ι → κ → DiffOp K) (j : κ)
    (h : i ≠ i₀) : rowAdd i₀ k q P i j = P i j := by
  simp only [rowAdd, if_neg h]

theorem rowAddVec_apply_self (i₀ k : ι) (q : DiffOp K) (v : ι → DiffOp K) :
    rowAddVec i₀ k q v k = v k + v i₀ * q := by
  simp [rowAddVec]

theorem rowAddVec_apply_of_ne (i₀ k : ι) (q : DiffOp K) (v : ι → DiffOp K) {i : ι}
    (h : i ≠ k) : rowAddVec i₀ k q v i = v i := by
  simp only [rowAddVec, if_neg h]

@[simp] theorem rowAddVec_zero (i₀ k : ι) (q : DiffOp K) :
    rowAddVec i₀ k q (0 : ι → DiffOp K) = 0 := by
  funext i
  by_cases hi : i = k
  · subst hi
    rw [rowAddVec_apply_self]
    simp
  · rw [rowAddVec_apply_of_ne i₀ k q 0 hi]

theorem rowAddVec_cancel {i₀ k : ι} (h : i₀ ≠ k) (q : DiffOp K) (v : ι → DiffOp K) :
    rowAddVec i₀ k (-q) (rowAddVec i₀ k q v) = v := by
  funext i
  by_cases hi : i = k
  · subst hi
    rw [rowAddVec_apply_self, rowAddVec_apply_self, rowAddVec_apply_of_ne i₀ i q v h, mul_neg]
    abel
  · rw [rowAddVec_apply_of_ne i₀ k (-q) _ hi, rowAddVec_apply_of_ne i₀ k q v hi]

variable [Fintype ι]

theorem degVec_rowAddVec_le (i₀ k : ι) (q : DiffOp K) (v : ι → DiffOp K) :
    degVec (rowAddVec i₀ k q v) ≤ degVec v + degree q := by
  refine degVec_le_iff.mpr fun i => ?_
  by_cases hi : i = k
  · subst hi
    rw [rowAddVec_apply_self]
    refine le_trans (degree_add_le (v i) (v i₀ * q)) (max_le ?_ ?_)
    · exact le_trans (degree_le_degVec v i) (Nat.le_add_right _ _)
    · exact le_trans (degree_mul_le (v i₀) q)
        (Nat.add_le_add_right (degree_le_degVec v i₀) (degree q))
  · rw [rowAddVec_apply_of_ne i₀ k q v hi]
    exact le_trans (degree_le_degVec v i) (Nat.le_add_right _ _)

theorem vecMul_rowAdd (i₀ k : ι) (q : DiffOp K) (P : ι → κ → DiffOp K)
    (v : ι → DiffOp K) :
    vecMul v (rowAdd i₀ k q P) = vecMul (rowAddVec i₀ k q v) P := by
  funext j
  have hleft : ∑ i, v i * (rowAdd i₀ k q P) i j
      = (∑ i, v i * P i j) + (v i₀ * (P i₀ j + q * P k j) - v i₀ * P i₀ j) := by
    have := sum_eq_of_eq_except (fun i => v i * (rowAdd i₀ k q P) i j)
      (fun i => v i * P i j) i₀ (fun i hi => by rw [rowAdd_apply_of_ne k q P j hi])
    rwa [rowAdd_apply_self] at this
  have hright : ∑ i, (rowAddVec i₀ k q v) i * P i j
      = (∑ i, v i * P i j) + ((v k + v i₀ * q) * P k j - v k * P k j) := by
    have := sum_eq_of_eq_except (fun i => (rowAddVec i₀ k q v) i * P i j)
      (fun i => v i * P i j) k (fun i hi => by rw [rowAddVec_apply_of_ne i₀ k q v hi])
    rwa [rowAddVec_apply_self] at this
  show ∑ i, v i * (rowAdd i₀ k q P) i j = ∑ i, (rowAddVec i₀ k q v) i * P i j
  rw [hleft, hright]
  noncomm_ring

omit [Fintype ι] in
theorem rowAdd_cancel {i₀ k : ι} (h : i₀ ≠ k) (q : DiffOp K) (P : ι → κ → DiffOp K) :
    rowAdd i₀ k (-q) (rowAdd i₀ k q P) = P := by
  funext i j
  by_cases hi : i = i₀
  · subst hi
    rw [rowAdd_apply_self, rowAdd_apply_self, rowAdd_apply_of_ne k q P j (Ne.symm h), neg_mul]
    abel
  · rw [rowAdd_apply_of_ne k (-q) _ j hi, rowAdd_apply_of_ne k q P j hi]

omit [Fintype ι] in
theorem rowStep_placeholder : True := trivial

/-- One elementary row operation. -/
def RowStep (P P' : ι → κ → DiffOp K) : Prop :=
  ∃ (i₀ k : ι) (q : DiffOp K), i₀ ≠ k ∧ P' = rowAdd i₀ k q P

theorem RowStep.rowIndep {P P' : ι → κ → DiffOp K} (hstep : RowStep P P')
    (hP : RowIndep P) : RowIndep P' := by
  obtain ⟨i₀, k, q, hne, rfl⟩ := hstep
  intro v hv
  rw [vecMul_rowAdd] at hv
  have h0 := hP _ hv
  have hc := rowAddVec_cancel hne q v
  rw [h0, rowAddVec_zero] at hc
  exact hc.symm

variable [Fintype κ]

theorem RowStep.boundedDistortion {P P' : ι → κ → DiffOp K} (hstep : RowStep P P')
    (hP' : BoundedDistortion P') : BoundedDistortion P := by
  obtain ⟨i₀, k, q, hne, rfl⟩ := hstep
  obtain ⟨B, hB⟩ := hP'
  refine ⟨B + degree q, fun v => ?_⟩
  have hround : rowAddVec i₀ k q (rowAddVec i₀ k (-q) v) = v := by
    have hc := rowAddVec_cancel (q := -q) hne v
    rwa [neg_neg] at hc
  have himg : vecMul (rowAddVec i₀ k (-q) v) (rowAdd i₀ k q P) = vecMul v P := by
    rw [vecMul_rowAdd, hround]
  have h₁ : degVec (rowAddVec i₀ k (-q) v) ≤ degVec (vecMul v P) + B := by
    have hb := hB (rowAddVec i₀ k (-q) v)
    rwa [himg] at hb
  have h₂ : degVec v ≤ degVec (rowAddVec i₀ k (-q) v) + degree q := by
    conv_lhs => rw [← hround]
    exact degVec_rowAddVec_le i₀ k q (rowAddVec i₀ k (-q) v)
  omega

/-- Equivalence of matrices under finitely many elementary row operations. -/
def RowEquiv : (ι → κ → DiffOp K) → (ι → κ → DiffOp K) → Prop := Relation.ReflTransGen RowStep

omit [Fintype ι] [Fintype κ] in
theorem RowEquiv.refl (P : ι → κ → DiffOp K) : RowEquiv P P := Relation.ReflTransGen.refl

omit [Fintype ι] [Fintype κ] in
theorem RowEquiv.tail {P Q P' : ι → κ → DiffOp K} (h : RowEquiv P Q) (hstep : RowStep Q P') :
    RowEquiv P P' := Relation.ReflTransGen.tail h hstep

omit [Fintype ι] [Fintype κ] in
theorem RowEquiv.trans {P Q S : ι → κ → DiffOp K} (h₁ : RowEquiv P Q) (h₂ : RowEquiv Q S) :
    RowEquiv P S := Relation.ReflTransGen.trans h₁ h₂

omit [Fintype κ] in
theorem RowEquiv.rowIndep {P P' : ι → κ → DiffOp K} (h : RowEquiv P P') (hP : RowIndep P) :
    RowIndep P' := by
  induction h with
  | refl => exact hP
  | tail _ hstep ih => exact hstep.rowIndep ih

theorem RowEquiv.boundedDistortion {P P' : ι → κ → DiffOp K} (h : RowEquiv P P')
    (hP' : BoundedDistortion P') : BoundedDistortion P := by
  induction h with
  | refl => exact hP'
  | tail _ hstep ih => exact ih (hstep.boundedDistortion hP')

end RowOps

section Clearing

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]

/-- Division against a pivot lowers every other entry of a column below the pivot order. -/
theorem exists_reduce_column (j₀ : κ) (P : ι → κ → DiffOp K) (i₀ : ι)
    (hpiv : P i₀ j₀ ≠ 0) :
    ∃ P' : ι → κ → DiffOp K, RowEquiv P P' ∧ P' i₀ j₀ = P i₀ j₀ ∧
      ∀ i, i ≠ i₀ → (P' i j₀ = 0 ∨ degree (P' i j₀) < degree (P i₀ j₀)) := by
  classical
  have key : ∀ T : Finset ι, i₀ ∉ T →
      ∃ P' : ι → κ → DiffOp K, RowEquiv P P' ∧ (∀ i, i ∉ T → P' i j₀ = P i j₀) ∧
        ∀ i ∈ T, (P' i j₀ = 0 ∨ degree (P' i j₀) < degree (P i₀ j₀)) := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact fun _ => ⟨P, RowEquiv.refl P, fun _ _ => rfl, fun i hi => absurd hi (by simp)⟩
    | insert a T ha ih =>
      intro hnot
      have hi₀T : i₀ ∉ T := fun h => hnot (Finset.mem_insert_of_mem h)
      have hai₀ : a ≠ i₀ := fun h => hnot (h ▸ Finset.mem_insert_self a T)
      obtain ⟨P₁, hequiv, hout, hin⟩ := ih hi₀T
      have hpiv₁ : P₁ i₀ j₀ = P i₀ j₀ := hout i₀ hi₀T
      obtain ⟨q, r, hqr, hr⟩ := exists_right_div (b := P₁ i₀ j₀) (by rw [hpiv₁]; exact hpiv)
        (P₁ a j₀)
      refine ⟨rowAdd a i₀ (-q) P₁, hequiv.tail ⟨a, i₀, -q, hai₀, rfl⟩, ?_, ?_⟩
      · intro i hi
        have hia : i ≠ a := fun h => hi (h ▸ Finset.mem_insert_self a T)
        have hiT : i ∉ T := fun h => hi (Finset.mem_insert_of_mem h)
        rw [rowAdd_apply_of_ne i₀ (-q) P₁ j₀ hia]
        exact hout i hiT
      · intro i hi
        by_cases hia : i = a
        · subst hia
          have hval : rowAdd i i₀ (-q) P₁ i j₀ = r := by
            rw [rowAdd_apply_self, hqr, neg_mul]
            abel
          rw [hval, ← hpiv₁]
          exact hr
        · have hiT : i ∈ T := (Finset.mem_insert.mp hi).resolve_left hia
          rw [rowAdd_apply_of_ne i₀ (-q) P₁ j₀ hia]
          exact hin i hiT
  obtain ⟨P', hequiv, hout, hin⟩ := key (Finset.univ.erase i₀) (Finset.notMem_erase i₀ _)
  refine ⟨P', hequiv, hout i₀ (Finset.notMem_erase i₀ _), fun i hi => hin i ?_⟩
  exact Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩

/-- A column with a nonzero entry can be cleared to a single pivot. -/
theorem exists_pivot_clear (j₀ : κ) :
    ∀ (n : ℕ) (P : ι → κ → DiffOp K) (i₀ : ι), P i₀ j₀ ≠ 0 → degree (P i₀ j₀) ≤ n →
      ∃ (P' : ι → κ → DiffOp K) (i₁ : ι), RowEquiv P P' ∧ P' i₁ j₀ ≠ 0 ∧
        ∀ i, i ≠ i₁ → P' i j₀ = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro P i₀ hpiv hdeg
    obtain ⟨P₁, hequiv, hfix, hlow⟩ := exists_reduce_column j₀ P i₀ hpiv
    by_cases hall : ∀ i, i ≠ i₀ → P₁ i j₀ = 0
    · exact ⟨P₁, i₀, hequiv, by rw [hfix]; exact hpiv, hall⟩
    · obtain ⟨k, hki₀, hknz⟩ : ∃ k, k ≠ i₀ ∧ P₁ k j₀ ≠ 0 := by
        by_contra hcon
        exact hall fun i hi => by
          by_contra hz
          exact hcon ⟨i, hi, hz⟩
      have hklt : degree (P₁ k j₀) < degree (P i₀ j₀) := (hlow k hki₀).resolve_left hknz
      obtain ⟨P₂, i₁, hequiv₂, hnz₂, hclear₂⟩ :=
        ih (degree (P₁ k j₀)) (by omega) P₁ k hknz le_rfl
      exact ⟨P₂, i₁, hequiv.trans hequiv₂, hnz₂, hclear₂⟩

end Clearing

section Main

variable {κ : Type*} [Fintype κ]

/-- **Bounded distortion.**  If the rows of `P` are left linearly independent over the operator
ring, then the order of a coefficient vector is bounded by the order of the corresponding
combination of rows, up to a constant depending only on `P`. -/
theorem boundedDistortion_of_rowIndep :
    ∀ (n : ℕ) {ι : Type v} [Fintype ι] [DecidableEq ι] (P : ι → κ → DiffOp K),
      Fintype.card ι ≤ n → RowIndep P → BoundedDistortion P := by
  intro n
  induction n with
  | zero =>
    intro ι _ _ P hcard _
    have hempty : IsEmpty ι := Fintype.card_eq_zero_iff.mp (Nat.le_zero.mp hcard)
    refine ⟨0, fun v => ?_⟩
    have hz : degVec v = 0 := by
      simp [degVec, Finset.univ_eq_empty]
    omega
  | succ n ih =>
    intro ι _ _ P hcard hindep
    by_cases hempty : IsEmpty ι
    · refine ⟨0, fun v => ?_⟩
      have hz : degVec v = 0 := by
        simp [degVec, Finset.univ_eq_empty]
      omega
    · rw [not_isEmpty_iff] at hempty
      obtain ⟨i⟩ := hempty
      have hnz : ∃ (i₀ : ι) (j₀ : κ), P i₀ j₀ ≠ 0 := by
        by_contra hall
        have hall' : ∀ (a : ι) (j : κ), P a j = 0 := by
          intro a j
          by_contra hz
          exact hall ⟨a, j, hz⟩
        have hv : vecMul (fun a => if a = i then (1 : DiffOp K) else 0) P = 0 := by
          funext j
          refine Finset.sum_eq_zero fun a _ => ?_
          rw [hall' a j, mul_zero]
        have hzero := hindep _ hv
        have h1 : (if i = i then (1 : DiffOp K) else 0) = 0 := congrFun hzero i
        rw [if_pos rfl] at h1
        exact one_ne_zero h1
      obtain ⟨i₀, j₀, hi₀j₀⟩ := hnz
      obtain ⟨P', i₁, hequiv, hnz', hclear⟩ :=
        exists_pivot_clear j₀ (degree (P i₀ j₀)) P i₀ hi₀j₀ le_rfl
      have hindep' : RowIndep P' := hequiv.rowIndep hindep
      have hcard' : Fintype.card {a : ι // a ≠ i₁} ≤ n := by
        have hc : Fintype.card {a : ι // a ≠ i₁} = Fintype.card ι - 1 := by
          rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
        have hpos : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i₁⟩
        omega
      have hsplit : ∀ (v : ι → DiffOp K) (j : κ),
          vecMul (fun a : {a : ι // a ≠ i₁} => v a.1) (fun a j => P' a.1 j) j
            = vecMul v P' j - v i₁ * P' i₁ j := by
        intro v j
        have hmem : ∀ a : ι, a ∈ Finset.univ.erase i₁ ↔ a ≠ i₁ := by
          intro a
          rw [Finset.mem_erase]
          exact ⟨fun h => h.1, fun h => ⟨h, Finset.mem_univ a⟩⟩
        have hsub : ∑ a : {a : ι // a ≠ i₁}, v a.1 * P' a.1 j
            = ∑ a ∈ Finset.univ.erase i₁, v a * P' a j :=
          (Finset.sum_subtype (Finset.univ.erase i₁) hmem (fun a => v a * P' a j)).symm
        have hfull : ∑ a, v a * P' a j
            = v i₁ * P' i₁ j + ∑ a ∈ Finset.univ.erase i₁, v a * P' a j :=
          (Finset.add_sum_erase _ _ (Finset.mem_univ i₁)).symm
        show ∑ a : {a : ι // a ≠ i₁}, v a.1 * P' a.1 j = (∑ a, v a * P' a j) - v i₁ * P' i₁ j
        rw [hsub, hfull]
        abel
      have hindepQ : RowIndep (fun (a : {a : ι // a ≠ i₁}) j => P' a.1 j) := by
        intro w hw
        set v : ι → DiffOp K := fun a => if h : a = i₁ then 0 else w ⟨a, h⟩ with hv_def
        have hv_top : v i₁ = 0 := by
          simp [hv_def]
        have hv_sub : ∀ a : {a : ι // a ≠ i₁}, v a.1 = w a := by
          intro a
          simp only [hv_def]
          exact dif_neg a.2
        have hzero : vecMul v P' = 0 := by
          funext j
          have hsp := hsplit v j
          rw [hv_top, zero_mul, sub_zero] at hsp
          rw [show (fun a : {a : ι // a ≠ i₁} => v a.1) = w from funext hv_sub,
            congrFun hw j] at hsp
          exact hsp.symm
        have h0 := hindep' _ hzero
        funext a
        have ha := congrFun h0 a.1
        rw [hv_sub a] at ha
        simpa using ha
      obtain ⟨B₀, hB₀⟩ := ih (fun (a : {a : ι // a ≠ i₁}) j => P' a.1 j) hcard' hindepQ
      have hBD' : BoundedDistortion P' := by
        refine ⟨matDeg P' + B₀, fun v => ?_⟩
        have hpivbound : degree (v i₁) ≤ degVec (vecMul v P') := by
          by_cases hv₁ : v i₁ = 0
          · rw [hv₁, degree_zero]
            exact Nat.zero_le _
          · have hcol : vecMul v P' j₀ = v i₁ * P' i₁ j₀ := by
              refine Finset.sum_eq_single i₁ ?_ ?_
              · intro a _ hane
                rw [hclear a hane, mul_zero]
              · intro h
                exact absurd (Finset.mem_univ i₁) h
            have hdeg : degree (vecMul v P' j₀) = degree (v i₁) + degree (P' i₁ j₀) := by
              rw [hcol, degree_mul hv₁ hnz']
            have hle := degree_le_degVec (vecMul v P') j₀
            omega
        have hQbound : degVec (vecMul (fun a : {a : ι // a ≠ i₁} => v a.1)
            (fun (a : {a : ι // a ≠ i₁}) j => P' a.1 j))
            ≤ degVec (vecMul v P') + matDeg P' := by
          refine degVec_le_iff.mpr fun j => ?_
          rw [hsplit v j]
          refine le_trans (degree_sub_le _ _) (max_le ?_ ?_)
          · exact le_trans (degree_le_degVec (vecMul v P') j) (Nat.le_add_right _ _)
          · exact le_trans (degree_mul_le (v i₁) (P' i₁ j))
              (Nat.add_le_add hpivbound (degree_le_matDeg P' i₁ j))
        have hw := hB₀ (fun a : {a : ι // a ≠ i₁} => v a.1)
        refine degVec_le_iff.mpr fun a => ?_
        by_cases ha : a = i₁
        · subst ha
          omega
        · have hda : degree (v a) ≤ degVec (fun a : {a : ι // a ≠ i₁} => v a.1) :=
            degree_le_degVec (fun a : {a : ι // a ≠ i₁} => v a.1) ⟨a, ha⟩
          omega
      exact hequiv.boundedDistortion hBD'

end Main

end

end DiffOp

end GaloisForLFunctions.HTGeometry
