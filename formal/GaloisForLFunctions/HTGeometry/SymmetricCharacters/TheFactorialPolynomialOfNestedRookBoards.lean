import GaloisForLFunctions.HTGeometry.SymmetricCharacters.NestedRowRookProducts
import Mathlib.Data.Finset.Sum
import Mathlib.Algebra.Group.ForwardDiff

/-!
# The factorial polynomial of a rook board

A rook placement on selected ordinary rows extends to a full placement by
injecting the missing rows into the auxiliary columns. Counting these
extensions in two ways gives the factorial rook polynomial. On nested
boards its value factors into the available column counts, exposing every
rook coefficient in the board expansion of Waters' moment formula (16).
-/

namespace GaloisForLFunctions.StaircasePacking
open Finset
noncomputable section
open scoped Classical

/-- One ordinary rook in each selected row, occupying distinct columns. -/
abbrev RowSubsetPlacement {α : Type*} (U : ℕ → Finset α) {n : ℕ} (A : Finset (Fin n)) :=
  {g : ↥A ↪ α // ∀ i : A, g i ∈ U i.val.val}

private instance placementFinite {α : Type*} (U : ℕ → Finset α) {n : ℕ} (A : Finset (Fin n)) :
    Finite (RowSubsetPlacement U A) := by
  let code (g : RowSubsetPlacement U A) (i : A) : U i.val.val := ⟨g.val i,g.property i⟩
  exact Finite.of_injective code fun f g h =>
    Subtype.ext (Function.Embedding.ext fun i => congrArg Subtype.val (congrFun h i))

/-- The new columns are disjoint from every ordinary column and are
available to every row. -/
def augmentedRookRows {α : Type*} (U : ℕ → Finset α) (e i : ℕ) : Finset (α ⊕ Fin e) :=
  (U i).disjSum univ

private abbrev MissingRows {n : ℕ} (A : Finset (Fin n)) := {i : Fin n // i∉A}

private def joinedColumn {α : Type*} {U : ℕ → Finset α} {n e : ℕ} {A : Finset (Fin n)}
    (g : RowSubsetPlacement U A) (h : MissingRows A ↪ Fin e) (i : Fin n) : α ⊕ Fin e :=
  if hi : i∈A then Sum.inl (g.val ⟨i,hi⟩) else Sum.inr (h ⟨i,hi⟩)

private def completePlacement {α : Type*} {U : ℕ → Finset α} {n e : ℕ} {A : Finset (Fin n)}
    (g : RowSubsetPlacement U A) (h : MissingRows A ↪ Fin e) :
    NestedRowRooks (augmentedRookRows U e) n := by
  refine ⟨⟨joinedColumn g h,?_⟩,?_⟩
  · intro i j he
    by_cases hi : i∈A <;> by_cases hj : j∈A
    · simp only [joinedColumn,dif_pos hi,dif_pos hj,Sum.inl.injEq] at he
      exact congrArg Subtype.val (g.val.injective he)
    · simp [joinedColumn,hi,hj] at he
    · simp [joinedColumn,hi,hj] at he
    · simp only [joinedColumn,dif_neg hi,dif_neg hj,Sum.inr.injEq] at he
      exact congrArg Subtype.val (h.injective he)
  · intro i
    change joinedColumn g h i ∈ (U i.val).disjSum univ
    by_cases hi : i∈A
    · rw [joinedColumn,dif_pos hi]
      exact inl_mem_disjSum.mpr (g.property ⟨i,hi⟩)
    · rw [joinedColumn,dif_neg hi]
      exact inr_mem_disjSum.mpr (mem_univ _)

private theorem ordinary_row_iff {α : Type*} {U : ℕ → Finset α} {n e : ℕ} {A : Finset (Fin n)}
    (g : RowSubsetPlacement U A) (h : MissingRows A ↪ Fin e) (i : Fin n) :
    (∃ x : α, joinedColumn g h i = Sum.inl x) ↔ i∈A := by
  by_cases hi : i∈A <;> simp [joinedColumn,hi]

private def completionEquiv {α : Type*} (U : ℕ → Finset α) (n e : ℕ) :
    ((A : Finset (Fin n)) × (RowSubsetPlacement U A × (MissingRows A ↪ Fin e))) ≃
      NestedRowRooks (augmentedRookRows U e) n := by
  let join (z : (A : Finset (Fin n)) × (RowSubsetPlacement U A × (MissingRows A ↪ Fin e))) :=
    completePlacement z.2.1 z.2.2
  refine Equiv.ofBijective join ⟨?_,?_⟩
  · rintro ⟨A,g,h⟩ ⟨B,j,l⟩ he
    have point (i : Fin n) : joinedColumn g h i=joinedColumn j l i :=
      congrArg (fun f : NestedRowRooks (augmentedRookRows U e) n => f.val i) he
    have ab : A=B := by
      ext i
      rw [←ordinary_row_iff g h,←ordinary_row_iff j l,point]
    subst B
    have eqg : g=j := by
      refine Subtype.ext (Function.Embedding.ext fun i => ?_)
      simpa only [joinedColumn,dif_pos i.property,Sum.inl.injEq] using point i.val
    have eqh : h=l := Function.Embedding.ext fun i => by
      simpa only [joinedColumn,dif_neg i.property,Sum.inr.injEq] using point i.val
    rw [eqg,eqh]
  · intro f
    let A := univ.filter fun i : Fin n => ∃ x : α, f.val i=Sum.inl x
    have hl (i : A) : ∃ x : α, f.val i.val=Sum.inl x := (mem_filter.mp i.property).2
    have hr (i : MissingRows A) : ∃ y : Fin e, f.val i.val=Sum.inr y := by
      cases he : f.val i.val with
      | inl x => exact (i.property (mem_filter.mpr ⟨mem_univ _,x,he⟩)).elim
      | inr y => exact ⟨y,rfl⟩
    choose x hx using hl
    choose y hy using hr
    let g : RowSubsetPlacement U A := ⟨⟨x,fun {i j} h => Subtype.ext (f.val.injective
      ((hx i).trans ((congrArg Sum.inl h).trans (hx j).symm)))⟩,fun i => by
        have h := f.property i.val
        rw [hx i] at h
        exact inl_mem_disjSum.mp h⟩
    let h : MissingRows A ↪ Fin e := ⟨y,fun {i j} he => Subtype.ext (f.val.injective
      ((hy i).trans ((congrArg Sum.inr he).trans (hy j).symm)))⟩
    refine ⟨⟨A,g,h⟩,Subtype.ext (Function.Embedding.ext fun i => ?_)⟩
    change joinedColumn g h i=f.val i
    by_cases hi : i∈A
    · rw [joinedColumn,dif_pos hi]
      exact (hx ⟨i,hi⟩).symm
    · rw [joinedColumn,dif_neg hi]
      exact (hy ⟨i,hi⟩).symm

/-- Every board, nested or otherwise, has the factorial expansion in its
physical partial rook placements. The number of completions depends only
on the number of empty rows. -/
theorem factorial_rook_expansion {α : Type*} (U : ℕ → Finset α) (n e : ℕ) :
    Nat.card (NestedRowRooks (augmentedRookRows U e) n) =
      ∑ A : Finset (Fin n), Nat.card (RowSubsetPlacement U A)*e.descFactorial (n-A.card) := by
  rw [← Nat.card_congr (completionEquiv U n e),Nat.card_sigma]
  refine sum_congr rfl fun A _ => ?_
  have hc : Fintype.card (MissingRows A) = n-A.card := by
    rw [Fintype.card_subtype_compl,Fintype.card_fin,Fintype.card_coe]
  rw [Nat.card_prod,Nat.card_eq_fintype_card (α:=MissingRows A ↪ Fin e),
    Fintype.card_embedding_eq,Fintype.card_fin,hc]

/-- The factorial rook polynomial of nested rows is a product of linear
factors, evaluated at any nonnegative integer number of auxiliary columns. -/
theorem factorial_rook_factorization {α : Type*} (U : ℕ → Finset α) (hU : Monotone U) (n e : ℕ) :
    ∑ A : Finset (Fin n), Nat.card (RowSubsetPlacement U A)*e.descFactorial (n-A.card) =
      ∏ i ∈ range n, ((U i).card+e-i) := by
  rw [← factorial_rook_expansion]
  have mono : Monotone (augmentedRookRows U e) := fun _ _ hij => disjSum_mono (hU hij) Subset.rfl
  rw [card_nestedRowRooks _ mono]
  simp only [augmentedRookRows,card_disjSum,card_univ,Fintype.card_fin]

/-- Total number of ordinary placements leaving exactly j of the n rows empty. -/
def vacantRowRookCount {α : Type*} (U : ℕ → Finset α) (n j : ℕ) : ℕ :=
  ∑ A ∈ (univ : Finset (Finset (Fin n))).filter (fun A => n-A.card=j), Nat.card (RowSubsetPlacement U A)

/-- The j-th forward difference of the linear-factor product reads the
j-vacancy rook coefficient, with the factorial from labeling the empty rows. -/
theorem rook_product_difference {α : Type*} (U : ℕ → Finset α) (hU : Monotone U) (n j : ℕ) :
    (fwdDiff (1:ℕ))^[j] (fun e : ℕ => ((∏ i ∈ range n, ((U i).card+e-i) : ℕ):ℤ)) 0 =
      (j.factorial:ℤ)*vacantRowRookCount U n j := by
  let m (A : Finset (Fin n)) := n-A.card
  let C (A : Finset (Fin n)) (e : ℕ) : ℤ := e.choose (m A)
  let w (A : Finset (Fin n)) : ℤ := (Nat.card (RowSubsetPlacement U A):ℤ)*(m A).factorial
  have expansion : (fun e : ℕ => ((∏ i ∈ range n, ((U i).card+e-i):ℕ):ℤ)) = ∑ A, w A • C A := by
    funext e
    rw [←factorial_rook_factorization U hU n e,Nat.cast_sum]
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,w,C,m,Nat.descFactorial_eq_factorial_mul_choose,
      Nat.cast_mul,mul_assoc]
  rw [expansion,fwdDiff_iter_finsetSum]
  simp only [fwdDiff_iter_const_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,C,fwdDiff_iter_choose_zero]
  simp only [vacantRowRookCount,Nat.cast_sum,mul_sum,sum_filter,mul_ite,mul_zero]
  refine sum_congr rfl fun A _ => ?_
  change (if j=m A then w A*1 else 0) =
    (j.factorial:ℤ) * ((if m A=j then Nat.card (RowSubsetPlacement U A) else 0 : ℕ):ℤ)
  by_cases h : m A=j
  · simp [w,h,mul_comm]
  · rw [if_neg (Ne.symm h),if_neg h,Nat.cast_zero,mul_zero]

/-- Every individual rook number is recovered from the j+1 evaluations
at 0 through j, in an explicit alternating binomial sum. -/
theorem rook_count_from_product_samples {α : Type*} (U : ℕ → Finset α) (hU : Monotone U)
    (n j : ℕ) :
    (∑ e ∈ range (j+1), ((-1:ℤ)^(j-e)*(j.choose e)) *
      ((∏ i ∈ range n, ((U i).card+e-i):ℕ):ℤ)) =
        (j.factorial:ℤ)*vacantRowRookCount U n j := by
  have h := rook_product_difference U hU n j
  rw [fwdDiff_iter_eq_sum_shift] at h
  simpa only [nsmul_eq_mul,mul_one,zero_add,zsmul_eq_mul,Nat.cast_id,Int.cast_id] using h


end
end GaloisForLFunctions.StaircasePacking
