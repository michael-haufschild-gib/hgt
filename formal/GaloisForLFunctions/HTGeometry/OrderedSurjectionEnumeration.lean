import GaloisForLFunctions.HTGeometry.OrderedSetPartitionEnumeration

/-!
# Ordered partition codes as finite surjections

An ordered partition of `Fin n` into `j` nonempty labelled blocks is exactly a surjection
`Fin n → Fin j`.  This file constructs the equivalence with `OrderedPartitionCode n j`.
The successor step distinguishes whether the block containing the new point contains an old point
or is a new singleton inserted at an arbitrary block position.
-/

namespace GaloisForLFunctions
namespace IrregularStokes

/-- A function between finite ordinals carrying its surjectivity proof. -/
@[ext]
structure FinSurjection (n j : ℕ) where
  toFun : Fin n → Fin j
  surjective : Function.Surjective toFun

instance (n j : ℕ) : CoeFun (FinSurjection n j) fun _ => Fin n → Fin j :=
  ⟨FinSurjection.toFun⟩

instance (n j : ℕ) : Finite (FinSurjection n j) := by
  let encode : FinSurjection n j → (Fin n → Fin j) := FinSurjection.toFun
  exact Finite.of_injective encode fun _ _ h => FinSurjection.ext h

namespace FinSurjection

/-- Delete one specified ordinal position from a different ordinal value. -/
noncomputable def deleteIndex {j : ℕ} (b y : Fin (j + 1)) (h : y ≠ b) : Fin j :=
  Classical.choose (Fin.exists_succAbove_eq h)

theorem succAbove_deleteIndex {j : ℕ} (b y : Fin (j + 1)) (h : y ≠ b) :
    b.succAbove (deleteIndex b y h) = y :=
  Classical.choose_spec (Fin.exists_succAbove_eq h)

@[simp] theorem deleteIndex_succAbove {j : ℕ} (b : Fin (j + 1)) (y : Fin j) :
    deleteIndex b (b.succAbove y) (b.succAbove_ne y) = y := by
  apply b.succAboveEmb.injective
  exact succAbove_deleteIndex b (b.succAbove y) (b.succAbove_ne y)

/-- Add a new domain point to an existing block. -/
def extendExisting {n j : ℕ} (b : Fin (j + 1)) (f : FinSurjection n (j + 1)) :
    FinSurjection (n + 1) (j + 1) where
  toFun := Fin.cases b f
  surjective := by
    intro y
    obtain ⟨x, rfl⟩ := f.surjective y
    exact ⟨x.succ, by simp⟩

/-- Insert the new domain point as a singleton block at position `b`. -/
def extendSingleton {n j : ℕ} (b : Fin (j + 1)) (f : FinSurjection n j) :
    FinSurjection (n + 1) (j + 1) where
  toFun := Fin.cases b fun x => b.succAbove (f x)
  surjective := by
    intro y
    by_cases hy : y = b
    · exact ⟨0, hy.symm⟩
    · obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq hy
      obtain ⟨x, hx⟩ := f.surjective z
      exact ⟨x.succ, by simpa [hx] using hz⟩

@[simp] theorem extendExisting_zero {n j : ℕ} (b : Fin (j + 1))
    (f : FinSurjection n (j + 1)) : extendExisting b f 0 = b := rfl

@[simp] theorem extendExisting_succ {n j : ℕ} (b : Fin (j + 1))
    (f : FinSurjection n (j + 1)) (x : Fin n) : extendExisting b f x.succ = f x := rfl

@[simp] theorem extendSingleton_zero {n j : ℕ} (b : Fin (j + 1))
    (f : FinSurjection n j) : extendSingleton b f 0 = b := rfl

@[simp] theorem extendSingleton_succ {n j : ℕ} (b : Fin (j + 1))
    (f : FinSurjection n j) (x : Fin n) :
    extendSingleton b f x.succ = b.succAbove (f x) := rfl

/-- Restrict after proving that the new point's block already contained an old point. -/
def restrictExisting {n j : ℕ} (f : FinSurjection (n + 1) (j + 1))
    (h : ∃ x : Fin n, f x.succ = f 0) : FinSurjection n (j + 1) where
  toFun := fun x => f x.succ
  surjective := by
    intro y
    by_cases hy : y = f 0
    · obtain ⟨x, hx⟩ := h
      exact ⟨x, by simpa [hy] using hx⟩
    · obtain ⟨z, hz⟩ := f.surjective y
      rcases Fin.eq_zero_or_eq_succ z with rfl | ⟨x, rfl⟩
      · exact False.elim (hy hz.symm)
      · exact ⟨x, hz⟩

/-- Restrict after proving that the new point forms a singleton block, deleting that block's
position from the codomain. -/
noncomputable def restrictSingleton {n j : ℕ} (f : FinSurjection (n + 1) (j + 1))
    (h : ¬∃ x : Fin n, f x.succ = f 0) : FinSurjection n j where
  toFun := fun x => deleteIndex (f 0) (f x.succ) (by
    intro heq
    exact h ⟨x, heq⟩)
  surjective := by
    intro y
    have htarget : (f 0).succAbove y ≠ f 0 := (f 0).succAbove_ne y
    obtain ⟨z, hz⟩ := f.surjective ((f 0).succAbove y)
    rcases Fin.eq_zero_or_eq_succ z with rfl | ⟨x, rfl⟩
    · exact False.elim (htarget hz.symm)
    · refine ⟨x, ?_⟩
      have hxne : f x.succ ≠ f 0 := by
        intro heq
        exact h ⟨x, heq⟩
      apply (f 0).succAboveEmb.injective
      change (f 0).succAbove (deleteIndex (f 0) (f x.succ) hxne) =
        (f 0).succAbove y
      rw [succAbove_deleteIndex (f 0) (f x.succ) hxne, hz]

/-- Successor classification for ordered surjections. -/
noncomputable def stepEquiv (n j : ℕ) :
    FinSurjection (n + 1) (j + 1) ≃
      (Fin (j + 1) × FinSurjection n (j + 1)) ⊕
        (Fin (j + 1) × FinSurjection n j) where
  toFun f :=
    if h : ∃ x : Fin n, f x.succ = f 0 then
      Sum.inl (f 0, restrictExisting f h)
    else
      Sum.inr (f 0, restrictSingleton f h)
  invFun
    | Sum.inl (b, f) => extendExisting b f
    | Sum.inr (b, f) => extendSingleton b f
  left_inv := by
    intro f
    classical
    by_cases h : ∃ x : Fin n, f x.succ = f 0
    · simp only [h, dif_pos]
      apply FinSurjection.ext
      funext x
      rcases Fin.eq_zero_or_eq_succ x with rfl | ⟨x, rfl⟩ <;> rfl
    · simp only [h]
      apply FinSurjection.ext
      funext x
      rcases Fin.eq_zero_or_eq_succ x with rfl | ⟨x, rfl⟩
      · rfl
      · exact succAbove_deleteIndex (f 0) (f x.succ) (by
          intro heq
          exact h ⟨x, heq⟩)
  right_inv := by
    intro s
    classical
    rcases s with ⟨b, f⟩ | ⟨b, f⟩
    · have h : ∃ x : Fin n, extendExisting b f x.succ = b := by
        obtain ⟨x, hx⟩ := f.surjective b
        exact ⟨x, by simpa using hx⟩
      change (if h' : ∃ x : Fin n, extendExisting b f x.succ = b then
          Sum.inl (b, restrictExisting (extendExisting b f) h')
        else Sum.inr (b, restrictSingleton (extendExisting b f) h')) = Sum.inl (b, f)
      rw [dif_pos h]
      congr 2
    · have h : ¬∃ x : Fin n, extendSingleton b f x.succ = b := by
        rintro ⟨x, hx⟩
        exact b.succAbove_ne (f x) hx
      change (if h' : ∃ x : Fin n, extendSingleton b f x.succ = b then
          Sum.inl (b, restrictExisting (extendSingleton b f) h')
        else Sum.inr (b, restrictSingleton (extendSingleton b f) h')) = Sum.inr (b, f)
      rw [dif_neg h]
      congr 2
      apply FinSurjection.ext
      funext x
      exact deleteIndex_succAbove b (f x)

/-- Recursive ordered-partition codes are exactly surjections onto labelled blocks. -/
noncomputable def codeEquiv : ∀ n j, OrderedPartitionCode n j ≃ FinSurjection n j
  | 0, 0 =>
      { toFun := fun _ => ⟨fun x => Fin.elim0 x, fun y => Fin.elim0 y⟩
        invFun := fun _ => PUnit.unit
        left_inv := fun x => by cases x; rfl
        right_inv := fun x => by
          apply FinSurjection.ext
          funext y
          exact Fin.elim0 y }
  | 0, j + 1 =>
      { toFun := PEmpty.elim
        invFun := fun f => False.elim (by
          obtain ⟨x, _⟩ := f.surjective 0
          exact Fin.elim0 x)
        left_inv := fun x => PEmpty.elim x
        right_inv := fun f => False.elim (by
          obtain ⟨x, _⟩ := f.surjective 0
          exact Fin.elim0 x) }
  | n + 1, 0 =>
      { toFun := PEmpty.elim
        invFun := fun f => Fin.elim0 (f 0)
        left_inv := fun x => PEmpty.elim x
        right_inv := fun f => Fin.elim0 (f 0) }
  | n + 1, j + 1 =>
      (Equiv.sumCongr
        (Equiv.prodCongr (Equiv.refl _) (codeEquiv n (j + 1)))
        (Equiv.prodCongr (Equiv.refl _) (codeEquiv n j))).trans
          (stepEquiv n j).symm

/-- Fixed-block ordered partitions have the expected exact cardinality as surjections. -/
theorem card (n j : ℕ) :
    Nat.card (FinSurjection n j) = j.factorial * Nat.stirlingSecond n j := by
  rw [Nat.card_congr (codeEquiv n j).symm]
  exact OrderedPartitionCode.card n j

end FinSurjection

end IrregularStokes
end GaloisForLFunctions
