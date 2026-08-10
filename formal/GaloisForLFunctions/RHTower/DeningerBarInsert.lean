import GaloisForLFunctions.RHTower.DeningerBarWord

/-!
# Unit insertion in bar words

Inserting the unit letter at a position of a word leaves the product of the letter heights and
the total arithmetic character unchanged, and is injective: the inserted position can be removed
again.  These are the only combinatorial facts the bar faces and the extra degeneracy need.

* `deningerInsertUnit` : insertion of the unit letter.
* `deningerInsertUnit_height`, `deningerInsertUnit_char`, `deningerInsertUnit_injective`.
-/

namespace RHTower

open GaloisForLFunctions

noncomputable section

/-- Insert the unit letter at position `t`. -/
def deningerInsertUnit {r : ℕ} (t : Fin (r + 2)) (f : Fin (r + 1) → DeningerPrimeLattice) :
    Fin (r + 2) → DeningerPrimeLattice :=
  Fin.insertNth (α := fun _ => DeningerPrimeLattice) t (0 : DeningerPrimeLattice) f

@[simp]
theorem deningerInsertUnit_same {r : ℕ} (t : Fin (r + 2))
    (f : Fin (r + 1) → DeningerPrimeLattice) : deningerInsertUnit t f t = 0 :=
  Fin.insertNth_apply_same (α := fun _ => DeningerPrimeLattice) t 0 f

@[simp]
theorem deningerInsertUnit_succAbove {r : ℕ} (t : Fin (r + 2))
    (f : Fin (r + 1) → DeningerPrimeLattice) (j : Fin (r + 1)) :
    deningerInsertUnit t f (t.succAbove j) = f j :=
  Fin.insertNth_apply_succAbove (α := fun _ => DeningerPrimeLattice) t 0 f j

/-- Unit insertion preserves the product of the letter heights. -/
theorem deningerInsertUnit_height {r : ℕ} (t : Fin (r + 2))
    (f : Fin (r + 1) → DeningerPrimeLattice) :
    (∏ i, deningerHeight (deningerInsertUnit t f i))
      = ∏ j, deningerHeight (f j) := by
  rw [Fin.prod_univ_succAbove (fun i => deningerHeight (deningerInsertUnit t f i)) t]
  simp

/-- Unit insertion preserves the total arithmetic character. -/
theorem deningerInsertUnit_char {r : ℕ} (t : Fin (r + 2))
    (f : Fin (r + 1) → DeningerPrimeLattice) :
    (∑ i, deningerInsertUnit t f i) = ∑ j, f j := by
  rw [Fin.sum_univ_succAbove (fun i => deningerInsertUnit t f i) t]
  simp

/-- Unit insertion at a fixed position is injective. -/
theorem deningerInsertUnit_injective {r : ℕ} (t : Fin (r + 2)) :
    Function.Injective (deningerInsertUnit (r := r) t) := by
  intro f g h
  have hf := Fin.removeNth_insertNth (α := fun _ => DeningerPrimeLattice) t (0 : DeningerPrimeLattice) f
  have hg := Fin.removeNth_insertNth (α := fun _ => DeningerPrimeLattice) t (0 : DeningerPrimeLattice) g
  have hcong := congrArg (Fin.removeNth (α := fun _ => DeningerPrimeLattice) t) h
  rw [deningerInsertUnit, deningerInsertUnit] at hcong
  rw [hf, hg] at hcong
  exact hcong

/-- The bar word obtained by inserting the unit letter at position `t`. -/
def deningerInsertUnitWord {r : ℕ} (t : Fin (r + 2))
    (f : Fin (r + 1) → DeningerPrimeLattice) : DeningerBarWord :=
  ⟨r + 1, deningerInsertUnit t f⟩

@[simp]
theorem deningerInsertUnitWord_height {r : ℕ} (t : Fin (r + 2))
    (f : Fin (r + 1) → DeningerPrimeLattice) :
    deningerBarHeight (deningerInsertUnitWord t f)
      = deningerBarHeight (⟨r, f⟩ : DeningerBarWord) :=
  deningerInsertUnit_height t f

@[simp]
theorem deningerInsertUnitWord_length {r : ℕ} (t : Fin (r + 2))
    (f : Fin (r + 1) → DeningerPrimeLattice) :
    deningerBarLength (deningerInsertUnitWord t f)
      = deningerBarLength (⟨r, f⟩ : DeningerBarWord) + 1 := rfl

@[simp]
theorem deningerInsertUnitWord_char {r : ℕ} (t : Fin (r + 2))
    (f : Fin (r + 1) → DeningerPrimeLattice) :
    deningerBarChar (deningerInsertUnitWord t f)
      = deningerBarChar (⟨r, f⟩ : DeningerBarWord) :=
  deningerInsertUnit_char t f

theorem deningerInsertUnitWord_injective {r : ℕ} (t : Fin (r + 2)) :
    Function.Injective (deningerInsertUnitWord (r := r) t) := by
  intro f g h
  rw [deningerInsertUnitWord, deningerInsertUnitWord, Sigma.mk.inj_iff] at h
  exact deningerInsertUnit_injective t (eq_of_heq h.2)

/-! ## Insertion at the front and behind it -/

theorem deningerInsertUnit_zero_apply_zero {r : ℕ} (f : Fin (r + 1) → DeningerPrimeLattice) :
    deningerInsertUnit (0 : Fin (r + 2)) f 0 = 0 :=
  deningerInsertUnit_same (0 : Fin (r + 2)) f

theorem deningerInsertUnit_zero_tail {r : ℕ} (f : Fin (r + 1) → DeningerPrimeLattice) :
    Fin.tail (deningerInsertUnit (0 : Fin (r + 2)) f) = f := by
  funext i
  show deningerInsertUnit (0 : Fin (r + 2)) f i.succ = f i
  rw [← Fin.zero_succAbove i]
  exact deningerInsertUnit_succAbove (0 : Fin (r + 2)) f i

theorem deningerInsertUnit_succ_apply_zero {r : ℕ} (u : Fin (r + 1))
    (f : Fin (r + 1) → DeningerPrimeLattice) :
    deningerInsertUnit u.succ f 0 = f 0 := by
  have h : u.succ.succAbove 0 = 0 := Fin.succ_succAbove_zero u
  calc deningerInsertUnit u.succ f 0
      = deningerInsertUnit u.succ f (u.succ.succAbove 0) := by rw [h]
    _ = f 0 := deningerInsertUnit_succAbove u.succ f 0

/-- Removing the first letter of a word with a unit inserted behind it is the word with the unit
inserted one position earlier. -/
theorem deningerInsertUnit_succ_tail {r : ℕ} (u : Fin (r + 2))
    (f : Fin (r + 2) → DeningerPrimeLattice) :
    Fin.tail (deningerInsertUnit (r := r + 1) u.succ f)
      = deningerInsertUnit (r := r) u (Fin.tail f) := by
  funext j
  refine Fin.succAboveCases (α := fun j =>
      Fin.tail (deningerInsertUnit (r := r + 1) u.succ f) j
        = deningerInsertUnit (r := r) u (Fin.tail f) j) u ?_ ?_ j
  · show deningerInsertUnit (r := r + 1) u.succ f u.succ
        = deningerInsertUnit (r := r) u (Fin.tail f) u
    rw [deningerInsertUnit_same, deningerInsertUnit_same]
  · intro i
    show deningerInsertUnit (r := r + 1) u.succ f (u.succAbove i).succ
        = deningerInsertUnit (r := r) u (Fin.tail f) (u.succAbove i)
    rw [← Fin.succ_succAbove_succ u i, deningerInsertUnit_succAbove,
      deningerInsertUnit_succAbove]
    rfl

theorem deningerInsertUnit_zero_eq_cons {r : ℕ} (g : Fin (r + 1) → DeningerPrimeLattice) :
    deningerInsertUnit (0 : Fin (r + 2)) g = Fin.cons 0 g := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rw [deningerInsertUnit_same]
    simp
  · intro j
    rw [← Fin.zero_succAbove j, deningerInsertUnit_succAbove]
    simp

theorem deningerInsertUnit_zero_of_apply_zero {r : ℕ} {f : Fin (r + 2) → DeningerPrimeLattice}
    (h : f 0 = 0) : deningerInsertUnit (0 : Fin (r + 2)) (Fin.tail f) = f := by
  rw [deningerInsertUnit_zero_eq_cons, ← h]
  exact Fin.cons_self_tail f

end

end RHTower
