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
def deningerInsertUnit {r : ℕ} (t : Fin (r + 2)) (f : Fin (r + 1) → DeningerLattice) :
    Fin (r + 2) → DeningerLattice :=
  Fin.insertNth (α := fun _ => DeningerLattice) t (0 : DeningerLattice) f

@[simp]
theorem deningerInsertUnit_same {r : ℕ} (t : Fin (r + 2))
    (f : Fin (r + 1) → DeningerLattice) : deningerInsertUnit t f t = 0 :=
  Fin.insertNth_apply_same (α := fun _ => DeningerLattice) t 0 f

@[simp]
theorem deningerInsertUnit_succAbove {r : ℕ} (t : Fin (r + 2))
    (f : Fin (r + 1) → DeningerLattice) (j : Fin (r + 1)) :
    deningerInsertUnit t f (t.succAbove j) = f j :=
  Fin.insertNth_apply_succAbove (α := fun _ => DeningerLattice) t 0 f j

/-- Unit insertion preserves the product of the letter heights. -/
theorem deningerInsertUnit_height {r : ℕ} (t : Fin (r + 2))
    (f : Fin (r + 1) → DeningerLattice) :
    (∏ i, deningerHeight (deningerInsertUnit t f i))
      = ∏ j, deningerHeight (f j) := by
  rw [Fin.prod_univ_succAbove (fun i => deningerHeight (deningerInsertUnit t f i)) t]
  simp

/-- Unit insertion preserves the total arithmetic character. -/
theorem deningerInsertUnit_char {r : ℕ} (t : Fin (r + 2))
    (f : Fin (r + 1) → DeningerLattice) :
    (∑ i, deningerInsertUnit t f i) = ∑ j, f j := by
  rw [Fin.sum_univ_succAbove (fun i => deningerInsertUnit t f i) t]
  simp

/-- Unit insertion at a fixed position is injective. -/
theorem deningerInsertUnit_injective {r : ℕ} (t : Fin (r + 2)) :
    Function.Injective (deningerInsertUnit (r := r) t) := by
  intro f g h
  have hf := Fin.removeNth_insertNth (α := fun _ => DeningerLattice) t (0 : DeningerLattice) f
  have hg := Fin.removeNth_insertNth (α := fun _ => DeningerLattice) t (0 : DeningerLattice) g
  have hcong := congrArg (Fin.removeNth (α := fun _ => DeningerLattice) t) h
  rw [deningerInsertUnit, deningerInsertUnit] at hcong
  rw [hf, hg] at hcong
  exact hcong

/-- The bar word obtained by inserting the unit letter at position `t`. -/
def deningerInsertUnitWord {r : ℕ} (t : Fin (r + 2))
    (f : Fin (r + 1) → DeningerLattice) : DeningerBarWord :=
  ⟨r + 1, deningerInsertUnit t f⟩

@[simp]
theorem deningerInsertUnitWord_height {r : ℕ} (t : Fin (r + 2))
    (f : Fin (r + 1) → DeningerLattice) :
    deningerBarHeight (deningerInsertUnitWord t f)
      = deningerBarHeight (⟨r, f⟩ : DeningerBarWord) :=
  deningerInsertUnit_height t f

@[simp]
theorem deningerInsertUnitWord_length {r : ℕ} (t : Fin (r + 2))
    (f : Fin (r + 1) → DeningerLattice) :
    deningerBarLength (deningerInsertUnitWord t f)
      = deningerBarLength (⟨r, f⟩ : DeningerBarWord) + 1 := rfl

@[simp]
theorem deningerInsertUnitWord_char {r : ℕ} (t : Fin (r + 2))
    (f : Fin (r + 1) → DeningerLattice) :
    deningerBarChar (deningerInsertUnitWord t f)
      = deningerBarChar (⟨r, f⟩ : DeningerBarWord) :=
  deningerInsertUnit_char t f

theorem deningerInsertUnitWord_injective {r : ℕ} (t : Fin (r + 2)) :
    Function.Injective (deningerInsertUnitWord (r := r) t) := by
  intro f g h
  rw [deningerInsertUnitWord, deningerInsertUnitWord, Sigma.mk.inj_iff] at h
  exact deningerInsertUnit_injective t (eq_of_heq h.2)

end

end RHTower
