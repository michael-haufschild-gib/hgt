import GaloisForLFunctions.RHTower.Deninger.DeningerBarFace

/-!
# Positional description of unit insertion, and its commutation

Reading a unit insertion off at a position below or above the insertion point turns it into an
ordinary index shift.  Two unit insertions therefore commute in the standard simplicial way: the
unordered pair of inserted positions is all that matters.

* `deningerInsertUnit_apply_of_lt`, `deningerInsertUnit_apply_of_gt` : positional evaluation.
* `deningerInsertUnit_comm` : **two unit insertions commute with the standard index shift.**
-/

namespace RHTower

open GaloisForLFunctions

noncomputable section

variable {r : ℕ}

theorem deningerInsertUnit_apply_of_lt {t i : Fin (r + 2)}
    (f : Fin (r + 1) → DeningerPrimeLattice) (h : (i : ℕ) < (t : ℕ))
    (k : Fin (r + 1)) (hk : (k : ℕ) = (i : ℕ)) :
    deningerInsertUnit t f i = f k := by
  have h1 : t.succAbove k = i := by
    rw [Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def, Fin.val_castSucc, hk]; exact h)]
    exact Fin.ext (by rw [Fin.val_castSucc, hk])
  rw [← h1, deningerInsertUnit_succAbove]

theorem deningerInsertUnit_apply_of_gt {t i : Fin (r + 2)}
    (f : Fin (r + 1) → DeningerPrimeLattice) (h : (t : ℕ) < (i : ℕ))
    (k : Fin (r + 1)) (hk : (k : ℕ) + 1 = (i : ℕ)) :
    deningerInsertUnit t f i = f k := by
  have h1 : t.succAbove k = i := by
    rw [Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def, Fin.val_castSucc]; omega)]
    exact Fin.ext (by rw [Fin.val_succ, hk])
  rw [← h1, deningerInsertUnit_succAbove]

theorem deningerInsertUnit_apply_of_eq {t i : Fin (r + 2)}
    (f : Fin (r + 1) → DeningerPrimeLattice) (h : (i : ℕ) = (t : ℕ)) :
    deningerInsertUnit t f i = 0 := by
  have h1 : i = t := Fin.ext h
  rw [h1, deningerInsertUnit_same]

/-- **Two unit insertions commute.**  Inserting at `b` and then at `a ≤ b` is the same as
inserting at `a` and then at `b+1`. -/
theorem deningerInsertUnit_comm (f : Fin (r + 1) → DeningerPrimeLattice) (a b : Fin (r + 2))
    (hab : (a : ℕ) ≤ (b : ℕ)) :
    deningerInsertUnit a.castSucc (deningerInsertUnit b f)
      = deningerInsertUnit b.succ (deningerInsertUnit a f) := by
  have hbb : (b.succ : Fin (r + 3)).val = (b : ℕ) + 1 := Fin.val_succ b
  have haa : (a.castSucc : Fin (r + 3)).val = (a : ℕ) := Fin.val_castSucc a
  have hblt : (b : ℕ) < r + 2 := b.isLt
  funext i
  rcases lt_trichotomy (i : ℕ) (a : ℕ) with hi | hi | hi
  · have hka : (i : ℕ) < r + 2 := by omega
    rw [deningerInsertUnit_apply_of_lt (t := a.castSucc) _ (by rw [haa]; exact hi)
        ⟨(i : ℕ), hka⟩ rfl,
      deningerInsertUnit_apply_of_lt (t := b.succ) _ (by rw [hbb]; omega)
        ⟨(i : ℕ), hka⟩ rfl,
      deningerInsertUnit_apply_of_lt (t := b) _ (by simpa using (by omega : (i : ℕ) < (b : ℕ)))
        ⟨(i : ℕ), by omega⟩ rfl,
      deningerInsertUnit_apply_of_lt (t := a) _ (by simpa using hi) ⟨(i : ℕ), by omega⟩ rfl]
  · rw [deningerInsertUnit_apply_of_eq (t := a.castSucc) _ (by rw [haa]; exact hi),
      deningerInsertUnit_apply_of_lt (t := b.succ) _ (by rw [hbb]; omega)
        ⟨(i : ℕ), by omega⟩ rfl,
      deningerInsertUnit_apply_of_eq (t := a) _ (by simpa using hi)]
  · rcases lt_trichotomy (i : ℕ) ((b : ℕ) + 1) with hi2 | hi2 | hi2
    · rw [deningerInsertUnit_apply_of_gt (t := a.castSucc) _ (by rw [haa]; exact hi)
          ⟨(i : ℕ) - 1, by omega⟩ (by simp; omega),
        deningerInsertUnit_apply_of_lt (t := b.succ) _ (by rw [hbb]; exact hi2)
          ⟨(i : ℕ), by omega⟩ rfl,
        deningerInsertUnit_apply_of_lt (t := b) _ (by simp; omega)
          ⟨(i : ℕ) - 1, by omega⟩ (by simp),
        deningerInsertUnit_apply_of_gt (t := a) _ (by simp; omega)
          ⟨(i : ℕ) - 1, by omega⟩ (by simp; omega)]
    · rw [deningerInsertUnit_apply_of_gt (t := a.castSucc) _ (by rw [haa]; exact hi)
          ⟨(i : ℕ) - 1, by omega⟩ (by simp; omega),
        deningerInsertUnit_apply_of_eq (t := b.succ) _ (by rw [hbb]; omega),
        deningerInsertUnit_apply_of_eq (t := b) _ (by simp; omega)]
    · rw [deningerInsertUnit_apply_of_gt (t := a.castSucc) _ (by rw [haa]; omega)
          ⟨(i : ℕ) - 1, by omega⟩ (by simp; omega),
        deningerInsertUnit_apply_of_gt (t := b.succ) _ (by rw [hbb]; omega)
          ⟨(i : ℕ) - 1, by omega⟩ (by simp; omega),
        deningerInsertUnit_apply_of_gt (t := b) _ (by simp; omega)
          ⟨(i : ℕ) - 2, by omega⟩ (by simp; omega),
        deningerInsertUnit_apply_of_gt (t := a) _ (by simp; omega)
          ⟨(i : ℕ) - 2, by omega⟩ (by simp; omega)]

end

end RHTower
