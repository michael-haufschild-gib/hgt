import GaloisForLFunctions.RHTower.DeningerBarSector

/-!
# Bar faces as an honest partial map on words

The `j`-th bar face merges the letters at positions `j` and `j+1`.  In the two-term Milnor
algebra the merge is defined exactly when one of the two letters is the unit, and it then deletes
that letter.  Written as an `Option`-valued map on words, its fibre over a word is precisely the
pair of unit insertions at positions `j` and `j+1`, which coincide exactly when the letter at `j`
is the unit.

This identifies the coefficient description of the bar differential with the pushforward along the
face, which is the form in which the simplicial identities apply.

* `deningerBarFaceWord` : the face as a partial map on words.
* `deningerBarFaceWord_eq_some_iff` : **its fibre is the pair of unit insertions.**
-/

namespace RHTower

open GaloisForLFunctions

noncomputable section

variable {L : ℕ}

/-! ## Comparing the two insertions -/

theorem deningerInsertUnit_succ_apply_castSucc (j : Fin (L + 1))
    (f : Fin (L + 1) → DeningerPrimeLattice) :
    deningerInsertUnit j.succ f j.castSucc = f j := by
  have h : (j.succ).succAbove j = j.castSucc :=
    Fin.succAbove_of_castSucc_lt _ _ Fin.castSucc_lt_succ
  rw [← h, deningerInsertUnit_succAbove]

theorem deningerInsertUnit_castSucc_apply_succ (j : Fin (L + 1))
    (f : Fin (L + 1) → DeningerPrimeLattice) :
    deningerInsertUnit j.castSucc f j.succ = f j := by
  have h : (j.castSucc).succAbove j = j.succ :=
    Fin.succAbove_of_le_castSucc _ _ (le_refl _)
  rw [← h, deningerInsertUnit_succAbove]

/-- Inserting the unit just before or just after a unit letter gives the same word. -/
theorem deningerInsertUnit_succ_eq_castSucc {j : Fin (L + 1)}
    {f : Fin (L + 1) → DeningerPrimeLattice} (h : f j = 0) :
    deningerInsertUnit j.succ f = deningerInsertUnit j.castSucc f := by
  funext i
  refine Fin.succAboveCases (α := fun i => deningerInsertUnit j.succ f i
      = deningerInsertUnit j.castSucc f i) j.succ ?_ ?_ i
  · rw [deningerInsertUnit_same]
    have hpos : (j.castSucc).succAbove j = j.succ :=
      Fin.succAbove_of_le_castSucc _ _ (le_refl _)
    rw [← hpos, deningerInsertUnit_succAbove, h]
  · intro k
    rw [deningerInsertUnit_succAbove]
    rcases lt_trichotomy k j with hk | hk | hk
    · have h1 : (j.succ).succAbove k = k.castSucc := by
        refine Fin.succAbove_of_castSucc_lt _ _ ?_
        rw [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
        have := (Fin.lt_def.mp hk)
        omega
      have h2 : (j.castSucc).succAbove k = k.castSucc := by
        refine Fin.succAbove_of_castSucc_lt _ _ ?_
        rw [Fin.lt_def, Fin.val_castSucc, Fin.val_castSucc]
        exact Fin.lt_def.mp hk
      rw [h1, ← h2, deningerInsertUnit_succAbove]
    · subst hk
      have h1 : (k.succ).succAbove k = k.castSucc :=
        Fin.succAbove_of_castSucc_lt _ _ Fin.castSucc_lt_succ
      rw [h1, deningerInsertUnit_same]
      exact h
    · have h1 : (j.succ).succAbove k = k.succ := by
        refine Fin.succAbove_of_le_castSucc _ _ ?_
        rw [Fin.le_def, Fin.val_castSucc, Fin.val_succ]
        have := (Fin.lt_def.mp hk)
        omega
      have h2 : (j.castSucc).succAbove k = k.succ := by
        refine Fin.succAbove_of_le_castSucc _ _ ?_
        rw [Fin.le_def, Fin.val_castSucc, Fin.val_castSucc]
        exact le_of_lt (Fin.lt_def.mp hk)
      rw [h1, ← h2, deningerInsertUnit_succAbove]

/-! ## The face as a partial map -/

/-- **The `j`-th bar face of a word**: merge the letters at positions `j` and `j+1`.  The value is
`none` exactly when both letters are nonunit, where the product vanishes. -/
def deningerBarFaceWord (j : Fin (L + 1)) (v : Fin (L + 2) → DeningerPrimeLattice) :
    Option (Fin (L + 1) → DeningerPrimeLattice) :=
  if v j.castSucc = 0 then some (Fin.removeNth j.castSucc v)
  else if v j.succ = 0 then some (Fin.removeNth j.succ v)
  else none

theorem deningerBarFaceWord_insert_castSucc (j : Fin (L + 1))
    (f : Fin (L + 1) → DeningerPrimeLattice) :
    deningerBarFaceWord j (deningerInsertUnit j.castSucc f) = some f := by
  rw [deningerBarFaceWord, if_pos (deningerInsertUnit_same j.castSucc f)]
  congr 1
  exact Fin.removeNth_insertNth (α := fun _ => DeningerPrimeLattice) j.castSucc 0 f

theorem deningerBarFaceWord_insert_succ (j : Fin (L + 1))
    (f : Fin (L + 1) → DeningerPrimeLattice) :
    deningerBarFaceWord j (deningerInsertUnit j.succ f) = some f := by
  by_cases h : f j = 0
  · rw [deningerInsertUnit_succ_eq_castSucc h]
    exact deningerBarFaceWord_insert_castSucc j f
  · rw [deningerBarFaceWord,
      if_neg (by rw [deningerInsertUnit_succ_apply_castSucc]; exact h),
      if_pos (deningerInsertUnit_same j.succ f)]
    congr 1
    exact Fin.removeNth_insertNth (α := fun _ => DeningerPrimeLattice) j.succ 0 f

/-- **The fibre of the `j`-th face is the pair of unit insertions.** -/
theorem deningerBarFaceWord_eq_some_iff (j : Fin (L + 1))
    (v : Fin (L + 2) → DeningerPrimeLattice) (f : Fin (L + 1) → DeningerPrimeLattice) :
    deningerBarFaceWord j v = some f ↔
      v = deningerInsertUnit j.castSucc f ∨ v = deningerInsertUnit j.succ f := by
  constructor
  · intro hv
    rw [deningerBarFaceWord] at hv
    by_cases h : v j.castSucc = 0
    · rw [if_pos h] at hv
      have hf : Fin.removeNth j.castSucc v = f := Option.some_injective _ hv
      left
      rw [deningerInsertUnit, ← hf, ← h]
      exact (Fin.insertNth_self_removeNth (α := fun _ => DeningerPrimeLattice) j.castSucc v).symm
    · rw [if_neg h] at hv
      by_cases h2 : v j.succ = 0
      · rw [if_pos h2] at hv
        have hf : Fin.removeNth j.succ v = f := Option.some_injective _ hv
        right
        rw [deningerInsertUnit, ← hf, ← h2]
        exact (Fin.insertNth_self_removeNth (α := fun _ => DeningerPrimeLattice) j.succ v).symm
      · rw [if_neg h2] at hv
        exact absurd hv (by simp)
  · rintro (rfl | rfl)
    · exact deningerBarFaceWord_insert_castSucc j f
    · exact deningerBarFaceWord_insert_succ j f

end

end RHTower
