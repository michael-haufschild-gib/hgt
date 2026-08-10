import GaloisForLFunctions.RHTower.DeningerBarUnit

/-!
# The strict contraction of the entire word-height bar source

The zeroth face of a word with the unit prepended is the word itself, and every later face of it
is the corresponding face of its tail with the opposite sign.  Hence

`b s + s b = 1`

on the whole bar source, so the augmented completed bar complex is split strictly exact: every
boundary range is closed, and the continuous extra degeneracy is an explicit contracting homotopy.

* `deningerBarContraction` : **`b s + s b = 1`.**
* `deningerBar_exact` : a cycle is the boundary of the explicit primitive `s c`.
-/

namespace RHTower

open GaloisForLFunctions

noncomputable section

private theorem deningerBar_head_term (c : DeningerBarWord → ℂ) {s : ℕ}
    (f : Fin (s + 1) → DeningerLattice) :
    deningerBarFibreSum (deningerBarUnitCoe c) f 0 = c (⟨s, f⟩ : DeningerBarWord) := by
  have hzero : (0 : Fin (s + 1)).castSucc = (0 : Fin (s + 2)) := rfl
  rw [deningerBarFibreSum, hzero]
  by_cases h : f 0 = 0
  · rw [if_pos h]
    exact deningerBarUnitCoe_insert_zero c f
  · rw [if_neg h, deningerBarUnitCoe_insert_zero c f,
      deningerBarUnitCoe_insert_succ c (0 : Fin (s + 1)) f h, add_zero]

private theorem deningerBar_tail_term_of_ne (c : DeningerBarWord → ℂ) {r : ℕ}
    (f : Fin (r + 2) → DeningerLattice) (hf : f 0 ≠ 0) (u : Fin (r + 1)) :
    deningerBarFibreSum (deningerBarUnitCoe c) f u.succ = 0 := by
  have hcast : (u.succ).castSucc = (u.castSucc).succ := (Fin.succ_castSucc u).symm
  have h1 : deningerBarUnitCoe c
      (deningerInsertUnitWord (u.succ).castSucc f) = 0 := by
    rw [hcast]
    exact deningerBarUnitCoe_insert_succ c u.castSucc f hf
  have h2 : deningerBarUnitCoe c (deningerInsertUnitWord (u.succ).succ f) = 0 :=
    deningerBarUnitCoe_insert_succ c u.succ f hf
  rw [deningerBarFibreSum]
  by_cases h : f u.succ = 0
  · rw [if_pos h, h1]
  · rw [if_neg h, h1, h2, add_zero]

private theorem deningerBar_tail_term_of_eq (c : DeningerBarWord → ℂ) {r : ℕ}
    (f : Fin (r + 2) → DeningerLattice) (hf : f 0 = 0) (u : Fin (r + 1)) :
    deningerBarFibreSum (deningerBarUnitCoe c) f u.succ
      = deningerBarFibreSum c (Fin.tail f) u := by
  have hcast : (u.succ).castSucc = (u.castSucc).succ := (Fin.succ_castSucc u).symm
  have h1 : deningerBarUnitCoe c (deningerInsertUnitWord (u.succ).castSucc f)
      = c (deningerInsertUnitWord u.castSucc (Fin.tail f)) := by
    rw [hcast, deningerInsertUnitWord, deningerBarUnitCoe_succ,
      if_pos (by rw [deningerInsertUnit_succ_apply_zero]; exact hf),
      deningerInsertUnit_succ_tail]
    rfl
  have h2 : deningerBarUnitCoe c (deningerInsertUnitWord (u.succ).succ f)
      = c (deningerInsertUnitWord u.succ (Fin.tail f)) := by
    rw [deningerInsertUnitWord, deningerBarUnitCoe_succ,
      if_pos (by rw [deningerInsertUnit_succ_apply_zero]; exact hf),
      deningerInsertUnit_succ_tail]
    rfl
  have htail : Fin.tail f u = f u.succ := rfl
  rw [deningerBarFibreSum, deningerBarFibreSum, htail]
  by_cases h : f u.succ = 0
  · rw [if_pos h, if_pos h, h1]
  · rw [if_neg h, if_neg h, h1, h2]

/-- **The extra degeneracy contracts the bar complex**: `b s + s b = 1`. -/
theorem deningerBarContraction (c : DeningerBarWord → ℂ) (w : DeningerBarWord) :
    deningerBarDiffCoe (deningerBarUnitCoe c) w + deningerBarUnitCoe (deningerBarDiffCoe c) w
      = c w := by
  obtain ⟨s, f⟩ := w
  have hsplit : deningerBarDiffCoe (deningerBarUnitCoe c) (⟨s, f⟩ : DeningerBarWord)
      = deningerBarFibreSum (deningerBarUnitCoe c) f 0
        + ∑ u : Fin s, (-1 : ℂ) ^ ((u.succ : Fin (s + 1)) : ℕ) *
            deningerBarFibreSum (deningerBarUnitCoe c) f u.succ := by
    show (∑ j : Fin (s + 1), (-1 : ℂ) ^ (j : ℕ) *
        deningerBarFibreSum (deningerBarUnitCoe c) f j) = _
    rw [Fin.sum_univ_succ]
    simp
  rw [hsplit, deningerBar_head_term c f]
  cases s with
  | zero =>
      show c (⟨0, f⟩ : DeningerBarWord) + (∑ u : Fin 0, _) +
        deningerBarUnitCoe (deningerBarDiffCoe c) (⟨0, f⟩ : DeningerBarWord) = _
      rw [Finset.univ_eq_empty, Finset.sum_empty, add_zero, deningerBarUnitCoe_one, add_zero]
  | succ r =>
      by_cases hf : f 0 = 0
      · have hterm : ∀ u : Fin (r + 1),
            (-1 : ℂ) ^ ((u.succ : Fin (r + 2)) : ℕ) *
              deningerBarFibreSum (deningerBarUnitCoe c) f u.succ
              = -((-1 : ℂ) ^ ((u : Fin (r + 1)) : ℕ) *
                  deningerBarFibreSum c (Fin.tail f) u) := by
          intro u
          rw [deningerBar_tail_term_of_eq c f hf u, Fin.val_succ, pow_succ]
          ring
        have hsum : (∑ u : Fin (r + 1), (-1 : ℂ) ^ ((u.succ : Fin (r + 2)) : ℕ) *
              deningerBarFibreSum (deningerBarUnitCoe c) f u.succ)
            = -deningerBarDiffCoe c (⟨r, Fin.tail f⟩ : DeningerBarWord) := by
          rw [Finset.sum_congr rfl fun u _ => hterm u, Finset.sum_neg_distrib]
          rfl
        have hunit : deningerBarUnitCoe (deningerBarDiffCoe c)
            (⟨r + 1, f⟩ : DeningerBarWord)
            = deningerBarDiffCoe c (⟨r, Fin.tail f⟩ : DeningerBarWord) := by
          rw [deningerBarUnitCoe_succ, if_pos hf]
        rw [hsum, hunit]
        ring
      · have hterm : ∀ u : Fin (r + 1),
            (-1 : ℂ) ^ ((u.succ : Fin (r + 2)) : ℕ) *
              deningerBarFibreSum (deningerBarUnitCoe c) f u.succ = 0 := by
          intro u
          rw [deningerBar_tail_term_of_ne c f hf u, mul_zero]
        have hsum : (∑ u : Fin (r + 1), (-1 : ℂ) ^ ((u.succ : Fin (r + 2)) : ℕ) *
              deningerBarFibreSum (deningerBarUnitCoe c) f u.succ) = 0 := by
          rw [Finset.sum_congr rfl fun u _ => hterm u, Finset.sum_const_zero]
        have hunit : deningerBarUnitCoe (deningerBarDiffCoe c)
            (⟨r + 1, f⟩ : DeningerBarWord) = 0 := by
          rw [deningerBarUnitCoe_succ, if_neg hf]
        rw [hsum, hunit, add_zero, add_zero]

/-- **`b s + s b = 1` as an operator identity on the source.** -/
theorem deningerBarContraction_op (c : DeningerBarKothe) :
    deningerBarDiff (deningerBarUnit c) + deningerBarUnit (deningerBarDiff c) = c := by
  ext w
  show ((deningerBarDiff (deningerBarUnit c) + deningerBarUnit (deningerBarDiff c) :
      DeningerBarKothe) : DeningerBarWord → ℂ) w = (c : DeningerBarWord → ℂ) w
  rw [Submodule.coe_add, Pi.add_apply]
  exact deningerBarContraction (c : DeningerBarWord → ℂ) w

/-- **Split strict exactness**: every bar cycle is the boundary of its own explicit primitive. -/
theorem deningerBar_exact (c : DeningerBarKothe) (hc : deningerBarDiff c = 0) :
    deningerBarDiff (deningerBarUnit c) = c := by
  have h := deningerBarContraction_op c
  rw [hc, map_zero, add_zero] at h
  exact h

end

end RHTower
