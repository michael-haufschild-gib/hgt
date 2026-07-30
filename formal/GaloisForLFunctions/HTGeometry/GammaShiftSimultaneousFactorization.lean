import GaloisForLFunctions.HTGeometry.GammaShiftAugmentedDeterminant

/-! Exact simultaneous block factorization. -/

open scoped BigOperators

namespace GaloisForLFunctions

open Matrix

noncomputable section

def gammaJetShiftedConsecutiveIndex {r q : ℕ} (mult : Fin r → ℕ)
    (h : Fin q) (k : Fin (gammaJetOrder mult + 1)) :
    Fin (gammaJetOrder mult + q) :=
  ⟨(h : ℕ) + (k : ℕ), by
    have hh := h.isLt
    have hk := k.isLt
    omega⟩

@[simp] theorem gammaJetShiftedConsecutiveIndex_val {r q : ℕ}
    (mult : Fin r → ℕ) (h : Fin q) (k : Fin (gammaJetOrder mult + 1)) :
    (gammaJetShiftedConsecutiveIndex mult h k : ℕ) = (h : ℕ) + (k : ℕ) := rfl

theorem gammaJetShiftedConsecutiveIndex_last {r q : ℕ} (mult : Fin r → ℕ)
    (h : Fin q) :
    gammaJetShiftedConsecutiveIndex mult h (Fin.last (gammaJetOrder mult)) =
      Fin.natAdd (gammaJetOrder mult) h := by
  ext
  simp [gammaJetShiftedConsecutiveIndex]
  omega

theorem gammaJetShiftedConsecutiveIndex_le_bottom {r q : ℕ} (mult : Fin r → ℕ)
    (h : Fin q) (k : Fin (gammaJetOrder mult + 1)) :
    gammaJetShiftedConsecutiveIndex mult h k ≤ Fin.natAdd (gammaJetOrder mult) h := by
  rw [Fin.le_def]
  simp [gammaJetShiftedConsecutiveIndex]
  omega

def gammaJetSimultaneousEliminationMatrix {r q : ℕ}
    (s : ℂ) (shift : Fin r → ℂ) (mult : Fin r → ℕ) :
    Matrix (Fin (gammaJetOrder mult + q)) (Fin (gammaJetOrder mult + q)) ℂ :=
  fun row col => Fin.addCases
    (fun i => if col = Fin.castAdd q i then 1 else 0)
    (fun h => ∑ k : Fin (gammaJetOrder mult + 1),
      if col = gammaJetShiftedConsecutiveIndex mult h k then
        gammaJetAnnihilatorCoeff (s + (h : ℕ)) shift mult (k : ℕ)
      else 0) row

theorem gammaJetSimultaneousEliminationMatrix_blockTriangular {r q : ℕ}
    (s : ℂ) (shift : Fin r → ℂ) (mult : Fin r → ℕ) :
    Matrix.BlockTriangular (gammaJetSimultaneousEliminationMatrix (q := q) s shift mult)
      OrderDual.toDual := by
  intro row col hrowcol
  change row < col at hrowcol
  induction row using Fin.addCases with
  | left i =>
      rw [gammaJetSimultaneousEliminationMatrix, Fin.addCases_left, if_neg]
      exact ne_of_gt hrowcol
  | right h =>
      rw [gammaJetSimultaneousEliminationMatrix, Fin.addCases_right]
      apply Finset.sum_eq_zero
      intro k _
      rw [if_neg]
      intro heq
      subst col
      exact (not_lt_of_ge (gammaJetShiftedConsecutiveIndex_le_bottom mult h k)) hrowcol

@[simp] theorem gammaJetSimultaneousEliminationMatrix_diagonal {r q : ℕ}
    (s : ℂ) (shift : Fin r → ℂ) (mult : Fin r → ℕ)
    (row : Fin (gammaJetOrder mult + q)) :
    gammaJetSimultaneousEliminationMatrix (q := q) s shift mult row row = 1 := by
  induction row using Fin.addCases with
  | left i =>
      simp [gammaJetSimultaneousEliminationMatrix]
  | right h =>
      rw [gammaJetSimultaneousEliminationMatrix, Fin.addCases_right]
      rw [Finset.sum_eq_single (Fin.last (gammaJetOrder mult))]
      · rw [if_pos (gammaJetShiftedConsecutiveIndex_last mult h).symm]
        simpa using gammaJetAnnihilatorCoeff_top (s + (h : ℕ)) shift mult
      · intro k _ hk
        rw [if_neg]
        intro heq
        have hval := congrArg Fin.val heq
        have : k = Fin.last (gammaJetOrder mult) := by
          apply Fin.ext
          simp [gammaJetShiftedConsecutiveIndex] at hval ⊢
          omega
        exact hk this
      · simp

theorem det_gammaJetSimultaneousEliminationMatrix {r q : ℕ}
    (s : ℂ) (shift : Fin r → ℂ) (mult : Fin r → ℕ) :
    (gammaJetSimultaneousEliminationMatrix (q := q) s shift mult).det = 1 := by
  rw [Matrix.det_of_lowerTriangular _
    (gammaJetSimultaneousEliminationMatrix_blockTriangular s shift mult)]
  simp

theorem gammaJetSimultaneousEliminationMatrix_mul_top {r q : ℕ}
    (s : ℂ) (shift : Fin r → ℂ) (mult : Fin r → ℕ)
    (M : Matrix (Fin (gammaJetOrder mult + q))
      (Fin (gammaJetOrder mult + q)) ℂ)
    (i : Fin (gammaJetOrder mult)) (col : Fin (gammaJetOrder mult + q)) :
    (gammaJetSimultaneousEliminationMatrix (q := q) s shift mult * M)
      (Fin.castAdd q i) col = M (Fin.castAdd q i) col := by
  rw [Matrix.mul_apply]
  simp only [gammaJetSimultaneousEliminationMatrix, Fin.addCases_left]
  rw [Finset.sum_eq_single (Fin.castAdd q i)]
  · simp
  · intro j _ hj
    rw [if_neg hj, zero_mul]
  · simp

theorem gammaJetSimultaneousEliminationMatrix_mul_bottom {r q : ℕ}
    (s : ℂ) (shift : Fin r → ℂ) (mult : Fin r → ℕ)
    (M : Matrix (Fin (gammaJetOrder mult + q))
      (Fin (gammaJetOrder mult + q)) ℂ)
    (h : Fin q) (col : Fin (gammaJetOrder mult + q)) :
    (gammaJetSimultaneousEliminationMatrix (q := q) s shift mult * M)
      (Fin.natAdd (gammaJetOrder mult) h) col =
      ∑ k : Fin (gammaJetOrder mult + 1),
        gammaJetAnnihilatorCoeff (s + (h : ℕ)) shift mult (k : ℕ) *
          M (gammaJetShiftedConsecutiveIndex mult h k) col := by
  rw [Matrix.mul_apply]
  simp only [gammaJetSimultaneousEliminationMatrix, Fin.addCases_right]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_eq_single (gammaJetShiftedConsecutiveIndex mult h k)]
  · simp
  · intro j _ hj
    rw [if_neg hj, zero_mul]
  · simp

def gammaZetaJetMixedMatrix {r q : ℕ} (s : ℂ) (shift : Fin r → ℂ)
    (mult : Fin r → ℕ) (f : Fin q → ℂ → ℂ) :
    Matrix (Fin (gammaJetOrder mult + q)) (Fin (gammaJetOrder mult + q)) ℂ :=
  fun row col => Fin.addCases
    (fun a => iteratedDeriv (gammaJetSlotOrder mult a) Complex.Gamma
      (s + shift (gammaJetSlotNode mult a) + (row : ℕ)))
    (fun j => f j (s + (row : ℕ))) col

def gammaZetaJetResidualMatrix {r q : ℕ} (s : ℂ) (shift : Fin r → ℂ)
    (mult : Fin r → ℕ) (f : Fin q → ℂ → ℂ) : Matrix (Fin q) (Fin q) ℂ :=
  fun h j => gammaJetAnnihilator (s + (h : ℕ)) shift mult (f j)

theorem gammaJetSimultaneousEliminated_bottom_gamma {r q : ℕ}
    (s : ℂ) (shift : Fin r → ℂ) (mult : Fin r → ℕ) (f : Fin q → ℂ → ℂ)
    (hpole : ∀ i (p : ℕ), s + shift i ≠ -(p : ℂ))
    (h : Fin q) (a : Fin (gammaJetOrder mult)) :
    (gammaJetSimultaneousEliminationMatrix (q := q) s shift mult *
      gammaZetaJetMixedMatrix s shift mult f)
        (Fin.natAdd (gammaJetOrder mult) h) (Fin.castAdd q a) = 0 := by
  rw [gammaJetSimultaneousEliminationMatrix_mul_bottom]
  simp only [gammaZetaJetMixedMatrix, Fin.addCases_left]
  simp only [gammaJetShiftedConsecutiveIndex_val]
  simp only [Nat.cast_add]
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ =>
    gammaJetAnnihilatorCoeff (s + (h : ℕ)) shift mult k *
      iteratedDeriv (gammaJetSlotOrder mult a) Complex.Gamma
        (s + shift (gammaJetSlotNode mult a) + ((h : ℕ) + k)))
      (gammaJetOrder mult + 1)]
  have hpole' : ∀ i (p : ℕ), s + (h : ℕ) + shift i ≠ -(p : ℂ) := by
    intro i p hzero
    apply hpole i (p + (h : ℕ))
    push_cast
    linear_combination hzero
  simpa only [add_assoc, add_left_comm, add_comm] using!
    gammaJetAnnihilator_iteratedDeriv_sum_eq_zero
      (s + (h : ℕ)) shift mult hpole' (gammaJetSlotNode mult a)
        (gammaJetSlotOrderIso mult a).2.isLt

theorem gammaJetSimultaneousEliminated_bottom_value {r q : ℕ}
    (s : ℂ) (shift : Fin r → ℂ) (mult : Fin r → ℕ) (f : Fin q → ℂ → ℂ)
    (h j : Fin q) :
    (gammaJetSimultaneousEliminationMatrix (q := q) s shift mult *
      gammaZetaJetMixedMatrix s shift mult f)
        (Fin.natAdd (gammaJetOrder mult) h) (Fin.natAdd (gammaJetOrder mult) j) =
      gammaZetaJetResidualMatrix s shift mult f h j := by
  rw [gammaJetSimultaneousEliminationMatrix_mul_bottom]
  simp only [gammaZetaJetMixedMatrix, Fin.addCases_right,
    gammaZetaJetResidualMatrix, gammaJetAnnihilator]
  simp only [gammaJetShiftedConsecutiveIndex_val]
  simp only [Nat.cast_add]
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ =>
    gammaJetAnnihilatorCoeff (s + (h : ℕ)) shift mult k *
      f j (s + ((h : ℕ) + k))) (gammaJetOrder mult + 1)]
  apply Finset.sum_congr rfl
  intro k _
  congr 2
  ring

theorem gammaJetSimultaneousEliminated_eq_block {r q : ℕ}
    (s : ℂ) (shift : Fin r → ℂ) (mult : Fin r → ℕ) (f : Fin q → ℂ → ℂ)
    (hpole : ∀ i (p : ℕ), s + shift i ≠ -(p : ℂ)) :
    Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm
      (gammaJetSimultaneousEliminationMatrix (q := q) s shift mult *
        gammaZetaJetMixedMatrix s shift mult f) =
      Matrix.fromBlocks
        (confluentGammaShiftMatrix s shift mult)
        (fun k j => f j (s + (k : ℕ))) 0
        (gammaZetaJetResidualMatrix s shift mult f) := by
  ext row col
  rcases row with k | h <;> rcases col with a | j
  · simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_symm, finSumFinEquiv_apply_left]
    rw [gammaJetSimultaneousEliminationMatrix_mul_top]
    change gammaZetaJetMixedMatrix s shift mult f (Fin.castAdd q k)
      (Fin.castAdd q a) = confluentGammaShiftMatrix s shift mult k a
    simp [gammaZetaJetMixedMatrix, confluentGammaShiftMatrix]
  · simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_symm, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
    rw [gammaJetSimultaneousEliminationMatrix_mul_top]
    change gammaZetaJetMixedMatrix s shift mult f (Fin.castAdd q k)
      (Fin.natAdd (gammaJetOrder mult) j) = f j (s + (k : ℕ))
    simp [gammaZetaJetMixedMatrix]
  · simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_symm, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
    change (gammaJetSimultaneousEliminationMatrix (q := q) s shift mult *
      gammaZetaJetMixedMatrix s shift mult f)
        (Fin.natAdd (gammaJetOrder mult) h) (Fin.castAdd q a) = 0
    exact gammaJetSimultaneousEliminated_bottom_gamma s shift mult f hpole h a
  · simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_symm, finSumFinEquiv_apply_right]
    change (gammaJetSimultaneousEliminationMatrix (q := q) s shift mult *
      gammaZetaJetMixedMatrix s shift mult f)
        (Fin.natAdd (gammaJetOrder mult) h)
          (Fin.natAdd (gammaJetOrder mult) j) =
      gammaZetaJetResidualMatrix s shift mult f h j
    exact gammaJetSimultaneousEliminated_bottom_value s shift mult f h j

/-- Equation (D2): exact block factorization after eliminating every Gamma jet column. -/
theorem det_gammaZetaJetMixedMatrix {r q : ℕ}
    (s : ℂ) (shift : Fin r → ℂ) (mult : Fin r → ℕ) (f : Fin q → ℂ → ℂ)
    (hpole : ∀ i (p : ℕ), s + shift i ≠ -(p : ℂ)) :
    (gammaZetaJetMixedMatrix s shift mult f).det =
      (confluentGammaShiftMatrix s shift mult).det *
        (gammaZetaJetResidualMatrix s shift mult f).det := by
  let E := gammaJetSimultaneousEliminationMatrix (q := q) s shift mult
  let M := gammaZetaJetMixedMatrix s shift mult f
  have hdetEM : (E * M).det = M.det := by
    rw [Matrix.det_mul, show E.det = 1 from
      det_gammaJetSimultaneousEliminationMatrix (q := q) s shift mult, one_mul]
  have hblockdet : (E * M).det =
      (confluentGammaShiftMatrix s shift mult).det *
        (gammaZetaJetResidualMatrix s shift mult f).det := by
    calc
      (E * M).det =
          (Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm (E * M)).det :=
        (Matrix.det_reindex_self finSumFinEquiv.symm (E * M)).symm
      _ = (Matrix.fromBlocks
          (confluentGammaShiftMatrix s shift mult)
          (fun k j => f j (s + (k : ℕ))) 0
          (gammaZetaJetResidualMatrix s shift mult f)).det := by
        rw [gammaJetSimultaneousEliminated_eq_block s shift mult f hpole]
        rfl
      _ = (confluentGammaShiftMatrix s shift mult).det *
          (gammaZetaJetResidualMatrix s shift mult f).det :=
        Matrix.det_fromBlocks_zero₂₁ _ _ _
  exact hdetEM.symm.trans hblockdet

end
end GaloisForLFunctions
