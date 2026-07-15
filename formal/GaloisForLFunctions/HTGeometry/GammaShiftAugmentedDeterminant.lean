import GaloisForLFunctions.HTGeometry.GammaShiftConfluentCasoratian
import GaloisForLFunctions.HTGeometry.GammaShiftDirichletResidual

/-! Exact augmented Gamma-jet determinant. -/

open scoped BigOperators

namespace GaloisForLFunctions

open Matrix Polynomial

noncomputable section

def gammaJetAugmentedMatrix {r : ℕ} (s : ℂ) (shift : Fin r → ℂ)
    (mult : Fin r → ℕ) (D : ℂ → ℂ) :
    Matrix (Fin (gammaJetOrder mult + 1)) (Fin (gammaJetOrder mult + 1)) ℂ :=
  fun k col => Fin.lastCases (D (s + (k : ℕ)))
    (fun a => iteratedDeriv (gammaJetSlotOrder mult a) Complex.Gamma
      (s + shift (gammaJetSlotNode mult a) + (k : ℕ))) col

def gammaJetAugmentedEliminatedMatrix {r : ℕ} (s : ℂ) (shift : Fin r → ℂ)
    (mult : Fin r → ℕ) (D : ℂ → ℂ) :
    Matrix (Fin (gammaJetOrder mult + 1)) (Fin (gammaJetOrder mult + 1)) ℂ :=
  let M := gammaJetAugmentedMatrix s shift mult D
  M.updateRow (Fin.last (gammaJetOrder mult))
    (∑ k : Fin (gammaJetOrder mult + 1),
      gammaJetAnnihilatorCoeff s shift mult (k : ℕ) • M k)

theorem det_gammaJetAugmentedEliminatedMatrix {r : ℕ}
    (s : ℂ) (shift : Fin r → ℂ) (mult : Fin r → ℕ) (D : ℂ → ℂ) :
    (gammaJetAugmentedEliminatedMatrix s shift mult D).det =
      (gammaJetAugmentedMatrix s shift mult D).det := by
  rw [gammaJetAugmentedEliminatedMatrix, Matrix.det_updateRow_sum]
  rw [show ((Fin.last (gammaJetOrder mult) : Fin (gammaJetOrder mult + 1)) : ℕ) =
      gammaJetOrder mult by rfl, gammaJetAnnihilatorCoeff_top]
  simp

theorem gammaJetAugmentedEliminatedMatrix_last_gamma {r : ℕ}
    (s : ℂ) (shift : Fin r → ℂ) (mult : Fin r → ℕ) (D : ℂ → ℂ)
    (hpole : ∀ i (p : ℕ), s + shift i ≠ -(p : ℂ))
    (a : Fin (gammaJetOrder mult)) :
    gammaJetAugmentedEliminatedMatrix s shift mult D
      (Fin.last (gammaJetOrder mult)) a.castSucc = 0 := by
  rw [gammaJetAugmentedEliminatedMatrix, Matrix.updateRow_self]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    gammaJetAugmentedMatrix, Fin.lastCases_castSucc]
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ =>
    gammaJetAnnihilatorCoeff s shift mult k *
      iteratedDeriv (gammaJetSlotOrder mult a) Complex.Gamma
        (s + shift (gammaJetSlotNode mult a) + k)) (gammaJetOrder mult + 1)]
  exact gammaJetAnnihilator_iteratedDeriv_sum_eq_zero s shift mult hpole
    (gammaJetSlotNode mult a) (gammaJetSlotOrderIso mult a).2.isLt

theorem gammaJetAugmentedEliminatedMatrix_last_dirichlet {r : ℕ}
    (s : ℂ) (shift : Fin r → ℂ) (mult : Fin r → ℕ) (D : ℂ → ℂ) :
    gammaJetAugmentedEliminatedMatrix s shift mult D
      (Fin.last (gammaJetOrder mult)) (Fin.last (gammaJetOrder mult)) =
        gammaJetAnnihilator s shift mult D := by
  rw [gammaJetAugmentedEliminatedMatrix, Matrix.updateRow_self]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    gammaJetAugmentedMatrix, Fin.lastCases_last]
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ =>
    gammaJetAnnihilatorCoeff s shift mult k * D (s + k))
    (gammaJetOrder mult + 1)]
  rfl

theorem gammaJetAugmentedEliminatedMatrix_minor {r : ℕ}
    (s : ℂ) (shift : Fin r → ℂ) (mult : Fin r → ℕ) (D : ℂ → ℂ) :
    (gammaJetAugmentedEliminatedMatrix s shift mult D).submatrix
      (Fin.last (gammaJetOrder mult)).succAbove
      (Fin.last (gammaJetOrder mult)).succAbove =
        confluentGammaShiftMatrix s shift mult := by
  rw [Fin.succAbove_last]
  ext k a
  rw [Matrix.submatrix_apply, gammaJetAugmentedEliminatedMatrix,
    Matrix.updateRow_ne (Fin.castSucc_ne_last k)]
  simp [gammaJetAugmentedMatrix, confluentGammaShiftMatrix]

theorem det_gammaJetAugmentedEliminatedMatrix_eq {r : ℕ}
    (s : ℂ) (shift : Fin r → ℂ) (mult : Fin r → ℕ) (D : ℂ → ℂ)
    (hpole : ∀ i (p : ℕ), s + shift i ≠ -(p : ℂ)) :
    (gammaJetAugmentedEliminatedMatrix s shift mult D).det =
      (confluentGammaShiftMatrix s shift mult).det *
        gammaJetAnnihilator s shift mult D := by
  rw [Matrix.det_succ_row _ (Fin.last (gammaJetOrder mult))]
  rw [Finset.sum_eq_single (Fin.last (gammaJetOrder mult))]
  · rw [gammaJetAugmentedEliminatedMatrix_last_dirichlet,
      gammaJetAugmentedEliminatedMatrix_minor]
    have hsign : ((-1 : ℂ) ^
        (((Fin.last (gammaJetOrder mult) : Fin (gammaJetOrder mult + 1)) : ℕ) +
          ((Fin.last (gammaJetOrder mult) : Fin (gammaJetOrder mult + 1)) : ℕ))) = 1 := by
      change ((-1 : ℂ) ^ (gammaJetOrder mult + gammaJetOrder mult)) = 1
      rw [show gammaJetOrder mult + gammaJetOrder mult = 2 * gammaJetOrder mult by omega,
        pow_mul]
      norm_num
    rw [hsign]
    rw [one_mul]
    exact mul_comm _ _
  · intro j _ hj
    induction j using Fin.lastCases with
    | last => exact (hj rfl).elim
    | cast a =>
        rw [gammaJetAugmentedEliminatedMatrix_last_gamma s shift mult D hpole a,
          mul_zero, zero_mul]
  · simp

/-- Equation (20): adjoining one value column multiplies the Gamma Casoratian by its canonical
Dirichlet residual. -/
theorem det_gammaJetAugmentedMatrix {r : ℕ}
    (s : ℂ) (shift : Fin r → ℂ) (mult : Fin r → ℕ) (D : ℂ → ℂ)
    (hpole : ∀ i (p : ℕ), s + shift i ≠ -(p : ℂ)) :
    (gammaJetAugmentedMatrix s shift mult D).det =
      (∏ i : Fin r, Complex.Gamma (s + shift i) ^ mult i) *
        (∏ i : Fin r, ∏ m : Fin (mult i), ((m : ℕ).factorial : ℂ)) *
          (∏ i : Fin r, ∏ j ∈ Finset.Ioi i,
            (shift j - shift i) ^ (mult i * mult j)) *
              gammaJetAnnihilator s shift mult D := by
  rw [← det_gammaJetAugmentedEliminatedMatrix,
    det_gammaJetAugmentedEliminatedMatrix_eq s shift mult D hpole,
    det_confluentGammaShiftMatrix s shift mult hpole]

end
end GaloisForLFunctions
