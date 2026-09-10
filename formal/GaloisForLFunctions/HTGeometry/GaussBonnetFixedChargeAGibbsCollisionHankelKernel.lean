import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsCollisionHankelRank

namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Coefficients of the common spectral annihilator, padded by zeros. -/
def egbFixedChargeAGibbsCollisionAnnihilator (k : ℕ) : Fin (k + 3) → ℝ :=
  Fin.cases (1 / 81 : ℝ) (Fin.cases (-17 / 36 : ℝ) (Fin.cases (1 : ℝ) (fun _ : Fin k => 0)))

/-- The spectral annihilator is nonzero in every padded dimension. -/
theorem egbFixedChargeAGibbsCollisionAnnihilator_ne_zero (k : ℕ) :
    egbFixedChargeAGibbsCollisionAnnihilator k ≠ 0 := by
  intro h
  have he := congrFun h ((0 : Fin (k + 1)).succ.succ)
  change (1 : ℝ) = 0 at he
  norm_num at he

/-- The same monic quadratic annihilates every sufficiently large temporal collision Hankel section. -/
theorem egbFixedChargeAGibbsCollisionHankelMatrix_annihilator (n o k : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    (egbFixedChargeAGibbsCollisionHankelMatrix n o (k + 3) β E).mulVec
      (egbFixedChargeAGibbsCollisionAnnihilator k) = 0 := by
  funext i
  simp only [Matrix.mulVec, dotProduct, egbFixedChargeAGibbsCollisionHankelMatrix,
    egbFixedChargeAGibbsCollisionAnnihilator, Fin.sum_univ_succ, Fin.cases_zero,
    Fin.cases_succ, mul_zero, Finset.sum_const_zero, add_zero, mul_one, Pi.zero_apply]
  have h := egbFixedChargeAGibbsCollisionExcess_recurrence n ((i : ℕ) + o) β E
  simp only [Fin.val_zero, Fin.val_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
    Nat.zero_add, Nat.add_zero] at h ⊢
  norm_num at h ⊢
  linarith

end
end GaloisForLFunctions.HTGeometry
