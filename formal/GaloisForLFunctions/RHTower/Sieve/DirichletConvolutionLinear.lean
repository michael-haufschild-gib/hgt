import GaloisForLFunctions.RHTower.Sieve.DirichletBilinear

/-! # Bilinearity of finite Dirichlet convolution -/

noncomputable section

namespace RHTower.Sieve

theorem dirConv_add_left (N M : ℕ) (a₁ a₂ : Fin N → ℂ) (b : Fin M → ℂ)
    (r : Fin (N * M)) :
    dirConv N M (a₁ + a₂) b r = dirConv N M a₁ b r + dirConv N M a₂ b r := by
  classical
  rw [dirConv, dirConv, dirConv, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  simp only [Pi.add_apply]
  ring

theorem dirConv_sub_left (N M : ℕ) (a₁ a₂ : Fin N → ℂ) (b : Fin M → ℂ)
    (r : Fin (N * M)) :
    dirConv N M (a₁ - a₂) b r = dirConv N M a₁ b r - dirConv N M a₂ b r := by
  classical
  rw [dirConv, dirConv, dirConv, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  simp only [Pi.sub_apply]
  ring

theorem dirConv_smul_left (c : ℂ) (N M : ℕ) (a : Fin N → ℂ) (b : Fin M → ℂ)
    (r : Fin (N * M)) :
    dirConv N M (c • a) b r = c * dirConv N M a b r := by
  classical
  rw [dirConv, dirConv, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem dirConv_add_right (N M : ℕ) (a : Fin N → ℂ) (b₁ b₂ : Fin M → ℂ)
    (r : Fin (N * M)) :
    dirConv N M a (b₁ + b₂) r = dirConv N M a b₁ r + dirConv N M a b₂ r := by
  classical
  rw [dirConv, dirConv, dirConv, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  simp only [Pi.add_apply]
  ring

theorem dirConv_sub_right (N M : ℕ) (a : Fin N → ℂ) (b₁ b₂ : Fin M → ℂ)
    (r : Fin (N * M)) :
    dirConv N M a (b₁ - b₂) r = dirConv N M a b₁ r - dirConv N M a b₂ r := by
  classical
  rw [dirConv, dirConv, dirConv, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  simp only [Pi.sub_apply]
  ring

theorem dirConv_smul_right (c : ℂ) (N M : ℕ) (a : Fin N → ℂ) (b : Fin M → ℂ)
    (r : Fin (N * M)) :
    dirConv N M a (c • b) r = c * dirConv N M a b r := by
  classical
  rw [dirConv, dirConv, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

end RHTower.Sieve
