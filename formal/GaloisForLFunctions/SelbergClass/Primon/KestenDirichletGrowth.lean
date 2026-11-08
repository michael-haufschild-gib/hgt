import GaloisForLFunctions.SelbergClass.Primon.KestenDirichletGreenKernel

/-!
# Positive rank-one growth of the Dirichlet Green sections

Adding one terminal site increases the old Green block by exactly one
positive rank-one matrix. The terminal response specifies both the gain
in every quadratic form and the directions in which that gain vanishes.
-/

open _root_.RHTower Matrix
namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

private theorem gap_pos (p : Nat.Primes) : 0 < 1 - primeReciprocal p ^ 2 :=
  sub_pos.mpr (pow_lt_one₀ (primeReciprocal_pos p).le (primeReciprocal_lt_one p) (by decide))

private theorem denominator_pos (p : Nat.Primes) (n : ℕ) :
    0 < 1 - primeReciprocal p ^ (2 * n + 3) :=
  sub_pos.mpr (pow_lt_one₀ (primeReciprocal_pos p).le (primeReciprocal_lt_one p) (by omega))

/-- Scalar gain from moving the Dirichlet boundary out by one site. -/
def kestenDirichletGrowth (p : Nat.Primes) (n : ℕ) : ℝ :=
  primeReciprocal p * (1 - primeReciprocal p ^ 2) ^ 2 /
    ((1 - primeReciprocal p ^ (2 * n + 3)) *
      (1 - primeReciprocal p ^ (2 * (n + 1) + 3)))

theorem kestenDirichletGrowth_pos (p : Nat.Primes) (n : ℕ) :
    0 < kestenDirichletGrowth p n :=
  div_pos (mul_pos (primeReciprocal_pos p) (pow_pos (gap_pos p) 2))
    (mul_pos (denominator_pos p n) (denominator_pos p (n + 1)))

private theorem correction_step (p : Nat.Primes) (n : ℕ) :
    kestenDirichletCorrection p n - primeReciprocal p ^ 2 * kestenDirichletCorrection p (n + 1) =
      kestenDirichletGrowth p n := by
  rw [kestenDirichletCorrection_eq, kestenDirichletCorrection_eq, kestenDirichletGrowth]
  field_simp [(denominator_pos p n).ne', (denominator_pos p (n + 1)).ne']
  rw [show 2 * (n + 1) + 3 = (2 * n + 3) + 2 by omega,
    pow_add (primeReciprocal p) (2 * n + 3) 2]
  ring

private theorem terminal_step (p : Nat.Primes) (n : ℕ) (i : Fin (n + 1)) :
    kestenGreenEntry p i (n + 1) = primeReciprocal p * kestenGreenEntry p i n := by
  have hi : i.val ≤ n := by omega
  have h0 := kestenGreenEntry_propagation p i (n - i.val)
  have h1 := kestenGreenEntry_propagation p i (n - i.val + 1)
  rw [Nat.add_sub_of_le hi] at h0
  rw [show i.val + (n - i.val + 1) = n + 1 by omega, pow_succ] at h1
  rw [h1, h0]
  ring

/-- Each entry gains the product of its two terminal responses times one positive scalar. -/
theorem kestenDirichletGreen_entry_step (p : Nat.Primes) (n : ℕ) (i j : Fin (n + 1)) :
    kestenDirichletGreen p (n + 1) i.castSucc j.castSucc - kestenDirichletGreen p n i j =
      kestenDirichletGrowth p n * kestenGreenEntry p i n * kestenGreenEntry p j n := by
  rw [kestenDirichletGreen_entry, kestenDirichletGreen_entry]
  simp only [Fin.val_castSucc]
  rw [terminal_step p n i, terminal_step p n j, ← correction_step]
  ring

/-- The old block of the next Dirichlet inverse differs by a positive rank-one matrix. -/
theorem kestenDirichletGreen_block_step (p : Nat.Primes) (n : ℕ) :
    (kestenDirichletGreen p (n + 1)).submatrix Fin.castSucc Fin.castSucc =
      kestenDirichletGreen p n + kestenDirichletGrowth p n •
        Matrix.vecMulVec (kestenGreenTerminalResponse p n) (kestenGreenTerminalResponse p n) := by
  ext i j
  change kestenDirichletGreen p (n + 1) i.castSucc j.castSucc =
    kestenDirichletGreen p n i j + kestenDirichletGrowth p n *
      (kestenGreenEntry p i n * kestenGreenEntry p j n)
  have h := kestenDirichletGreen_entry_step p n i j
  linarith only [h]

/-- Every old entry strictly increases when the terminal boundary moves out one site. -/
theorem kestenDirichletGreen_entry_lt_succ (p : Nat.Primes) (n : ℕ) (i j : Fin (n + 1)) :
    kestenDirichletGreen p n i j < kestenDirichletGreen p (n + 1) i.castSucc j.castSucc := by
  apply sub_pos.mp
  rw [kestenDirichletGreen_entry_step]
  exact mul_pos (mul_pos (kestenDirichletGrowth_pos p n) (kestenGreenEntry_pos p i n))
    (kestenGreenEntry_pos p j n)

/-- Adding a terminal site changes every old-source energy by one squared response. -/
theorem kestenDirichletGreen_energy_step (p : Nat.Primes) (n : ℕ) (c : Fin (n + 1) → ℝ) :
    c ⬝ᵥ ((kestenDirichletGreen p (n + 1)).submatrix Fin.castSucc Fin.castSucc *ᵥ c) =
      c ⬝ᵥ (kestenDirichletGreen p n *ᵥ c) +
        kestenDirichletGrowth p n * (∑ i, c i * kestenGreenEntry p i n) ^ 2 := by
  have hform : c ⬝ᵥ ((kestenDirichletGrowth p n •
      Matrix.vecMulVec (kestenGreenTerminalResponse p n) (kestenGreenTerminalResponse p n)) *ᵥ c) =
      kestenDirichletGrowth p n * (c ⬝ᵥ kestenGreenTerminalResponse p n) ^ 2 := by
    rw [Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, IsCentralScalar.op_smul_eq_smul,
      dotProduct_smul, dotProduct_smul]
    have hc : kestenGreenTerminalResponse p n ⬝ᵥ c = c ⬝ᵥ kestenGreenTerminalResponse p n := by
      apply Finset.sum_congr rfl
      intro i _
      exact mul_comm _ _
    rw [hc]
    simp only [smul_eq_mul]
    ring
  rw [kestenDirichletGreen_block_step, Matrix.add_mulVec, dotProduct_add, hform]
  rfl

theorem kestenDirichletGreen_energy_le_succ (p : Nat.Primes) (n : ℕ) (c : Fin (n + 1) → ℝ) :
    c ⬝ᵥ (kestenDirichletGreen p n *ᵥ c) ≤
      c ⬝ᵥ ((kestenDirichletGreen p (n + 1)).submatrix Fin.castSucc Fin.castSucc *ᵥ c) := by
  rw [kestenDirichletGreen_energy_step]
  exact le_add_of_nonneg_right (mul_nonneg (kestenDirichletGrowth_pos p n).le (sq_nonneg _))

/-- The directions with no gain are exactly those orthogonal to the terminal response. -/
theorem kestenDirichletGreen_energy_step_eq_iff (p : Nat.Primes) (n : ℕ) (c : Fin (n + 1) → ℝ) :
    c ⬝ᵥ ((kestenDirichletGreen p (n + 1)).submatrix Fin.castSucc Fin.castSucc *ᵥ c) =
      c ⬝ᵥ (kestenDirichletGreen p n *ᵥ c) ↔ ∑ i, c i * kestenGreenEntry p i n = 0 := by
  rw [kestenDirichletGreen_energy_step, add_eq_left, mul_eq_zero]
  simp [(kestenDirichletGrowth_pos p n).ne']

end
end GaloisForLFunctions.SelbergClass.Primon
