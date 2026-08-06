import GaloisForLFunctions.RHTower.Sieve.DirichletSigmaUniform

/-!
# The rectangle shape

Composing the per-block saving off the line with the depth criterion gives the analogue of the
Littlewood shape for `Re s = σ`: a head controlled by the integral comparison below the abscissa,
plus a count of blocks times the uniform saving.

The order is constant, as on the line, and the hypotheses are the same four per block with the depth
criterion carrying the extra width term `1 - σ`.
-/

namespace RHTower.Sieve

open Finset

/-- **Rectangle shape.**  Head plus a count of blocks times the uniform saving, off the line. -/
theorem norm_dirichlet_sigma_littlewood_shape {σ t : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (ht : 0 < t)
    {C R : ℕ} (hC : 3 ≤ C) (K : ℕ) {ε : ℝ} (hε : 0 < ε) (hK : 2 ≤ K)
    (hfac : ∀ r < R, Nat.factorial (K - 1) ≤ C * 2 ^ r)
    (hlow : ∀ r < R, 8 * Real.pi * ((C * 2 ^ r : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤ t)
    (hhigh : ∀ r < R, t ≤ 2 * Real.pi * 2 ^ K * ((C * 2 ^ r : ℕ) : ℝ) ^ (K - 1)
      * ((C * 2 ^ r : ℕ) : ℝ) ^ (-(1 / 3) : ℝ))
    (hdeep : ∀ r < R, Real.log (2560 / ε)
      ≤ (1 / (3 * (2 : ℝ) ^ K) - (1 - σ)) * Real.log ((C * 2 ^ r : ℕ) : ℝ)) :
    ‖∑ n ∈ Finset.Ico (1 : ℕ) (C * 2 ^ R), (n : ℂ) ^ (-(σ : ℂ) - Complex.I * (t : ℂ))‖
      ≤ (1 + (((C - 1 : ℕ) : ℝ) ^ (1 - σ) - 1) / (1 - σ) + ((C - 1 : ℕ) : ℝ) ^ (-σ))
        + (R : ℝ) * ε := by
  refine norm_dirichlet_sigma_partial_uniform hσ0 hσ1 hC fun r hrR => ?_
  have hN : 1 ≤ C * 2 ^ r := by
    calc 1 = 1 * 1 := (Nat.one_mul 1).symm
      _ ≤ C * 2 ^ r := Nat.mul_le_mul (by omega) Nat.one_le_two_pow
  have hspan : C * 2 ^ (r + 1) = 2 * (C * 2 ^ r) := by ring
  rw [hspan]
  refine le_trans
    (dirichlet_block_sigma_saving_of_small_factorial hσ0.le ht hN (by omega) (by omega) hK
      (hfac r hrR) (hlow r hrR) (hhigh r hrR)) ?_
  exact block_sigma_saving_le_of_log_ge hN hε (hdeep r hrR)

end RHTower.Sieve
