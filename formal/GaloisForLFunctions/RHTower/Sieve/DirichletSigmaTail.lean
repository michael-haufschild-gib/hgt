import GaloisForLFunctions.RHTower.Sieve.DirichletBlockSigma
import GaloisForLFunctions.RHTower.Sieve.DirichletBlockTrivialBound

/-!
# The dyadic tail off the line

The dyadic assembly never looks at the summand: it is the triangle inequality across the blocks of
`sum_Ico_dyadic`.  Stating it for an arbitrary family therefore serves both the line and the
rectangle, and the corresponding statement for `n^(-1-it)` becomes an instance.
-/

namespace RHTower.Sieve

open Finset

/-- **Dyadic tail from per-block bounds, for an arbitrary summand.** -/
theorem norm_sum_Ico_dyadic_of_blockBound {E : Type*} [NormedAddCommGroup E] (A R : ℕ)
    (f : ℕ → E) (b : ℕ → ℝ)
    (hb : ∀ r < R, ‖∑ n ∈ Finset.Ico (A * 2 ^ r) (A * 2 ^ (r + 1)), f n‖ ≤ b r) :
    ‖∑ n ∈ Finset.Ico A (A * 2 ^ R), f n‖ ≤ ∑ r ∈ Finset.range R, b r := by
  refine le_trans (norm_sum_Ico_dyadic_le A f R) ?_
  exact Finset.sum_le_sum fun r hr => hb r (Finset.mem_range.mp hr)

/-- **Dyadic tail off the line.**  Each block contributes its saving, weighted by `N^(1-σ)`. -/
theorem dirichlet_tail_sigma_dyadic_le {σ : ℝ} (hσ : 0 ≤ σ) {t : ℝ} (ht : 0 < t) {A R : ℕ}
    (hA : 1 ≤ A) (k : ℕ → ℕ)
    (hk : ∀ r < R, 2 ≤ k r)
    (hfac : ∀ r < R, Nat.factorial (k r - 1) ≤ A * 2 ^ r)
    (hlow : ∀ r < R, 8 * Real.pi * ((A * 2 ^ r : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤ t)
    (hhigh : ∀ r < R, t ≤ 2 * Real.pi * 2 ^ (k r) * ((A * 2 ^ r : ℕ) : ℝ) ^ (k r - 1)
      * ((A * 2 ^ r : ℕ) : ℝ) ^ (-(1 / 3) : ℝ)) :
    ‖∑ n ∈ Finset.Ico A (A * 2 ^ R), (n : ℂ) ^ (-(σ : ℂ) - Complex.I * (t : ℂ))‖
      ≤ ∑ r ∈ Finset.range R,
          2560 * ((A * 2 ^ r : ℕ) : ℝ) ^ (1 - σ)
            * ((A * 2 ^ r : ℕ) : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ (k r)))) := by
  refine norm_sum_Ico_dyadic_of_blockBound A R _ _ fun r hrR => ?_
  have hN : 1 ≤ A * 2 ^ r := by
    calc 1 = 1 * 1 := (Nat.one_mul 1).symm
      _ ≤ A * 2 ^ r := Nat.mul_le_mul hA Nat.one_le_two_pow
  have hspan : A * 2 ^ (r + 1) = 2 * (A * 2 ^ r) := by ring
  rw [hspan]
  exact dirichlet_block_sigma_saving_of_small_factorial hσ ht hN (by omega) (by omega)
    (hk r hrR) (hfac r hrR) (hlow r hrR) (hhigh r hrR)

end RHTower.Sieve
