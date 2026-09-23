import GaloisForLFunctions.RHTower.Sieve.KloostermanSameModulusRamanujanEnergy

/-!
# Exact analytic frontier for the signed integer Kloosterman kernel

Transform output energy is decomposed into nonnegative Ramanujan main energy, equal-modulus
completion remainder, and terminal distinct-modulus carrier. Both residual carriers receive fully
explicit source-weighted budgets, yielding an unconditional scalar baseline without introducing an
analytic premise.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset

namespace RHTower.Sieve

noncomputable section

/-- Nonnegative real main energy from complete equal-modulus Kloosterman columns. -/
def kloostermanRamanujanMainEnergy
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) : ℝ :=
  ∑ q ∈ Q, ‖w q‖ ^ (2 : ℕ) * ((M : ℝ) / ((q + 1 : ℕ) : ℝ)) *
    ∑ m : ZMod (q + 1),
      ‖kloostermanCompleteColumnTransform (q + 1) B b m‖ ^ (2 : ℕ)

/-- Closed full-source budget for equal-modulus completion remainders. -/
def kloostermanSameModulusRemainderBudget
    (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) : ℝ :=
  ∑ n ∈ B, ‖b n‖ * ∑ k ∈ B, ‖b k‖ *
    ∑ q ∈ Q, ‖w q‖ ^ (2 : ℕ) *
      (((q + 1 : ℕ) : ℝ) * Nat.totient (q + 1))

/-- Closed full-source budget for terminal distinct-modulus carriers. -/
def kloostermanDistinctModulusTerminalBudget
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) : ℝ :=
  ∑ n ∈ B, ‖b n‖ * ∑ k ∈ B, ‖b k‖ *
    ∑ q ∈ Q, ‖w q‖ * ∑ r ∈ Q.erase q, ‖w r‖ *
      (((M % Nat.lcm (q + 1) (r + 1) : ℕ) : ℝ) *
        Nat.totient (q + 1) * Nat.totient (r + 1))

/-- Full same-modulus completion quadratic obeys its explicit source-weighted budget. -/
theorem norm_kloostermanSameModulusRemainderQuadratic_le_budget
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    ‖kloostermanSameModulusRemainderQuadratic M Q w B b‖ ≤
      kloostermanSameModulusRemainderBudget Q w B b := by
  calc
    ‖kloostermanSameModulusRemainderQuadratic M Q w B b‖ ≤
        ∑ n ∈ B, ‖star (b n) * ∑ k ∈ B, b k *
          kloostermanSameModulusRemainderGram M Q w n k‖ := by
      unfold kloostermanSameModulusRemainderQuadratic
      exact norm_sum_le _ _
    _ = ∑ n ∈ B, ‖b n‖ * ‖∑ k ∈ B, b k *
          kloostermanSameModulusRemainderGram M Q w n k‖ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [norm_mul, norm_star]
    _ ≤ ∑ n ∈ B, ‖b n‖ * ∑ k ∈ B,
          ‖b k * kloostermanSameModulusRemainderGram M Q w n k‖ := by
      apply Finset.sum_le_sum
      intro n hn
      gcongr
      exact norm_sum_le _ _
    _ = ∑ n ∈ B, ‖b n‖ * ∑ k ∈ B,
          ‖b k‖ * ‖kloostermanSameModulusRemainderGram M Q w n k‖ := by
      apply Finset.sum_congr rfl
      intro n hn
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [norm_mul]
    _ ≤ ∑ n ∈ B, ‖b n‖ * ∑ k ∈ B, ‖b k‖ *
        ∑ q ∈ Q, ‖w q‖ ^ (2 : ℕ) *
          (((q + 1 : ℕ) : ℝ) * Nat.totient (q + 1)) := by
      apply Finset.sum_le_sum
      intro n hn
      gcongr with k hk
      exact norm_kloostermanSameModulusRemainderGram_le M Q w n k
    _ = kloostermanSameModulusRemainderBudget Q w B b := rfl

/-- Full terminal distinct-modulus quadratic obeys its explicit source-weighted residual budget. -/
theorem norm_kloostermanDistinctModulusTerminalGramQuadratic_le_budget
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    ‖kloostermanDistinctModulusTerminalGramQuadratic M Q w B b‖ ≤
      kloostermanDistinctModulusTerminalBudget M Q w B b := by
  calc
    ‖kloostermanDistinctModulusTerminalGramQuadratic M Q w B b‖ ≤
        ∑ n ∈ B, ‖star (b n) * ∑ k ∈ B, b k *
          kloostermanDistinctModulusTerminalGram M Q w n k‖ := by
      unfold kloostermanDistinctModulusTerminalGramQuadratic
      exact norm_sum_le _ _
    _ = ∑ n ∈ B, ‖b n‖ * ‖∑ k ∈ B, b k *
          kloostermanDistinctModulusTerminalGram M Q w n k‖ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [norm_mul, norm_star]
    _ ≤ ∑ n ∈ B, ‖b n‖ * ∑ k ∈ B,
          ‖b k * kloostermanDistinctModulusTerminalGram M Q w n k‖ := by
      apply Finset.sum_le_sum
      intro n hn
      gcongr
      exact norm_sum_le _ _
    _ = ∑ n ∈ B, ‖b n‖ * ∑ k ∈ B,
          ‖b k‖ * ‖kloostermanDistinctModulusTerminalGram M Q w n k‖ := by
      apply Finset.sum_congr rfl
      intro n hn
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [norm_mul]
    _ ≤ ∑ n ∈ B, ‖b n‖ * ∑ k ∈ B, ‖b k‖ *
        ∑ q ∈ Q, ‖w q‖ * ∑ r ∈ Q.erase q, ‖w r‖ *
          (((M % Nat.lcm (q + 1) (r + 1) : ℕ) : ℝ) *
            Nat.totient (q + 1) * Nat.totient (r + 1)) := by
      apply Finset.sum_le_sum
      intro n hn
      gcongr with k hk
      exact norm_kloostermanDistinctModulusTerminalGram_le M Q w n k
    _ = kloostermanDistinctModulusTerminalBudget M Q w B b := rfl

/-- Exact analytic frontier: output energy is positive Ramanujan energy plus the two literal
completion carriers. -/
theorem ofReal_sum_norm_kloostermanIntegerKernelTransform_sq_eq_mainEnergy_add_remainders
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    ((∑ m ∈ Finset.Icc 1 M,
      ‖kloostermanIntegerKernelTransform Q w B b m‖ ^ (2 : ℕ) : ℝ) : ℂ) =
      (kloostermanRamanujanMainEnergy M Q w B b : ℂ) +
        kloostermanSameModulusRemainderQuadratic M Q w B b +
          kloostermanDistinctModulusTerminalGramQuadratic M Q w B b := by
  rw [ofReal_sum_norm_kloostermanIntegerKernelTransform_sq_eq_ramanujan_add_remainders,
    kloostermanSameModulusRamanujanMainQuadratic_eq_transformEnergy]
  rfl

/-- The two completion carriers have cancelling imaginary parts because output and main energies
are real. -/
theorem im_kloostermanCompletionQuadratics_add_eq_zero
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    (kloostermanSameModulusRemainderQuadratic M Q w B b +
      kloostermanDistinctModulusTerminalGramQuadratic M Q w B b).im = 0 := by
  have h := congrArg Complex.im
    (ofReal_sum_norm_kloostermanIntegerKernelTransform_sq_eq_mainEnergy_add_remainders
      M Q w B b)
  simp only [ofReal_im, add_im] at h ⊢
  linarith

/-- Combined completion carrier obeys the sum of its two closed budgets. -/
theorem norm_kloostermanCompletionQuadratics_le_budgets
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    ‖kloostermanSameModulusRemainderQuadratic M Q w B b +
      kloostermanDistinctModulusTerminalGramQuadratic M Q w B b‖ ≤
      kloostermanSameModulusRemainderBudget Q w B b +
        kloostermanDistinctModulusTerminalBudget M Q w B b := by
  exact (norm_add_le _ _).trans (add_le_add
    (norm_kloostermanSameModulusRemainderQuadratic_le_budget M Q w B b)
    (norm_kloostermanDistinctModulusTerminalGramQuadratic_le_budget M Q w B b))

/-- Fully scalar unconditional output-energy baseline with no analytic premise. -/
theorem sum_norm_kloostermanIntegerKernelTransform_sq_le_mainEnergy_add_budgets
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    (∑ m ∈ Finset.Icc 1 M,
      ‖kloostermanIntegerKernelTransform Q w B b m‖ ^ (2 : ℕ) : ℝ) ≤
      kloostermanRamanujanMainEnergy M Q w B b +
        kloostermanSameModulusRemainderBudget Q w B b +
          kloostermanDistinctModulusTerminalBudget M Q w B b := by
  have h := congrArg Complex.re
    (ofReal_sum_norm_kloostermanIntegerKernelTransform_sq_eq_mainEnergy_add_remainders
      M Q w B b)
  simp only [ofReal_re, add_re] at h
  calc
    (∑ m ∈ Finset.Icc 1 M,
        ‖kloostermanIntegerKernelTransform Q w B b m‖ ^ (2 : ℕ) : ℝ) =
        kloostermanRamanujanMainEnergy M Q w B b +
          (kloostermanSameModulusRemainderQuadratic M Q w B b).re +
            (kloostermanDistinctModulusTerminalGramQuadratic M Q w B b).re := h
    _ ≤ kloostermanRamanujanMainEnergy M Q w B b +
          ‖kloostermanSameModulusRemainderQuadratic M Q w B b‖ +
            ‖kloostermanDistinctModulusTerminalGramQuadratic M Q w B b‖ := by
      gcongr
      · exact Complex.re_le_norm _
      · exact Complex.re_le_norm _
    _ ≤ kloostermanRamanujanMainEnergy M Q w B b +
        kloostermanSameModulusRemainderBudget Q w B b +
          kloostermanDistinctModulusTerminalBudget M Q w B b := by
      gcongr
      · exact norm_kloostermanSameModulusRemainderQuadratic_le_budget M Q w B b
      · exact norm_kloostermanDistinctModulusTerminalGramQuadratic_le_budget M Q w B b

end

end RHTower.Sieve
