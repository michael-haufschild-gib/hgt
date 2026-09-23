import GaloisForLFunctions.RHTower.Sieve.KloostermanDistinctModulusTerminalGram

/-!
# Source quadratic forms for the terminal distinct-modulus Kloosterman Gram

The modulus-equality split is composed with the existing source-index Gram receiver. This yields
exact decompositions of transform energy and erased source off-diagonal terms, while retaining all
source coefficients, modulus weights, and terminal residual lengths.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset

namespace RHTower.Sieve

noncomputable section

/-- Source quadratic form built from equal-modulus Gram entries on `[1,M]`. -/
def kloostermanSameModulusGramQuadratic
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) : ℂ :=
  ∑ n ∈ B, star (b n) * ∑ k ∈ B, b k *
    kloostermanSameModulusGram Q w (Finset.Icc 1 M) n k

/-- Source quadratic form built from weighted terminal distinct-modulus Gram entries. -/
def kloostermanDistinctModulusTerminalGramQuadratic
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) : ℂ :=
  ∑ n ∈ B, star (b n) * ∑ k ∈ B, b k *
    kloostermanDistinctModulusTerminalGram M Q w n k

/-- Source off-diagonal form built from equal-modulus Gram entries. -/
def kloostermanSameModulusGramOffDiagonal
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) : ℂ :=
  ∑ n ∈ B, star (b n) * ∑ k ∈ B.erase n, b k *
    kloostermanSameModulusGram Q w (Finset.Icc 1 M) n k

/-- Source off-diagonal form built from weighted terminal distinct-modulus Gram entries. -/
def kloostermanDistinctModulusTerminalGramOffDiagonal
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) : ℂ :=
  ∑ n ∈ B, star (b n) * ∑ k ∈ B.erase n, b k *
    kloostermanDistinctModulusTerminalGram M Q w n k

/-- Full Gram quadratic form splits exactly by modulus equality and terminal distinct-modulus
blocks. -/
theorem kloostermanIntegerKernelGramQuadratic_Icc_eq_sameModulus_add_terminal
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    kloostermanIntegerKernelGramQuadratic Q w (Finset.Icc 1 M) B b =
      kloostermanSameModulusGramQuadratic M Q w B b +
        kloostermanDistinctModulusTerminalGramQuadratic M Q w B b := by
  unfold kloostermanIntegerKernelGramQuadratic
    kloostermanSameModulusGramQuadratic
    kloostermanDistinctModulusTerminalGramQuadratic
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← mul_add]
  apply congrArg (star (b n) * ·)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [kloostermanIntegerKernelGram_Icc_eq_same_add_terminalGram]
  ring

/-- Existing source off-diagonal form splits into equal-modulus and terminal distinct-modulus
parts. -/
theorem kloostermanIntegerKernelGramOffDiagonal_Icc_eq_sameModulus_add_terminal
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    kloostermanIntegerKernelGramOffDiagonal Q w (Finset.Icc 1 M) B b =
      kloostermanSameModulusGramOffDiagonal M Q w B b +
        kloostermanDistinctModulusTerminalGramOffDiagonal M Q w B b := by
  unfold kloostermanIntegerKernelGramOffDiagonal
    kloostermanSameModulusGramOffDiagonal
    kloostermanDistinctModulusTerminalGramOffDiagonal
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← mul_add]
  apply congrArg (star (b n) * ·)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [kloostermanIntegerKernelGram_Icc_eq_same_add_terminalGram]
  ring

/-- Output transform square energy equals the exact same-modulus plus terminal-modulus quadratic
decomposition. -/
theorem ofReal_sum_norm_kloostermanIntegerKernelTransform_sq_eq_sameModulus_add_terminal
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    ((∑ m ∈ Finset.Icc 1 M,
      ‖kloostermanIntegerKernelTransform Q w B b m‖ ^ (2 : ℕ) : ℝ) : ℂ) =
      kloostermanSameModulusGramQuadratic M Q w B b +
        kloostermanDistinctModulusTerminalGramQuadratic M Q w B b := by
  rw [ofReal_sum_norm_kloostermanIntegerKernelTransform_sq_eq_gramQuadratic,
    kloostermanIntegerKernelGramQuadratic_Icc_eq_sameModulus_add_terminal]

/-- Full source-weighted residual budget for the terminal distinct-modulus off-diagonal form. -/
theorem norm_kloostermanDistinctModulusTerminalGramOffDiagonal_le
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    ‖kloostermanDistinctModulusTerminalGramOffDiagonal M Q w B b‖ ≤
      ∑ n ∈ B, ‖b n‖ * ∑ k ∈ B.erase n, ‖b k‖ *
        ∑ q ∈ Q, ‖w q‖ * ∑ r ∈ Q.erase q, ‖w r‖ *
          (((M % Nat.lcm (q + 1) (r + 1) : ℕ) : ℝ) *
            Nat.totient (q + 1) * Nat.totient (r + 1)) := by
  calc
    ‖kloostermanDistinctModulusTerminalGramOffDiagonal M Q w B b‖ ≤
        ∑ n ∈ B, ‖star (b n) * ∑ k ∈ B.erase n, b k *
          kloostermanDistinctModulusTerminalGram M Q w n k‖ := by
      unfold kloostermanDistinctModulusTerminalGramOffDiagonal
      exact norm_sum_le _ _
    _ = ∑ n ∈ B, ‖b n‖ * ‖∑ k ∈ B.erase n, b k *
          kloostermanDistinctModulusTerminalGram M Q w n k‖ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [norm_mul, norm_star]
    _ ≤ ∑ n ∈ B, ‖b n‖ * ∑ k ∈ B.erase n,
          ‖b k * kloostermanDistinctModulusTerminalGram M Q w n k‖ := by
      apply Finset.sum_le_sum
      intro n hn
      gcongr
      exact norm_sum_le _ _
    _ = ∑ n ∈ B, ‖b n‖ * ∑ k ∈ B.erase n,
          ‖b k‖ * ‖kloostermanDistinctModulusTerminalGram M Q w n k‖ := by
      apply Finset.sum_congr rfl
      intro n hn
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [norm_mul]
    _ ≤ ∑ n ∈ B, ‖b n‖ * ∑ k ∈ B.erase n, ‖b k‖ *
        ∑ q ∈ Q, ‖w q‖ * ∑ r ∈ Q.erase q, ‖w r‖ *
          (((M % Nat.lcm (q + 1) (r + 1) : ℕ) : ℝ) *
            Nat.totient (q + 1) * Nat.totient (r + 1)) := by
      apply Finset.sum_le_sum
      intro n hn
      gcongr with k hk
      exact norm_kloostermanDistinctModulusTerminalGram_le M Q w n k

end

end RHTower.Sieve
