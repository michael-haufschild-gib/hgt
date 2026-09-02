import GaloisForLFunctions.RHTower.Sieve.KloostermanDistinctModulusTerminalBlock

/-!
# Terminal-block expansion of the distinct-modulus Kloosterman Gram

This module restores the source modulus weights around the literal terminal common-period blocks.
It identifies the existing distinct-modulus Gram exactly with that weighted carrier and proves its
fully explicit residual-length budget.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset

namespace RHTower.Sieve

noncomputable section

/-- Distinct-modulus Gram contribution written with literal terminal common-period blocks. -/
def kloostermanDistinctModulusTerminalGram
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ) (n k : ℕ) : ℂ :=
  ∑ q ∈ Q, star (w q) *
    ∑ r ∈ Q.erase q, w r *
      kloostermanNaturalCrossIntervalTerminalBlock M (q + 1) (r + 1)
        (Int.cast (n : ℤ)) (Int.cast (k : ℤ))

/-- The existing distinct-modulus Gram on `[1,M]` is exactly the weighted terminal-block Gram. -/
theorem kloostermanDistinctModulusGram_Icc_eq_terminalGram
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ) (n k : ℕ) :
    kloostermanDistinctModulusGram Q w (Finset.Icc 1 M) n k =
      kloostermanDistinctModulusTerminalGram M Q w n k := by
  unfold kloostermanDistinctModulusGram kloostermanDistinctModulusTerminalGram
  apply Finset.sum_congr rfl
  intro q hq
  apply congrArg (star (w q) * ·)
  apply Finset.sum_congr rfl
  intro r hr
  have hrq : r ≠ q := (Finset.mem_erase.mp hr).1
  rw [kloostermanCrossModulusCorrelation_Icc_eq_terminalBlock_of_ne
    M q r (Ne.symm hrq) (n : ℤ) (k : ℤ)]

/-- Full signed-kernel Gram entry: exact same-modulus part plus terminal distinct-modulus part. -/
theorem kloostermanIntegerKernelGram_Icc_eq_same_add_terminalGram
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ) (n k : ℕ) :
    kloostermanIntegerKernelGram Q w (Finset.Icc 1 M) n k =
      kloostermanSameModulusGram Q w (Finset.Icc 1 M) n k +
        kloostermanDistinctModulusTerminalGram M Q w n k := by
  rw [kloostermanIntegerKernelGram_eq_same_add_distinctModulus,
    kloostermanDistinctModulusGram_Icc_eq_terminalGram]

/-- Weighted exact-residual-length budget for the terminal distinct-modulus Gram. -/
theorem norm_kloostermanDistinctModulusTerminalGram_le
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ) (n k : ℕ) :
    ‖kloostermanDistinctModulusTerminalGram M Q w n k‖ ≤
      ∑ q ∈ Q, ‖w q‖ * ∑ r ∈ Q.erase q, ‖w r‖ *
        (((M % Nat.lcm (q + 1) (r + 1) : ℕ) : ℝ) *
          Nat.totient (q + 1) * Nat.totient (r + 1)) := by
  calc
    ‖kloostermanDistinctModulusTerminalGram M Q w n k‖ ≤
        ∑ q ∈ Q, ‖star (w q) *
          ∑ r ∈ Q.erase q, w r *
            kloostermanNaturalCrossIntervalTerminalBlock M (q + 1) (r + 1)
              (Int.cast (n : ℤ)) (Int.cast (k : ℤ))‖ := by
      unfold kloostermanDistinctModulusTerminalGram
      exact norm_sum_le _ _
    _ = ∑ q ∈ Q, ‖w q‖ * ‖∑ r ∈ Q.erase q, w r *
          kloostermanNaturalCrossIntervalTerminalBlock M (q + 1) (r + 1)
            (Int.cast (n : ℤ)) (Int.cast (k : ℤ))‖ := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [norm_mul, norm_star]
    _ ≤ ∑ q ∈ Q, ‖w q‖ * ∑ r ∈ Q.erase q,
          ‖w r * kloostermanNaturalCrossIntervalTerminalBlock M (q + 1) (r + 1)
            (Int.cast (n : ℤ)) (Int.cast (k : ℤ))‖ := by
      apply Finset.sum_le_sum
      intro q hq
      gcongr
      exact norm_sum_le _ _
    _ = ∑ q ∈ Q, ‖w q‖ * ∑ r ∈ Q.erase q,
          ‖w r‖ * ‖kloostermanNaturalCrossIntervalTerminalBlock M (q + 1) (r + 1)
            (Int.cast (n : ℤ)) (Int.cast (k : ℤ))‖ := by
      apply Finset.sum_congr rfl
      intro q hq
      congr 1
      apply Finset.sum_congr rfl
      intro r hr
      rw [norm_mul]
    _ ≤ ∑ q ∈ Q, ‖w q‖ * ∑ r ∈ Q.erase q, ‖w r‖ *
        (((M % Nat.lcm (q + 1) (r + 1) : ℕ) : ℝ) *
          Nat.totient (q + 1) * Nat.totient (r + 1)) := by
      apply Finset.sum_le_sum
      intro q hq
      gcongr with r hr
      exact norm_kloostermanNaturalCrossIntervalTerminalBlock_le
        M (q + 1) (r + 1) (Int.cast (n : ℤ)) (Int.cast (k : ℤ))

/-- Same weighted residual budget directly for the existing distinct-modulus Gram carrier. -/
theorem norm_kloostermanDistinctModulusGram_Icc_le_terminal
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ) (n k : ℕ) :
    ‖kloostermanDistinctModulusGram Q w (Finset.Icc 1 M) n k‖ ≤
      ∑ q ∈ Q, ‖w q‖ * ∑ r ∈ Q.erase q, ‖w r‖ *
        (((M % Nat.lcm (q + 1) (r + 1) : ℕ) : ℝ) *
          Nat.totient (q + 1) * Nat.totient (r + 1)) := by
  rw [kloostermanDistinctModulusGram_Icc_eq_terminalGram]
  exact norm_kloostermanDistinctModulusTerminalGram_le M Q w n k

end

end RHTower.Sieve
