import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ReceivingCharges.LiteralUpwardRows
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.WeightedAffinePrimeWindowsAreUniform

/-!
# Exact multiplier support geometry

The actual literal rows have positive lower endpoints, a uniform
logarithmic width, and a quadratic source threshold for proper-power tails.
-/

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open Finset
open GaloisForLFunctions.CriticalArithmeticCorrelationTheory

def literalMultiplierLower (c : ℝ) (N n : ℕ) : ℕ :=
  ⌈(N : ℝ) / (c * Real.exp 1 * n)⌉₊

def literalMultiplierUpper (c : ℝ) (N n : ℕ) : ℕ :=
  ⌊((N : ℝ) + linearPrimeStrip c) / n⌋₊

def literalMultiplierWidth (c : ℝ) : ℝ :=
  |Real.log (2 * c * Real.exp 1)| + mertensWindowConstant + 1

theorem literalMultiplierWidth_nonneg (c : ℝ) : 0 ≤ literalMultiplierWidth c :=
  add_nonneg (add_nonneg (abs_nonneg _) mertensWindowConstant_nonneg) zero_le_one

/-- Positive horizon and receiving index give a positive lower multiplier endpoint. -/
theorem literalMultiplierLower_pos {c : ℝ} (hc : 0 < c) {N n : ℕ}
    (hN : 1 ≤ N) (hn : 1 ≤ n) : 1 ≤ literalMultiplierLower c N n := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlo : (N : ℝ) / (c * Real.exp 1 * n) ≤ literalMultiplierLower c N n := Nat.le_ceil _
  have hp : (0 : ℝ) < literalMultiplierLower c N n :=
    (div_pos hN0 (mul_pos (mul_pos hc (Real.exp_pos 1)) hn0)).trans_le hlo
  exact_mod_cast hp

/-- The complete supported interval has a single positive logarithmic mass bound. -/
theorem literalMultiplierWidth_bounds {c : ℝ} (hc : 0 < c) {N n : ℕ}
    (hN : 1 ≤ N) (hn : 1 ≤ n) (hB : linearPrimeStrip c ≤ N)
    (hHX : literalMultiplierLower c N n ≤ literalMultiplierUpper c N n) :
    Real.log (literalMultiplierUpper c N n) - Real.log (literalMultiplierLower c N n) +
      mertensWindowConstant + 1 ≤ literalMultiplierWidth c := by
  have h := (multiplier_interval_log_width hc hN hn hB hHX rfl rfl).2
  have habs := h.trans (le_abs_self (Real.log (2 * c * Real.exp 1)))
  dsimp only [literalMultiplierWidth]
  linarith only [habs]

/-- A receiving row below the quadratic source threshold has no active multiplier below that threshold. -/
theorem literalMultiplierLower_ge_sq {c : ℝ} (hc : 0 < c) {N n Q : ℕ}
    (hn : 1 ≤ n) (hprod : c * Real.exp 1 * n * (Q : ℝ) ^ 2 ≤ N) :
    Q ^ 2 ≤ literalMultiplierLower c N n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < c * Real.exp 1 * n := mul_pos (mul_pos hc (Real.exp_pos 1)) hn0
  have hlo : (Q : ℝ) ^ 2 ≤ (N : ℝ) / (c * Real.exp 1 * n) :=
    (le_div_iff₀ hden).mpr (by simpa only [mul_comm] using hprod)
  have hceil := hlo.trans (Nat.le_ceil ((N : ℝ) / (c * Real.exp 1 * n)))
  exact_mod_cast hceil

/-- One upper receiving endpoint suffices for the quadratic multiplier support condition. -/
theorem literalMultiplierLower_ge_sq_on_interval {c : ℝ} (hc : 0 < c)
    {N n Q Z : ℕ} (hn : n ∈ Icc 1 Z)
    (hprod : c * Real.exp 1 * Z * (Q : ℝ) ^ 2 ≤ N) :
    Q ^ 2 ≤ literalMultiplierLower c N n := by
  apply literalMultiplierLower_ge_sq hc (mem_Icc.mp hn).1
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (by exact_mod_cast (mem_Icc.mp hn).2)
      (mul_pos hc (Real.exp_pos 1)).le) (sq_nonneg (Q : ℝ))).trans hprod

#print axioms literalMultiplierWidth_bounds
#print axioms literalMultiplierLower_ge_sq_on_interval

/-- Earlier receiving rows have no smaller active multiplier endpoint. -/
theorem literalMultiplierLower_antitone {c : ℝ} (hc : 0 < c) {N n A : ℕ}
    (hn : 1 ≤ n) (hnA : n ≤ A) :
    literalMultiplierLower c N A ≤ literalMultiplierLower c N n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  apply Nat.ceil_mono
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg N)
    (mul_pos (mul_pos hc (Real.exp_pos 1)) hn0)
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hnA) (mul_pos hc (Real.exp_pos 1)).le)

/-- Quadratic multiplier support gives the full proper-power gain at the source cutoff. -/
theorem literalMultiplierLower_proper_power_tail {c : ℝ} {N n Q : ℕ}
    (hQ : 1 ≤ Q) (hH : Q ^ 2 ≤ literalMultiplierLower c N n) :
    (literalMultiplierLower c N n : ℝ) ^ (-(7 / 16 : ℝ)) ≤
      (Q : ℝ) ^ (-(7 / 8 : ℝ)) := by
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  calc
    _ ≤ ((Q : ℝ) ^ (2 : ℕ)) ^ (-(7 / 16 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hQ0) (by exact_mod_cast hH) (by norm_num)
    _ = _ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]
      norm_num

#print axioms literalMultiplierLower_antitone
#print axioms literalMultiplierLower_proper_power_tail

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
