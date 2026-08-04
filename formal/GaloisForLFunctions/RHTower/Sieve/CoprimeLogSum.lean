import GaloisForLFunctions.RHTower.Sieve.MRFibreDensity
import GaloisForLFunctions.RHTower.Sieve.CoprimeSquarefreeDyadic
import GaloisForLFunctions.RHTower.Sieve.BalancedPairsRescale

/-!
# The logarithmic mean of the deleted squarefree indicator

The weight of the card's step 2 is `μ²·1_{p∤·}`, whose count is `m·Dp/(p+1) + O(√m)` — the corpus's
coprime window estimate at starting point `0`.  The general passage from a square-root-accurate count
to a logarithmic mean therefore applies verbatim:

    ∑_{⌈u⌉ ≤ a ≤ ⌊2u⌋} μ²(a)·1_{p∤a}/a  →  (D p/(p+1)) · log 2.

This is the third and last logarithmic mean the card needs, and it matches the rescaled block mean
of `SharedSectorLimit.tendsto_blockMean_coprime` exactly.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction Filter Topology
open scoped ArithmeticFunction.Moebius

/-- The deleted density is nonnegative. -/
theorem coprime_block_density_nonneg {p : ℕ} (hp : p.Prime) :
    0 ≤ squarefreeDensity * (p : ℝ) / ((p : ℝ) + 1) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hD := squarefreeDensity_nonneg'
  positivity

/-- The weight is unit bounded. -/
theorem abs_coprimeSquarefreeWeight_le_one (p n : ℕ) :
    |coprimeSquarefreeWeight p n| ≤ 1 := by
  rw [coprimeSquarefreeWeight]
  split
  · norm_num
  · exact abs_moebius_sq_real_le_one n

/-- **The coprime squarefree count up to `m`, with square-root error.** -/
theorem abs_weightErr_coprime_le {p : ℕ} (hp : p.Prime) (m : ℕ) :
    |weightErr (coprimeSquarefreeWeight p) (squarefreeDensity * (p : ℝ) / ((p : ℝ) + 1)) m|
      ≤ 3 * Real.sqrt m + 3 := by
  have hR1 : 1 ≤ Nat.sqrt m + 1 := by omega
  have hRM : 0 + m ≤ (Nat.sqrt m + 1) ^ 2 := by
    have h := Nat.lt_succ_sqrt' m
    rw [zero_add]
    have hs : Nat.sqrt m + 1 = Nat.succ (Nat.sqrt m) := rfl
    rw [hs]
    exact le_of_lt h
  have hbase := abs_window_coprime_squarefree_sub_le (t := 0) (L := m) (R := Nat.sqrt m + 1)
    hp hR1 hRM
  rw [zero_add, Ioc_zero_eq_Icc_one, coprime_density_eq hp] at hbase
  have hval : weightErr (coprimeSquarefreeWeight p)
      (squarefreeDensity * (p : ℝ) / ((p : ℝ) + 1)) m
      = ∑ n ∈ Finset.Icc 1 m, (if p ∣ n then 0 else ((μ n : ℤ) : ℝ) ^ 2)
        - (m : ℝ) * (squarefreeDensity * (p : ℝ) / ((p : ℝ) + 1)) := by
    rw [weightErr, weightCount]
    congr 1
  rw [hval]
  refine le_trans hbase ?_
  have hs0 : (0 : ℝ) ≤ Real.sqrt m := Real.sqrt_nonneg _
  have hRle : ((Nat.sqrt m + 1 : ℕ) : ℝ) ≤ Real.sqrt m + 1 := by
    have := natSqrt_le_sqrt m
    push_cast
    linarith
  have hRgt : Real.sqrt m < ((Nat.sqrt m + 1 : ℕ) : ℝ) := sqrt_lt_natSqrt_succ m
  have hRpos : (0 : ℝ) < ((Nat.sqrt m + 1 : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ ((Nat.sqrt m + 1 : ℕ) : ℝ) := by exact_mod_cast hR1
    linarith
  have hquot : (m : ℝ) / ((Nat.sqrt m + 1 : ℕ) : ℝ) ≤ Real.sqrt m := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      have hspos : (0 : ℝ) < Real.sqrt m := Real.sqrt_pos.2 hm0
      rw [div_le_iff₀ hRpos]
      have hsq : Real.sqrt m * Real.sqrt m = (m : ℝ) := Real.mul_self_sqrt (le_of_lt hm0)
      nlinarith
  linarith

/-- **The logarithmic mean of the deleted squarefree indicator over a dyadic block.** -/
theorem tendsto_coprime_block_log_mean {p : ℕ} (hp : p.Prime) :
    Tendsto (fun u : ℝ =>
        ∑ a ∈ Finset.Icc ⌈u⌉₊ ⌊2 * u⌋₊, coprimeSquarefreeWeight p a / (a : ℝ))
      atTop (𝓝 (squarefreeDensity * (p : ℝ) / ((p : ℝ) + 1) * Real.log 2)) :=
  tendsto_block_log_mean_of_count (coprime_block_density_nonneg hp) (by norm_num)
    (abs_weightErr_coprime_le hp)

end RHTower.Sieve
