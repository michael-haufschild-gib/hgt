import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenC3Coefficient
import GaloisForLFunctions.RHTower.Sieve.SiftTailDivisorEulerBound

/-!
# Literal Matomäki--Teräväinen `c₁,n` coefficient

This file defines the actual bounded-coefficient Legendre truncation error.  Every discarded
divisor of a quotient `n/m` remains a discarded smooth divisor of `n`; retaining that support
reduces the source `d₃(n)|c₁,n|` mean to the Rankin--Euler estimate without replacing the
coefficient or its convolution multiplicity by a premise.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Literal Legendre-truncation error `c₁,n`. -/
def mtC1Coefficient (α : ℕ → ℂ) (z D n : ℕ) : ℂ :=
  ∑ m ∈ n.divisors,
    α m * ((rho (n / m) z : ℂ) - (truncLegendre (n / m) z D : ℂ))

/-- Pointwise bounded-coefficient estimate retaining one discarded smooth divisor. -/
theorem norm_mtC1Coefficient_le
    (α : ℕ → ℂ) {z D n : ℕ} (hn : 0 < n)
    {B : ℝ} (hB : 0 ≤ B) (hα : ∀ m, ‖α m‖ ≤ B) :
    ‖mtC1Coefficient α z D n‖ ≤
      B * (n.divisors.card : ℝ) * siftTailDivisorCount z D n := by
  unfold mtC1Coefficient
  calc
    ‖∑ m ∈ n.divisors,
        α m * ((rho (n / m) z : ℂ) - (truncLegendre (n / m) z D : ℂ))‖ ≤
      ∑ m ∈ n.divisors,
        ‖α m * ((rho (n / m) z : ℂ) - (truncLegendre (n / m) z D : ℂ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _m ∈ n.divisors, B * siftTailDivisorCount z D n := by
      apply Finset.sum_le_sum
      intro m hm
      have hmDiv : m ∣ n := (Nat.mem_divisors.mp hm).1
      have hk : 0 < n / m :=
        Nat.div_pos (Nat.le_of_dvd hn hmDiv) (Nat.pos_of_mem_divisors hm)
      have hkDiv : n / m ∣ n := by
        refine ⟨m, ?_⟩
        exact (Nat.div_mul_cancel hmDiv).symm
      have hnorm :
          ‖(rho (n / m) z : ℂ) - (truncLegendre (n / m) z D : ℂ)‖ ≤
            (truncTail (n / m) z D : ℝ) := by
        rw [← Int.cast_natCast, ← Int.cast_sub, Complex.norm_intCast]
        exact_mod_cast abs_rho_sub_truncLegendre_le (k := n / m) (z := z) (D := D) hk
      have htail := truncTail_le_siftTailDivisorCount (z := z) (D := D) hkDiv
      rw [norm_mul]
      exact mul_le_mul (hα m) (hnorm.trans htail) (norm_nonneg _) hB
    _ = B * (n.divisors.card : ℝ) * siftTailDivisorCount z D n := by
      simp [Finset.sum_const, nsmul_eq_mul]
      ring

/-- The source `d₃` weight and convolution multiplicity cost exactly a cube of `d(n)`. -/
theorem ternaryDivisorCount_mul_norm_mtC1Coefficient_le
    (α : ℕ → ℂ) {z D n : ℕ} (hn : 0 < n)
    {B : ℝ} (hB : 0 ≤ B) (hα : ∀ m, ‖α m‖ ≤ B) :
    (ternaryDivisorCount n : ℝ) * ‖mtC1Coefficient α z D n‖ ≤
      B * weightedSiftTailDivisorCount 3 z D n := by
  have hd3 : (ternaryDivisorCount n : ℝ) ≤ (n.divisors.card : ℝ) ^ 2 := by
    exact_mod_cast ternaryDivisorCount_le_sq hn
  have hc := norm_mtC1Coefficient_le α (z := z) (D := D) hn hB hα
  have htail : 0 ≤ siftTailDivisorCount z D n := by
    unfold siftTailDivisorCount
    positivity
  have hd : 0 ≤ (n.divisors.card : ℝ) := Nat.cast_nonneg _
  unfold weightedSiftTailDivisorCount
  calc
    (ternaryDivisorCount n : ℝ) * ‖mtC1Coefficient α z D n‖ ≤
      ((n.divisors.card : ℝ) ^ 2) *
        (B * (n.divisors.card : ℝ) * siftTailDivisorCount z D n) := by
      exact mul_le_mul hd3 hc (norm_nonneg _) (by positivity)
    _ = B * (((n.divisors.card : ℝ) ^ 3) * siftTailDivisorCount z D n) := by ring

/-- Full arithmetic `d₃(n)|c₁,n|` estimate before paper-scale substitution. -/
theorem sum_ternaryDivisorCount_mul_norm_mtC1Coefficient_le
    (α : ℕ → ℂ) {z D Y : ℕ} (hz : 2 ≤ z) (hD : 0 < D) (hY : 1 ≤ Y)
    {B : ℝ} (hB : 0 ≤ B) (hα : ∀ m, ‖α m‖ ≤ B) :
    ∑ n ∈ Finset.Icc 1 Y,
        (ternaryDivisorCount n : ℝ) * ‖mtC1Coefficient α z D n‖ ≤
      B * ((Y : ℝ) * (1 + Real.log (Y : ℝ)) ^ (2 ^ 3 - 1) *
        ((D : ℝ) ^ (-(1 / Real.log z)) *
          Real.exp ((((2 : ℝ) ^ 3) * Real.exp 1) *
            (logLog z + mertensSecondUpperConst)))) := by
  have hmean := sum_weightedSiftTailDivisorCount_le 3 z D Y hY
  have heuler := sum_largeSiftDivisors_card_pow_div_le 3 hz hD
  have hfront : 0 ≤ (Y : ℝ) *
      (1 + Real.log (Y : ℝ)) ^ (2 ^ 3 - 1) := by
    have hlog : 0 ≤ Real.log (Y : ℝ) := Real.log_nonneg (by exact_mod_cast hY)
    positivity
  calc
    ∑ n ∈ Finset.Icc 1 Y,
        (ternaryDivisorCount n : ℝ) * ‖mtC1Coefficient α z D n‖ ≤
      B * ∑ n ∈ Finset.Icc 1 Y, weightedSiftTailDivisorCount 3 z D n := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro n hnMem
      exact ternaryDivisorCount_mul_norm_mtC1Coefficient_le α (by
        rw [Finset.mem_Icc] at hnMem
        omega) hB hα
    _ ≤ B * ((Y : ℝ) * (1 + Real.log (Y : ℝ)) ^ (2 ^ 3 - 1) *
        ∑ e ∈ largeSiftDivisors z D,
          ((e.divisors.card : ℝ) ^ 3) / (e : ℝ)) :=
      mul_le_mul_of_nonneg_left hmean hB
    _ ≤ B * ((Y : ℝ) * (1 + Real.log (Y : ℝ)) ^ (2 ^ 3 - 1) *
        ((D : ℝ) ^ (-(1 / Real.log z)) *
          Real.exp ((((2 : ℝ) ^ 3) * Real.exp 1) *
            (logLog z + mertensSecondUpperConst)))) := by
      apply mul_le_mul_of_nonneg_left _ hB
      exact mul_le_mul_of_nonneg_left heuler hfront

end

end RHTower.Sieve
