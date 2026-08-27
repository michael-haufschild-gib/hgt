import GaloisForLFunctions.RHTower.Sieve.DivisorMomentEulerBound
import GaloisForLFunctions.RHTower.Sieve.MinorantDecomposition

/-!
# Mean square of the minorant truncation tail

This file composes the Rankin bound for the discarded Legendre divisors with the divisor-moment
mean square and its Euler-product estimate. It supplies the `c₁,n` estimate in
Matomäki--Teräväinen, Lemma 2.3(i), up to the final choice of the external `X`-parameters.
-/

namespace RHTower.Sieve

open Finset

/-- Lcm form of the explicit sifting-modulus pair bound. -/
theorem sum_pair_lcm_siftModulus_invLog_le_logLog
    {z : ℕ} (hz : 2 ≤ z) :
    ∑ e₁ ∈ (siftModulus z).divisors, ∑ e₂ ∈ (siftModulus z).divisors,
        (e₁ : ℝ) ^ (1 / Real.log z) * (e₂ : ℝ) ^ (1 / Real.log z) /
          (e₁.lcm e₂ : ℝ) ≤
      Real.exp ((2 * Real.exp 1 + Real.exp 2) *
        (logLog z + mertensSecondUpperConst)) := by
  rw [show (∑ e₁ ∈ (siftModulus z).divisors, ∑ e₂ ∈ (siftModulus z).divisors,
      (e₁ : ℝ) ^ (1 / Real.log z) * (e₂ : ℝ) ^ (1 / Real.log z) /
        (e₁.lcm e₂ : ℝ)) =
      ∑ e₁ ∈ (siftModulus z).divisors, ∑ e₂ ∈ (siftModulus z).divisors,
        ((e₁ : ℝ) * (e₂ : ℝ)) ^ (1 / Real.log z - 1) *
          (e₁.gcd e₂ : ℝ) by
    apply Finset.sum_congr rfl
    intro e₁ he₁
    apply Finset.sum_congr rfl
    intro e₂ he₂
    exact pair_term_eq (Nat.pos_of_mem_divisors he₁)
      (Nat.pos_of_mem_divisors he₂) (1 / Real.log z)]
  exact sum_pair_gcd_siftModulus_invLog_le_logLog hz

/-- Generic Rankin mean square for the discarded Legendre divisors. -/
theorem sum_sq_truncTail_le
    {Y z D : ℕ} {α : ℝ} (hα : 0 < α) (hD : 0 < D) :
    ∑ n ∈ Finset.Icc 1 Y, (truncTail n z D : ℝ) ^ 2 ≤
      (D : ℝ) ^ (-2 * α) * (Y : ℝ) *
        ∑ e₁ ∈ (siftModulus z).divisors,
          ∑ e₂ ∈ (siftModulus z).divisors,
            (e₁ : ℝ) ^ α * (e₂ : ℝ) ^ α / (e₁.lcm e₂ : ℝ) := by
  let moment : ℕ → ℝ := fun n =>
    ∑ e ∈ (Nat.gcd n (siftModulus z)).divisors, (e : ℝ) ^ α
  have hDpow_nonneg : 0 ≤ (D : ℝ) ^ (-α) :=
    Real.rpow_nonneg (Nat.cast_nonneg D) _
  have hterm : ∀ n ∈ Finset.Icc 1 Y,
      (truncTail n z D : ℝ) ^ 2 ≤
        ((D : ℝ) ^ (-α) * moment n) ^ 2 := by
    intro n _
    have hmoment_nonneg : 0 ≤ moment n := by
      exact Finset.sum_nonneg fun e _ =>
        Real.rpow_nonneg (Nat.cast_nonneg e) α
    exact (sq_le_sq₀ (Nat.cast_nonneg _) (mul_nonneg hDpow_nonneg hmoment_nonneg)).2
      (truncTail_le_rankin hα hD)
  have hrpow_sq : ((D : ℝ) ^ (-α)) ^ 2 = (D : ℝ) ^ (-2 * α) := by
    have hDR : 0 < (D : ℝ) := by exact_mod_cast hD
    rw [pow_two, ← Real.rpow_add hDR]
    congr 1
    ring
  calc
    ∑ n ∈ Finset.Icc 1 Y, (truncTail n z D : ℝ) ^ 2 ≤
        ∑ n ∈ Finset.Icc 1 Y, ((D : ℝ) ^ (-α) * moment n) ^ 2 := by
      exact Finset.sum_le_sum hterm
    _ = (D : ℝ) ^ (-2 * α) *
        ∑ n ∈ Finset.Icc 1 Y, (moment n) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      rw [mul_pow, hrpow_sq]
    _ ≤ (D : ℝ) ^ (-2 * α) * ((Y : ℝ) *
        ∑ e₁ ∈ (siftModulus z).divisors,
          ∑ e₂ ∈ (siftModulus z).divisors,
            (e₁ : ℝ) ^ α * (e₂ : ℝ) ^ α / (e₁.lcm e₂ : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _
        (Real.rpow_nonneg (Nat.cast_nonneg D) _)
      exact sum_sq_divisor_moment_le (siftModulus_pos z) α
    _ = (D : ℝ) ^ (-2 * α) * (Y : ℝ) *
        ∑ e₁ ∈ (siftModulus z).divisors,
          ∑ e₂ ∈ (siftModulus z).divisors,
            (e₁ : ℝ) ^ α * (e₂ : ℝ) ^ α / (e₁.lcm e₂ : ℝ) := by ring

/-- Explicit `c₁,n` mean-square estimate at `α = 1/log z`. -/
theorem sum_sq_truncTail_invLog_le_logLog
    {Y z D : ℕ} (hz : 2 ≤ z) (hD : 0 < D) :
    ∑ n ∈ Finset.Icc 1 Y, (truncTail n z D : ℝ) ^ 2 ≤
      (D : ℝ) ^ (-2 / Real.log z) * (Y : ℝ) *
        Real.exp ((2 * Real.exp 1 + Real.exp 2) *
          (logLog z + mertensSecondUpperConst)) := by
  have hlogz : 0 < Real.log z := by
    exact Real.log_pos (by exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hz))
  have hgeneric := sum_sq_truncTail_le
    (Y := Y) (z := z) (D := D) (α := 1 / Real.log z) (by positivity) hD
  have hpair := sum_pair_lcm_siftModulus_invLog_le_logLog hz
  calc
    ∑ n ∈ Finset.Icc 1 Y, (truncTail n z D : ℝ) ^ 2 ≤
        (D : ℝ) ^ (-2 * (1 / Real.log z)) * (Y : ℝ) *
          ∑ e₁ ∈ (siftModulus z).divisors,
            ∑ e₂ ∈ (siftModulus z).divisors,
              (e₁ : ℝ) ^ (1 / Real.log z) * (e₂ : ℝ) ^ (1 / Real.log z) /
                (e₁.lcm e₂ : ℝ) := hgeneric
    _ ≤ (D : ℝ) ^ (-2 * (1 / Real.log z)) * (Y : ℝ) *
        Real.exp ((2 * Real.exp 1 + Real.exp 2) *
          (logLog z + mertensSecondUpperConst)) := by
      gcongr
    _ = (D : ℝ) ^ (-2 / Real.log z) * (Y : ℝ) *
        Real.exp ((2 * Real.exp 1 + Real.exp 2) *
          (logLog z + mertensSecondUpperConst)) := by
      congr 3
      ring

end RHTower.Sieve
