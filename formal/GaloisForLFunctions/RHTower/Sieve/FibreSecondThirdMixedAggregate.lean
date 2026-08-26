import GaloisForLFunctions.RHTower.Sieve.FibreSecondThirdMixed

/-!
# Aggregate mixed-derivative Type-I bound

The crossover estimate sums with divisor weights `b⁻¹ᐟ²` and `b⁻¹`.  These give a square-root
support cost and harmonic tail, respectively, including both logarithmic Vaughan weights.
-/

namespace RHTower.Sieve

open RHTower

noncomputable section

def secondThirdMixedAggregateEnvelope (T r : ℝ) (A B K : ℕ) : ℝ :=
  4 * secondThirdMixedFibreMainCoefficient T r A * Real.sqrt K
    + fibreTail T r B * invSum K

theorem sum_secondThirdMixedFibreBound_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {A B K : ℕ} (hA : 1 ≤ A) (hKA : K ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    (∑ b ∈ Finset.Icc 1 K, secondThirdMixedFibreBound T r A B b) ≤
      secondThirdMixedAggregateEnvelope T r A B K := by
  have hC1 : 0 ≤ secondThirdMixedFibreMainCoefficient T r A := by
    rw [secondThirdMixedFibreMainCoefficient]
    exact add_nonneg (sharpThirdDerivativeFibreFirstCoefficient_nonneg hT hr hA)
      (Real.sqrt_nonneg _)
  have hpoint : ∀ b ∈ Finset.Icc 1 K,
      secondThirdMixedFibreBound T r A B b ≤
        2 * secondThirdMixedFibreMainCoefficient T r A * (b : ℝ) ^ (-(1 / 2 : ℝ))
          + fibreTail T r B / b := by
    intro b hb
    rw [Finset.mem_Icc] at hb
    exact secondThirdMixedFibreBound_le_powerEnvelope hT hr hA hb.1
      (le_trans hb.2 hKA) hAB hBA
  refine (Finset.sum_le_sum hpoint).trans ?_
  have hhalf := RHTower.sum_rpow_neg_half_le K
  have hfactor :
      (∑ b ∈ Finset.Icc 1 K,
        (2 * secondThirdMixedFibreMainCoefficient T r A * (b : ℝ) ^ (-(1 / 2 : ℝ))
          + fibreTail T r B / b)) =
        2 * secondThirdMixedFibreMainCoefficient T r A *
            (∑ b ∈ Finset.Icc 1 K, (b : ℝ) ^ (-(1 / 2 : ℝ)))
          + fibreTail T r B * invSum K := by
    have htail : (∑ b ∈ Finset.Icc 1 K, fibreTail T r B / (b : ℝ)) =
        fibreTail T r B * invSum K := by
      rw [invSum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by rw [mul_one_div]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, htail]
  rw [hfactor, secondThirdMixedAggregateEnvelope]
  have hfirst := mul_le_mul_of_nonneg_left hhalf
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC1)
  calc
    2 * secondThirdMixedFibreMainCoefficient T r A *
          (∑ b ∈ Finset.Icc 1 K, (b : ℝ) ^ (-(1 / 2 : ℝ))) + fibreTail T r B * invSum K
        ≤ 2 * secondThirdMixedFibreMainCoefficient T r A * (2 * Real.sqrt K) +
            fibreTail T r B * invSum K := add_le_add hfirst le_rfl
    _ = 4 * secondThirdMixedFibreMainCoefficient T r A * Real.sqrt K +
          fibreTail T r B * invSum K := by ring

theorem sum_log_secondThirdMixedFibreBound_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {A B K : ℕ} (hA : 1 ≤ A) (hK : 1 ≤ K) (hKA : K ≤ A)
    (hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    (∑ b ∈ Finset.Icc 1 K, Real.log b * secondThirdMixedFibreBound T r A B b) ≤
      Real.log K * secondThirdMixedAggregateEnvelope T r A B K := by
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hpoint : ∀ b ∈ Finset.Icc 1 K,
      Real.log b * secondThirdMixedFibreBound T r A B b ≤
        Real.log K * secondThirdMixedFibreBound T r A B b := by
    intro b hb
    rw [Finset.mem_Icc] at hb
    have hlog : Real.log b ≤ Real.log K :=
      Real.log_le_log (by exact_mod_cast hb.1) (by exact_mod_cast hb.2)
    exact mul_le_mul_of_nonneg_right hlog
      (secondThirdMixedFibreBound_nonneg hT hr hb.1)
  refine (Finset.sum_le_sum hpoint).trans ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left
    (sum_secondThirdMixedFibreBound_le hT hr hA hKA hAB hBA)
    (Real.log_nonneg hK1)

theorem sum_two_secondThirdMixedFibreBound_log_le {T r : ℝ}
    (hT : 0 < T) (hr : 0 < r) {A B K : ℕ} (hA : 1 ≤ A) (hKA : K ≤ A)
    (hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    (∑ b ∈ Finset.Icc 1 K,
        2 * secondThirdMixedFibreBound T r A B b *
          Real.log ((((B - 1) / b + 1 - 1 : ℕ)) : ℝ)) ≤
      2 * Real.log B * secondThirdMixedAggregateEnvelope T r A B K := by
  have hB1 : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast le_trans hA hAB
  have hpoint : ∀ b ∈ Finset.Icc 1 K,
      2 * secondThirdMixedFibreBound T r A B b *
          Real.log ((((B - 1) / b + 1 - 1 : ℕ)) : ℝ) ≤
        2 * Real.log B * secondThirdMixedFibreBound T r A B b := by
    intro b hb
    rw [Finset.mem_Icc] at hb
    have hlogle : Real.log ((((B - 1) / b + 1 - 1 : ℕ)) : ℝ) ≤ Real.log B := by
      rcases Nat.eq_zero_or_pos ((B - 1) / b + 1 - 1) with h | h
      · rw [h]
        simpa using Real.log_nonneg hB1
      · refine Real.log_le_log (by exact_mod_cast h) ?_
        exact_mod_cast (show (B - 1) / b + 1 - 1 ≤ B by
          have := Nat.div_le_self (B - 1) b
          omega)
    have hfb := secondThirdMixedFibreBound_nonneg (A := A) (B := B) hT hr hb.1
    nlinarith
  refine (Finset.sum_le_sum hpoint).trans ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left
    (sum_secondThirdMixedFibreBound_le hT hr hA hKA hAB hBA)
    (mul_nonneg (by norm_num) (Real.log_nonneg hB1))

end

end RHTower.Sieve
