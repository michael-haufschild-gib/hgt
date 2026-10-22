import GaloisForLFunctions.RHTower.Sieve.FibreThirdSharpPowerBound
import GaloisForLFunctions.RHTower.CarrierLineSup

/-!
# Aggregating the sharp third-derivative fibre bounds over divisors

The sharp third-derivative bound for the Type I fibre at divisor `b` of a dyadic range
`A ≤ B ≤ 2A` is dominated by the factored envelope `C₁ b^(-1/2) + C₂ b^(-1)`, with coefficients
`C₁, C₂` depending on `T, r, A`. Summing over `1 ≤ b ≤ K ≤ A` gives the aggregate bound
`2 C₁ √K + C₂ H_K` with `H_K` the harmonic number, together with the log-weighted variants used
for the Vaughan Type I sums.

## Main results

- `sum_sharpThirdDerivativeFibreBound_le`: `∑_{b ≤ K} F(b) ≤ 2 C₁ √K + C₂ H_K`.
- `sum_log_sharpThirdDerivativeFibreBound_le`: `∑_{b ≤ K} log b · F(b) ≤ log K (2 C₁ √K + C₂ H_K)`.
- `sum_two_sharpThirdDerivativeFibreBound_log_le`: `∑_{b ≤ K} 2 F(b) log(⌊(B-1)/b⌋) ≤
  2 log B (2 C₁ √K + C₂ H_K)`.

## Hypotheses

All results are unconditional explicit inequalities. They assume `T, r > 0`, `1 ≤ A`, `K ≤ A`, the
dyadic range `A ≤ B ≤ 2A`, and `1 ≤ K` for the log-weighted bound.
-/

namespace RHTower.Sieve

open RHTower

noncomputable section

/-- The first envelope coefficient `C₁` is nonnegative for `T, r > 0`, `A ≥ 1`. -/
theorem sharpThirdDerivativeFibreFirstCoefficient_nonneg {T r : ℝ}
    (hT : 0 < T) (hr : 0 < r) {A : ℕ} (hA : 1 ≤ A) :
    0 ≤ sharpThirdDerivativeFibreFirstCoefficient T r A := by
  rw [sharpThirdDerivativeFibreFirstCoefficient]
  positivity

/-- The second envelope coefficient `C₂` is nonnegative for `T, r > 0`, `A ≥ 1`. -/
theorem sharpThirdDerivativeFibreSecondCoefficient_nonneg {T r : ℝ}
    (hT : 0 < T) (hr : 0 < r) {A : ℕ} (hA : 1 ≤ A) :
    0 ≤ sharpThirdDerivativeFibreSecondCoefficient T r A := by
  rw [sharpThirdDerivativeFibreSecondCoefficient]
  positivity

/-- Assuming `T, r > 0`, `1 ≤ A`, `K ≤ A` and `A ≤ B ≤ 2A`, the sharp third-derivative fibre bounds
over divisors `1 ≤ b ≤ K` sum to at most `2 C₁ √K + C₂ H_K`. -/
theorem sum_sharpThirdDerivativeFibreBound_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {A B K : ℕ} (hA : 1 ≤ A) (hKA : K ≤ A)
    (hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    (∑ b ∈ Finset.Icc 1 K, sharpThirdDerivativeFibreBound T r A B b)
      ≤ 2 * sharpThirdDerivativeFibreFirstCoefficient T r A * Real.sqrt K
        + sharpThirdDerivativeFibreSecondCoefficient T r A * invSum K := by
  have hC1 := sharpThirdDerivativeFibreFirstCoefficient_nonneg hT hr hA
  have hC2 := sharpThirdDerivativeFibreSecondCoefficient_nonneg hT hr hA
  have hpoint : ∀ b ∈ Finset.Icc 1 K,
      sharpThirdDerivativeFibreBound T r A B b ≤
        sharpThirdDerivativeFibreFactoredEnvelope T r A b := by
    intro b hb
    rw [Finset.mem_Icc] at hb
    exact (sharpThirdDerivativeFibreBound_le_powerEnvelope hT hr hA hb.1
      (le_trans hb.2 hKA) hAB hBA).trans_eq
        (sharpThirdDerivativeFibrePowerEnvelope_eq_factored hT hr hA hb.1)
  refine (Finset.sum_le_sum hpoint).trans ?_
  have hhalf := RHTower.sum_rpow_neg_half_le K
  have hfactor : (∑ b ∈ Finset.Icc 1 K, sharpThirdDerivativeFibreFactoredEnvelope T r A b) =
      sharpThirdDerivativeFibreFirstCoefficient T r A *
          (∑ b ∈ Finset.Icc 1 K, (b : ℝ) ^ (-(1 / 2 : ℝ)))
        + sharpThirdDerivativeFibreSecondCoefficient T r A * invSum K := by
    calc
      (∑ b ∈ Finset.Icc 1 K, sharpThirdDerivativeFibreFactoredEnvelope T r A b) =
          ∑ b ∈ Finset.Icc 1 K,
            (sharpThirdDerivativeFibreFirstCoefficient T r A * (b : ℝ) ^ (-(1 / 2 : ℝ))
              + sharpThirdDerivativeFibreSecondCoefficient T r A * (b : ℝ)⁻¹) :=
        Finset.sum_congr rfl fun b hb => by rw [sharpThirdDerivativeFibreFactoredEnvelope]
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        simp only [invSum, one_div]
  rw [hfactor]
  have hfirst := mul_le_mul_of_nonneg_left hhalf hC1
  nlinarith

/-- Under the same assumptions and `1 ≤ K`, the `log b`-weighted fibre bounds sum to at most
`log K (2 C₁ √K + C₂ H_K)`. -/
theorem sum_log_sharpThirdDerivativeFibreBound_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {A B K : ℕ} (hA : 1 ≤ A) (hK : 1 ≤ K) (hKA : K ≤ A)
    (hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    (∑ b ∈ Finset.Icc 1 K, Real.log b * sharpThirdDerivativeFibreBound T r A B b)
      ≤ Real.log K *
        (2 * sharpThirdDerivativeFibreFirstCoefficient T r A * Real.sqrt K
          + sharpThirdDerivativeFibreSecondCoefficient T r A * invSum K) := by
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hpoint : ∀ b ∈ Finset.Icc 1 K,
      Real.log b * sharpThirdDerivativeFibreBound T r A B b ≤
        Real.log K * sharpThirdDerivativeFibreBound T r A B b := by
    intro b hb
    rw [Finset.mem_Icc] at hb
    have hlog : Real.log b ≤ Real.log K :=
      Real.log_le_log (by exact_mod_cast hb.1) (by exact_mod_cast hb.2)
    exact mul_le_mul_of_nonneg_right hlog
      (sharpThirdDerivativeFibreBound_nonneg hT hr hb.1)
  refine (Finset.sum_le_sum hpoint).trans ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left
    (sum_sharpThirdDerivativeFibreBound_le hT hr hA hKA hAB hBA)
    (Real.log_nonneg hK1)

/-- Under the same assumptions, `∑_{b ≤ K} 2 F(b) log(⌊(B-1)/b⌋) ≤ 2 log B (2 C₁ √K + C₂ H_K)`. -/
theorem sum_two_sharpThirdDerivativeFibreBound_log_le {T r : ℝ}
    (hT : 0 < T) (hr : 0 < r) {A B K : ℕ} (hA : 1 ≤ A) (hKA : K ≤ A)
    (hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    (∑ b ∈ Finset.Icc 1 K,
        2 * sharpThirdDerivativeFibreBound T r A B b *
          Real.log ((((B - 1) / b + 1 - 1 : ℕ)) : ℝ))
      ≤ 2 * Real.log B *
        (2 * sharpThirdDerivativeFibreFirstCoefficient T r A * Real.sqrt K
          + sharpThirdDerivativeFibreSecondCoefficient T r A * invSum K) := by
  have hB1 : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast le_trans hA hAB
  have hpoint : ∀ b ∈ Finset.Icc 1 K,
      2 * sharpThirdDerivativeFibreBound T r A B b *
          Real.log ((((B - 1) / b + 1 - 1 : ℕ)) : ℝ)
        ≤ 2 * Real.log B * sharpThirdDerivativeFibreBound T r A B b := by
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
    have hfb : 0 ≤ sharpThirdDerivativeFibreBound T r A B b :=
      sharpThirdDerivativeFibreBound_nonneg hT hr hb.1
    nlinarith
  refine (Finset.sum_le_sum hpoint).trans ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left
    (sum_sharpThirdDerivativeFibreBound_le hT hr hA hKA hAB hBA)
    (mul_nonneg (by norm_num) (Real.log_nonneg hB1))

end

end RHTower.Sieve
