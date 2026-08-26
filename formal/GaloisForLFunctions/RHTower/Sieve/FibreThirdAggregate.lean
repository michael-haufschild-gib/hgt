import GaloisForLFunctions.RHTower.Sieve.FibreThirdPowerBound
import GaloisForLFunctions.RHTower.CarrierLineSup
import GaloisForLFunctions.RHTower.CreaseBudgetPrimeMass

/-!
# Aggregating third-derivative type-I fibres

The factored fibre envelope has divisor weights `b⁻¹ᐟ²` and `b⁻⁵ᐟ⁴`.  Their partial sums are at
most `2√K` and `5`, respectively, giving the exact square-root support cost used by the Vaughan
parameter choice.
-/

namespace RHTower.Sieve

open RHTower

noncomputable section

theorem thirdDerivativeFibreFirstCoefficient_nonneg {T r : ℝ}
    (hT : 0 < T) (hr : 0 < r) {A : ℕ} (hA : 1 ≤ A) :
    0 ≤ thirdDerivativeFibreFirstCoefficient T r A := by
  rw [thirdDerivativeFibreFirstCoefficient]
  positivity

theorem thirdDerivativeFibreSecondCoefficient_nonneg {T r : ℝ}
    (hT : 0 < T) (hr : 0 < r) {A : ℕ} (hA : 1 ≤ A) :
    0 ≤ thirdDerivativeFibreSecondCoefficient T r A := by
  rw [thirdDerivativeFibreSecondCoefficient]
  positivity

/-- Sum of the raw third-derivative fibre envelopes over a supported divisor range. -/
theorem sum_thirdDerivativeFibreBound_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {A B K : ℕ} (hA : 1 ≤ A) (hKA : K ≤ A)
    (hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    (∑ b ∈ Finset.Icc 1 K, thirdDerivativeFibreBound T r A B b)
      ≤ 2 * thirdDerivativeFibreFirstCoefficient T r A * Real.sqrt K
        + 5 * thirdDerivativeFibreSecondCoefficient T r A := by
  have hC1 := thirdDerivativeFibreFirstCoefficient_nonneg hT hr hA
  have hC2 := thirdDerivativeFibreSecondCoefficient_nonneg hT hr hA
  have hpoint : ∀ b ∈ Finset.Icc 1 K,
      thirdDerivativeFibreBound T r A B b ≤
        thirdDerivativeFibreFactoredEnvelope T r A b := by
    intro b hb
    rw [Finset.mem_Icc] at hb
    exact (thirdDerivativeFibreBound_le_powerEnvelope hT hr hA hb.1 (le_trans hb.2 hKA)
      hAB hBA).trans_eq (thirdDerivativeFibrePowerEnvelope_eq_factored hT hr hA hb.1)
  refine (Finset.sum_le_sum hpoint).trans ?_
  have hhalf := RHTower.sum_rpow_neg_half_le K
  have hfive := RHTower.sum_Icc_rpow_neg_le (c := (5 / 4 : ℝ)) (by norm_num) K
  norm_num at hfive
  have hfactor : (∑ b ∈ Finset.Icc 1 K, thirdDerivativeFibreFactoredEnvelope T r A b) =
      thirdDerivativeFibreFirstCoefficient T r A *
          (∑ b ∈ Finset.Icc 1 K, (b : ℝ) ^ (-(1 / 2 : ℝ)))
        + thirdDerivativeFibreSecondCoefficient T r A *
          (∑ b ∈ Finset.Icc 1 K, (b : ℝ) ^ (-(5 / 4 : ℝ))) := by
    calc
      (∑ b ∈ Finset.Icc 1 K, thirdDerivativeFibreFactoredEnvelope T r A b) =
          ∑ b ∈ Finset.Icc 1 K,
            (thirdDerivativeFibreFirstCoefficient T r A * (b : ℝ) ^ (-(1 / 2 : ℝ))
              + thirdDerivativeFibreSecondCoefficient T r A * (b : ℝ) ^ (-(5 / 4 : ℝ))) :=
        Finset.sum_congr rfl fun b hb => by rw [thirdDerivativeFibreFactoredEnvelope]
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hfactor]
  have hfirst := mul_le_mul_of_nonneg_left hhalf hC1
  have hsecond := mul_le_mul_of_nonneg_left hfive hC2
  nlinarith

/-- First Vaughan type-I aggregate, including its coefficient logarithm. -/
theorem sum_log_thirdDerivativeFibreBound_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {A B K : ℕ} (hA : 1 ≤ A) (hK : 1 ≤ K) (hKA : K ≤ A)
    (hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    (∑ b ∈ Finset.Icc 1 K, Real.log b * thirdDerivativeFibreBound T r A B b)
      ≤ Real.log K *
        (2 * thirdDerivativeFibreFirstCoefficient T r A * Real.sqrt K
          + 5 * thirdDerivativeFibreSecondCoefficient T r A) := by
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hpoint : ∀ b ∈ Finset.Icc 1 K,
      Real.log b * thirdDerivativeFibreBound T r A B b ≤
        Real.log K * thirdDerivativeFibreBound T r A B b := by
    intro b hb
    rw [Finset.mem_Icc] at hb
    have hlog : Real.log b ≤ Real.log K :=
      Real.log_le_log (by exact_mod_cast hb.1) (by exact_mod_cast hb.2)
    exact mul_le_mul_of_nonneg_right hlog
      (thirdDerivativeFibreBound_nonneg hT hr hb.1)
  refine (Finset.sum_le_sum hpoint).trans ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left
    (sum_thirdDerivativeFibreBound_le hT hr hA hKA hAB hBA)
    (Real.log_nonneg hK1)

/-- Second Vaughan type-I aggregate, including the inner logarithmic weight. -/
theorem sum_two_thirdDerivativeFibreBound_log_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {A B K : ℕ} (hA : 1 ≤ A) (hKA : K ≤ A)
    (hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    (∑ b ∈ Finset.Icc 1 K,
        2 * thirdDerivativeFibreBound T r A B b *
          Real.log ((((B - 1) / b + 1 - 1 : ℕ)) : ℝ))
      ≤ 2 * Real.log B *
        (2 * thirdDerivativeFibreFirstCoefficient T r A * Real.sqrt K
          + 5 * thirdDerivativeFibreSecondCoefficient T r A) := by
  have hB1 : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast le_trans hA hAB
  have hpoint : ∀ b ∈ Finset.Icc 1 K,
      2 * thirdDerivativeFibreBound T r A B b *
          Real.log ((((B - 1) / b + 1 - 1 : ℕ)) : ℝ)
        ≤ 2 * Real.log B * thirdDerivativeFibreBound T r A B b := by
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
    have hfb : 0 ≤ thirdDerivativeFibreBound T r A B b :=
      thirdDerivativeFibreBound_nonneg hT hr hb.1
    nlinarith
  refine (Finset.sum_le_sum hpoint).trans ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left
    (sum_thirdDerivativeFibreBound_le hT hr hA hKA hAB hBA)
    (mul_nonneg (by norm_num) (Real.log_nonneg hB1))

end

end RHTower.Sieve
