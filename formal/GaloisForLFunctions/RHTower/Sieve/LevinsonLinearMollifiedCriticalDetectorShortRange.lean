import GaloisForLFunctions.RHTower.Sieve.LevinsonLinearMollifiedCriticalDetectorEnergy
import GaloisForLFunctions.RHTower.LocalizedHalfDensityCurvature

/-!
# Short-range differentiated critical detector coefficient

Inside the full mollifier range, the first Barban--Vehov divisor-log moment is evaluated by the
second logarithmic derivative of Möbius inversion.  The product-index logarithms cancel, leaving
the exact classical coefficient

`((1 - lambda log M) Lambda(k) - lambda (Lambda * Lambda)(k)) / (log M sqrt k)`.
-/

noncomputable section

open Finset ArithmeticFunction
open scoped ArithmeticFunction ArithmeticFunction.Moebius

namespace RHTower.Sieve

/-- On the full mollifier range, the divisor-log moment is a von Mangoldt first jet minus the
von Mangoldt self-convolution. -/
theorem barbanVehovLogMomentCoeff_eq_vonMangoldt
    {M k : ℕ} (hk : 0 < k) (hkM : k ≤ M) :
    barbanVehovLogMomentCoeff M k =
      Λ k * (Real.log k - Real.log M) - (Λ * Λ) k := by
  have hM : 0 < M := lt_of_lt_of_le hk hkM
  have hterm : ∀ q ∈ k.divisors,
      barbanVehovWeight M q * Real.log q =
        (μ q : ℝ) * (Real.log M - Real.log q) * Real.log q := by
    intro q hq
    have hqk : q ∣ k := Nat.dvd_of_mem_divisors hq
    have hqpos : 0 < q := Nat.pos_of_mem_divisors hq
    have hqM : q ≤ M := le_trans (Nat.le_of_dvd hk hqk) hkM
    rw [barbanVehovWeight, if_pos hqM,
      Real.log_div (by exact_mod_cast (Nat.ne_of_gt hM))
        (by exact_mod_cast (Nat.ne_of_gt hqpos))]
  rw [barbanVehovLogMomentCoeff, Finset.sum_congr rfl hterm]
  have hlog := RHTower.sum_divisors_moebius_mul_log (Nat.ne_of_gt hk)
  have hlogSq := RHTower.sum_divisors_moebius_mul_log_sq (Nat.ne_of_gt hk)
  calc
    ∑ q ∈ k.divisors, (μ q : ℝ) * (Real.log M - Real.log q) * Real.log q =
        Real.log M * (∑ q ∈ k.divisors, (μ q : ℝ) * Real.log q) -
          ∑ q ∈ k.divisors, (μ q : ℝ) * (Real.log q) ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ = Λ k * (Real.log k - Real.log M) - (Λ * Λ) k := by
      rw [hlog, hlogSq]
      ring

@[simp] theorem barbanVehovLogMomentCoeff_one (M : ℕ) :
    barbanVehovLogMomentCoeff M 1 = 0 := by
  simp [barbanVehovLogMomentCoeff]

/-- Inside the full mollifier range, logarithms of the product index cancel and the differentiated
coefficient is exactly `((1-lambda log M) Lambda - lambda Lambda*Lambda)/(log M sqrt k)`. -/
theorem levinsonLinearMollifiedCriticalDetectorCoeff_eq_vonMangoldt
    {lam : ℝ} {M k : ℕ} (hk : 1 < k) (hkM : k ≤ M) :
    levinsonLinearMollifiedCriticalDetectorCoeff lam M k =
      (((((1 - lam * Real.log M) * Λ k - lam * (Λ * Λ) k) /
          Real.log M : ℝ) * ((1 : ℝ) / Real.sqrt k) : ℝ) : ℂ) := by
  rw [levinsonLinearMollifiedCriticalDetectorCoeff_eq (Nat.zero_lt_of_lt hk),
    barbanVehovCoeff_eq_vonMangoldt hk hkM,
    barbanVehovLogMomentCoeff_eq_vonMangoldt (Nat.zero_lt_of_lt hk) hkM]
  congr 1
  ring

/-- Exact square energy of a non-unit coefficient in the full mollifier range. -/
theorem norm_levinsonLinearMollifiedCriticalDetectorCoeff_sq_eq_vonMangoldt
    {lam : ℝ} {M k : ℕ} (hk : 1 < k) (hkM : k ≤ M) :
    ‖levinsonLinearMollifiedCriticalDetectorCoeff lam M k‖ ^ 2 =
      ((1 - lam * Real.log M) * Λ k - lam * (Λ * Λ) k) ^ 2 /
        (k : ℝ) / (Real.log M) ^ 2 := by
  rw [norm_levinsonLinearMollifiedCriticalDetectorCoeff_sq
      (lt_of_lt_of_le hk hkM) (Nat.zero_lt_of_lt hk),
    barbanVehovCoeff_eq_vonMangoldt hk hkM,
    barbanVehovLogMomentCoeff_eq_vonMangoldt (Nat.zero_lt_of_lt hk) hkM]
  congr 2
  ring

/-- Exact non-unit short-range energy in terms of `Lambda` and its self-convolution. -/
theorem sum_norm_levinsonLinearMollifiedCriticalDetectorCoeff_sq_eq_vonMangoldt
    (lam : ℝ) {M N : ℕ} (hNM : N ≤ M) :
    ∑ k ∈ Finset.Icc 2 N,
        ‖levinsonLinearMollifiedCriticalDetectorCoeff lam M k‖ ^ 2 =
      (∑ k ∈ Finset.Icc 2 N,
          ((1 - lam * Real.log M) * Λ k - lam * (Λ * Λ) k) ^ 2 / (k : ℝ)) /
        (Real.log M) ^ 2 := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  rw [norm_levinsonLinearMollifiedCriticalDetectorCoeff_sq_eq_vonMangoldt
    (lt_of_lt_of_le Nat.one_lt_two (Finset.mem_Icc.mp hk).1)
    (le_trans (Finset.mem_Icc.mp hk).2 hNM)]

/-- The unit coefficient of the differentiated critical detector product is exactly one. -/
@[simp] theorem levinsonLinearMollifiedCriticalDetectorCoeff_one
    (lam : ℝ) {M : ℕ} (hM : 1 < M) :
    levinsonLinearMollifiedCriticalDetectorCoeff lam M 1 = 1 := by
  rw [levinsonLinearMollifiedCriticalDetectorCoeff_eq Nat.one_pos,
    barbanVehovCoeff_one (Nat.le_of_lt hM), barbanVehovLogMomentCoeff_one]
  have hlog : Real.log (M : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hM))
  norm_num [hlog]

end RHTower.Sieve
