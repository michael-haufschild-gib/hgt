import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalPrimeHarmonicDiagonal

/-!
# Cumulative charge of the critical factorial prime kernel

The cubic cumulative divisor charge vanishes at cutoffs zero and one, is negative
at cutoffs two through four, and is positive from cutoff five onward. A direct
von Mangoldt divisor bound gives absolute cubic summability, uniform boundedness,
and a strictly positive limit. These facts concern the cumulative charge; they do
not determine the sign of the complete prime quadratic form.
-/

open Finset Filter
open scoped BigOperators Topology

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

/-- The cubic cumulative charge in the common-density critical prime kernel. -/
def factorialCriticalPrimeCumulativeCharge (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, factorialCriticalPrimeHarmonicCharge m / (m : ℝ)^3

/-- Every odd prime contributes its literal prime logarithmic charge. -/
theorem factorialCriticalPrimeHarmonicCharge_odd_prime {p : ℕ}
    (hp : p.Prime) (hodd : p % 2 = 1) :
    factorialCriticalPrimeHarmonicCharge p = (p : ℝ) * Real.log p := by
  have h1p : 1 ≠ p := Ne.symm hp.ne_one
  have hpp : p / p = 1 := Nat.div_self hp.pos
  simp [factorialCriticalPrimeHarmonicCharge, hp.divisors, h1p, hpp,
    dyadicHarmonicChi, hodd, ArithmeticFunction.vonMangoldt_apply_prime hp]

private theorem cumulative_small_values :
    factorialCriticalPrimeCumulativeCharge 0 = 0 ∧
    factorialCriticalPrimeCumulativeCharge 1 = 0 ∧
    factorialCriticalPrimeCumulativeCharge 2 = -Real.log 2 / 4 ∧
    factorialCriticalPrimeCumulativeCharge 3 = -Real.log 2 / 4 + Real.log 3 / 9 ∧
    factorialCriticalPrimeCumulativeCharge 4 = -Real.log 2 / 4 + Real.log 3 / 9 ∧
    factorialCriticalPrimeCumulativeCharge 5 =
      -Real.log 2 / 4 + Real.log 3 / 9 + Real.log 5 / 25 := by
  have hA1 : factorialCriticalPrimeHarmonicCharge 1 = 0 :=
    (factorialCriticalPrimeHarmonicCharge_sign 1).2.1.mpr (Or.inl rfl)
  have hA2 := factorialCriticalPrimeHarmonicCharge_two
  have hA3 : factorialCriticalPrimeHarmonicCharge 3 = 3 * Real.log 3 :=
    factorialCriticalPrimeHarmonicCharge_odd_prime (by norm_num) (by norm_num)
  have hA4 : factorialCriticalPrimeHarmonicCharge 4 = 0 :=
    (factorialCriticalPrimeHarmonicCharge_sign 4).2.1.mpr (Or.inr rfl)
  have hA5 : factorialCriticalPrimeHarmonicCharge 5 = 5 * Real.log 5 :=
    factorialCriticalPrimeHarmonicCharge_odd_prime (by norm_num) (by norm_num)
  have hI2 : Finset.Icc (1 : ℕ) 2 = {1,2} := by decide
  have hI3 : Finset.Icc (1 : ℕ) 3 = {1,2,3} := by decide
  have hI4 : Finset.Icc (1 : ℕ) 4 = {1,2,3,4} := by decide
  have hI5 : Finset.Icc (1 : ℕ) 5 = {1,2,3,4,5} := by decide
  constructor
  · simp [factorialCriticalPrimeCumulativeCharge]
  constructor
  · simp [factorialCriticalPrimeCumulativeCharge, hA1]
  constructor
  · norm_num [factorialCriticalPrimeCumulativeCharge, hI2, hA1, hA2]; ring
  constructor
  · norm_num [factorialCriticalPrimeCumulativeCharge, hI3, hA1, hA2, hA3]; ring
  constructor
  · norm_num [factorialCriticalPrimeCumulativeCharge, hI4, hA1, hA2, hA3, hA4]; ring
  · norm_num [factorialCriticalPrimeCumulativeCharge, hI5, hA1, hA2, hA3, hA4, hA5]; ring

/-- Every increment after the unique negative second charge is nonnegative. -/
theorem factorialCriticalPrimeCumulativeCharge_mono {M N : ℕ}
    (hM : 2 ≤ M) (hMN : M ≤ N) :
    factorialCriticalPrimeCumulativeCharge M ≤ factorialCriticalPrimeCumulativeCharge N := by
  unfold factorialCriticalPrimeCumulativeCharge
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro m hm
    rcases Finset.mem_Icc.mp hm with ⟨hm1, hmM⟩
    exact Finset.mem_Icc.mpr ⟨hm1, hmM.trans hMN⟩
  · intro m hm hmnot
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hmgt : M < m := by
      by_contra h
      exact hmnot (Finset.mem_Icc.mpr ⟨hm1, by omega⟩)
    have hmne : m ≠ 2 := by omega
    have hA : 0 ≤ factorialCriticalPrimeHarmonicCharge m :=
      le_of_not_gt (fun h => hmne ((factorialCriticalPrimeHarmonicCharge_sign m).1.mp h))
    exact div_nonneg hA (by positivity)

private theorem cumulative_log_inequalities :
    Real.log 3 < 2 * Real.log 2 ∧
    3 * Real.log 2 < 2 * Real.log 3 ∧
    9 * Real.log 2 < 4 * Real.log 5 := by
  have h₁ := Real.log_lt_log (by norm_num : (0 : ℝ) < 3)
    (by norm_num : (3 : ℝ) < 2^2)
  have h₂ := Real.log_lt_log (by norm_num : (0 : ℝ) < 2^3)
    (by norm_num : (2 : ℝ)^3 < 3^2)
  have h₃ := Real.log_lt_log (by norm_num : (0 : ℝ) < 2^9)
    (by norm_num : (2 : ℝ)^9 < 5^4)
  simp only [Real.log_pow, Nat.cast_ofNat] at h₁ h₂ h₃
  exact ⟨h₁, h₂, h₃⟩

/-- The positive cumulative tail has a fixed strict margin from the fifth harmonic onward. -/
theorem factorialCriticalPrimeCumulativeCharge_lower {N : ℕ} (hN : 5 ≤ N) :
    Real.log 2 / 150 < factorialCriticalPrimeCumulativeCharge N := by
  have hfive : Real.log 2 / 150 < factorialCriticalPrimeCumulativeCharge 5 := by
    rcases cumulative_small_values with ⟨h0, h1, h2, h3, h4, h5⟩
    rcases cumulative_log_inequalities with ⟨hlog3, h23, h25⟩
    rw [h5]
    linarith
  exact hfive.trans_le (factorialCriticalPrimeCumulativeCharge_mono (by norm_num) hN)

/-- The cumulative native charge changes sign exactly between cutoffs four and five. -/
theorem factorialCriticalPrimeCumulativeCharge_sign (N : ℕ) :
    (factorialCriticalPrimeCumulativeCharge N < 0 ↔ 2 ≤ N ∧ N ≤ 4) ∧
    (factorialCriticalPrimeCumulativeCharge N = 0 ↔ N ≤ 1) ∧
    (0 < factorialCriticalPrimeCumulativeCharge N ↔ 5 ≤ N) := by
  rcases cumulative_small_values with ⟨h0, h1, h2, h3, h4, h5⟩
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 := cumulative_log_inequalities.1
  have hzero (hN : N ≤ 1) : factorialCriticalPrimeCumulativeCharge N = 0 := by
    interval_cases N
    · exact h0
    · exact h1
  have hneg (hN2 : 2 ≤ N) (hN4 : N ≤ 4) : factorialCriticalPrimeCumulativeCharge N < 0 := by
    interval_cases N
    · rw [h2]
      linarith
    · rw [h3]
      linarith
    · rw [h4]
      linarith
  have hpos (hN : 5 ≤ N) : 0 < factorialCriticalPrimeCumulativeCharge N :=
    lt_trans (div_pos hlog2 (by norm_num)) (factorialCriticalPrimeCumulativeCharge_lower hN)
  by_cases hsmall : N ≤ 1
  · rw [hzero hsmall]
    norm_num
    omega
  by_cases hmid : N ≤ 4
  · have hn := hneg (by omega) hmid
    have hn0 : factorialCriticalPrimeCumulativeCharge N ≠ 0 := ne_of_lt hn
    have hnp : ¬ 0 < factorialCriticalPrimeCumulativeCharge N := not_lt_of_ge hn.le
    simp only [hn, hn0, hnp, true_iff, false_iff]
    omega
  · have hp := hpos (by omega)
    have hp0 : factorialCriticalPrimeCumulativeCharge N ≠ 0 := ne_of_gt hp
    have hpn : ¬ factorialCriticalPrimeCumulativeCharge N < 0 := not_lt_of_ge hp.le
    simp only [hp, hp0, hpn, true_iff, false_iff]
    omega

/-- The absolute native divisor charge is bounded by the full logarithmic divisor mass. -/
theorem abs_factorialCriticalPrimeHarmonicCharge_le (m : ℕ) :
    |factorialCriticalPrimeHarmonicCharge m| ≤ (m : ℝ) * Real.log m := by
  unfold factorialCriticalPrimeHarmonicCharge
  rw [abs_mul]
  calc
    |dyadicHarmonicChi m| * |∑ r ∈ m.divisors,
        (r : ℝ) * (ArithmeticFunction.vonMangoldt r : ℝ) * dyadicHarmonicChi (m/r)|
        ≤ 1 * |∑ r ∈ m.divisors,
          (r : ℝ) * (ArithmeticFunction.vonMangoldt r : ℝ) * dyadicHarmonicChi (m/r)| :=
      mul_le_mul_of_nonneg_right (abs_dyadicHarmonicChi_le_one m) (abs_nonneg _)
    _ = |∑ r ∈ m.divisors,
        (r : ℝ) * (ArithmeticFunction.vonMangoldt r : ℝ) * dyadicHarmonicChi (m/r)| :=
      one_mul _
    _ ≤ ∑ r ∈ m.divisors,
        |(r : ℝ) * (ArithmeticFunction.vonMangoldt r : ℝ) * dyadicHarmonicChi (m/r)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ m.divisors, (m : ℝ) * (ArithmeticFunction.vonMangoldt r : ℝ) := by
      apply Finset.sum_le_sum
      intro r hr
      have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt r : ℝ) :=
        ArithmeticFunction.vonMangoldt_nonneg
      have hrm : (r : ℝ) ≤ m := by exact_mod_cast Nat.divisor_le hr
      rw [abs_mul, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg r) hΛ)]
      calc (r : ℝ) * (ArithmeticFunction.vonMangoldt r : ℝ) * |dyadicHarmonicChi (m/r)|
          ≤ (r : ℝ) * (ArithmeticFunction.vonMangoldt r : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left (abs_dyadicHarmonicChi_le_one _) (by positivity)
        _ ≤ (m : ℝ) * (ArithmeticFunction.vonMangoldt r : ℝ) := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_right hrm hΛ
    _ = (m : ℝ) * Real.log m := by
      rw [← Finset.mul_sum, ArithmeticFunction.vonMangoldt_sum]

/-- Cubic absolute summability controls the cumulative charge independently of cutoff. -/
theorem summable_abs_factorialCriticalPrimeHarmonicCharge_div_cube :
    Summable (fun m : ℕ => |factorialCriticalPrimeHarmonicCharge m| / (m : ℝ)^3) := by
  refine Summable.of_nonneg_of_le (fun m => div_nonneg (abs_nonneg _) (by positivity))
    (fun m => ?_) (summable_envelopeLogMajorant_of_half_lt (by norm_num : (1 : ℝ)/2 < 3/2))
  by_cases hm : 2 ≤ m
  · have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    calc
      |factorialCriticalPrimeHarmonicCharge m| / (m : ℝ)^3
          ≤ ((m : ℝ) * Real.log m) / (m : ℝ)^3 :=
        div_le_div_of_nonneg_right (abs_factorialCriticalPrimeHarmonicCharge_le m) (by positivity)
      _ = Real.log m / (m : ℝ)^2 := by field_simp [hm0]
      _ = envelopeLogMajorant (3/2) m := by
        simp only [envelopeLogMajorant, if_pos hm, show (3/2 : ℝ) + 1/2 = 2 by norm_num,
          Real.rpow_two]
  · have hm01 : m = 0 ∨ m = 1 := by omega
    rcases hm01 with rfl | rfl
    · simp [envelopeLogMajorant]
    · have hA1 : factorialCriticalPrimeHarmonicCharge 1 = 0 :=
        (factorialCriticalPrimeHarmonicCharge_sign 1).2.1.mpr (Or.inl rfl)
      simp [envelopeLogMajorant, hA1]

/-- The signed cubic charge is absolutely convergent. -/
theorem summable_factorialCriticalPrimeHarmonicCharge_div_cube :
    Summable (fun m : ℕ => factorialCriticalPrimeHarmonicCharge m / (m : ℝ)^3) := by
  apply summable_abs_factorialCriticalPrimeHarmonicCharge_div_cube.of_norm_bounded
  intro m
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (show 0 ≤ (m : ℝ)^3 by positivity)]

/-- One finite constant bounds every cumulative charge. -/
theorem abs_factorialCriticalPrimeCumulativeCharge_le (N : ℕ) :
    |factorialCriticalPrimeCumulativeCharge N| ≤
      ∑' m : ℕ, |factorialCriticalPrimeHarmonicCharge m| / (m : ℝ)^3 := by
  have habs (m : ℕ) : |factorialCriticalPrimeHarmonicCharge m / (m : ℝ)^3| =
      |factorialCriticalPrimeHarmonicCharge m| / (m : ℝ)^3 := by
    rw [abs_div, abs_of_nonneg (show 0 ≤ (m : ℝ)^3 by positivity)]
  have h := Finset.abs_sum_le_sum_abs
    (fun m : ℕ => factorialCriticalPrimeHarmonicCharge m / (m : ℝ)^3) (Finset.Icc 1 N)
  simp_rw [habs] at h
  exact h.trans (summable_abs_factorialCriticalPrimeHarmonicCharge_div_cube.sum_le_tsum
    (Finset.Icc 1 N) (fun m _ => div_nonneg (abs_nonneg _) (by positivity)))

/-- The cumulative kernel charge converges to its absolutely convergent cubic series. -/
theorem factorialCriticalPrimeCumulativeCharge_tendsto :
    Tendsto factorialCriticalPrimeCumulativeCharge atTop
      (𝓝 (∑' m : ℕ, factorialCriticalPrimeHarmonicCharge m / (m : ℝ)^3)) := by
  have h := summable_factorialCriticalPrimeHarmonicCharge_div_cube.hasSum.tendsto_sum_nat.comp
    (tendsto_add_atTop_nat 1)
  unfold factorialCriticalPrimeCumulativeCharge
  refine h.congr fun N => ?_
  have he : (Finset.range (N + 1)).erase 0 = Finset.Icc 1 N := by
    ext m
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Icc]
    omega
  have hz : factorialCriticalPrimeHarmonicCharge 0 / ((0 : ℕ) : ℝ)^3 = 0 := by simp
  simpa only [Function.comp_apply, he] using
    (Finset.sum_erase (f := fun m : ℕ => factorialCriticalPrimeHarmonicCharge m / (m : ℝ)^3)
      (a := 0) (Finset.range (N + 1)) hz).symm

/-- The limiting cubic charge retains a strict positive margin. -/
theorem factorialCriticalPrimeCubicCharge_lower :
    Real.log 2 / 150 <
      ∑' m : ℕ, factorialCriticalPrimeHarmonicCharge m / (m : ℝ)^3 := by
  have h5 : factorialCriticalPrimeCumulativeCharge 5 ≤
      ∑' m : ℕ, factorialCriticalPrimeHarmonicCharge m / (m : ℝ)^3 :=
    ge_of_tendsto factorialCriticalPrimeCumulativeCharge_tendsto
      (eventually_atTop.2 ⟨5, fun N hN =>
        factorialCriticalPrimeCumulativeCharge_mono (by norm_num) hN⟩)
  exact (factorialCriticalPrimeCumulativeCharge_lower (by norm_num : 5 ≤ 5)).trans_le h5

end GaloisForLFunctions.ArithmeticPositivityTheory
