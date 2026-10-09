import GaloisForLFunctions.RHTower.WeilLogShiftQuadraticColumnGrowth

/-!
# Exponential damping cannot control late impulse responses

The quadratic coefficient envelope survives the square-root normalization
and the paired-log kernel's exponential decay. Every fixed real exponential
damping rate still leaves response magnitudes tending to infinity, at every
real shift. Consequently no such damped signed response series is summable.
-/

open Filter Topology Real

namespace RHTower

open WeilExcess

/-- A positive quadratic-exponential lower envelope for every sufficiently
late fixed response column, retaining its normalization through `n+1`. -/
theorem exists_weilLogShiftRecoveryMomentResponse_quadratic_exponential_lower :
    ∃ K : ℕ, 625 ≤ K ∧ ∀ k : ℕ, K ≤ k → ∀ y : ℝ, ∃ C : ℝ, 0 < C ∧
      ∀ᶠ n : ℕ in atTop,
        (C / ((n : ℝ) + 1)) *
          exp ((n : ℝ) * ((n : ℝ) + 1) / 2 - (2 * π + 1) * n) ≤
            |weilLogShiftRecoveryMomentResponse y n k| := by
  obtain ⟨K, hK, hcoeff⟩ := exists_weilLogShiftRecoveryCoefficientColumn_quadratic_exponential_lower
  refine ⟨K, hK, fun k hk y => ?_⟩
  obtain ⟨c, hc, hcol⟩ := hcoeff k hk
  have hrate : logKernelCriticalRate y < 2 * π + 1 := by
    have he : exp (-|y|) ≤ 1 := exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg y))
    have h := mul_le_mul_of_nonneg_left he (show 0 ≤ 2 * π by positivity)
    dsimp only [logKernelCriticalRate]
    linarith only [h]
  obtain ⟨D, hD, hkernel⟩ := exists_paired_logKernel_lower_of_rate_lt hrate
  let C : ℝ := c * D
  refine ⟨C, mul_pos hc hD, ?_⟩
  filter_upwards [hkernel, eventually_ge_atTop (k + 2)] with n hker hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hN : 0 < (n : ℝ) + 1 := by positivity
  have hsqrt : 0 < sqrt (n : ℝ) := sqrt_pos.mpr hnpos
  have hsqrtN : sqrt (n : ℝ) ≤ (n : ℝ) + 1 := by
    have h := sqrt_le_self_iff.mpr (Or.inr (show (1 : ℝ) ≤ n by
      exact_mod_cast (show 1 ≤ n by omega)))
    linarith only [h]
  change D * exp (-((2 * π + 1) * n)) ≤ pairedLogKernel y n at hker
  rw [weilLogShiftRecoveryMomentResponse_eq_coefficientColumn y k n (by omega),
    abs_mul, abs_div, abs_of_pos hsqrt, abs_of_pos (pairedLogKernel_pos y n)]
  calc
    (C / ((n : ℝ) + 1)) *
        exp ((n : ℝ) * ((n : ℝ) + 1) / 2 - (2 * π + 1) * n) =
        ((c * exp ((n : ℝ) * ((n : ℝ) + 1) / 2)) / ((n : ℝ) + 1)) *
          (D * exp (-((2 * π + 1) * n))) := by
      rw [sub_eq_add_neg, exp_add]
      dsimp only [C]
      ring
    _ ≤ (|weilLogShiftRecoveryCoefficientColumn k n| / ((n : ℝ) + 1)) *
        pairedLogKernel y n := mul_le_mul
      (div_le_div_of_nonneg_right (hcol n hn) hN.le) hker (by positivity) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_left (abs_nonneg _) hsqrt hsqrtN) (pairedLogKernel_pos y n).le

private theorem tendsto_quadratic_exponential_div_linear (c A : ℝ) (hc : 0 < c) :
    Tendsto (fun n : ℕ => (c / ((n : ℝ) + 1)) *
      exp ((n : ℝ) * ((n : ℝ) + 1) / 2 - A * n)) atTop atTop := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * A + 3)
  have hlower : ∀ᶠ n : ℕ in atTop,
      c * exp (n : ℝ) ≤ (c / ((n : ℝ) + 1)) *
        exp ((n : ℝ) * ((n : ℝ) + 1) / 2 - A * n) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hlinear : 2 * A + 3 ≤ (n : ℝ) := hN.le.trans hnR
    have hpoly : 2 * (n : ℝ) ≤ (n : ℝ) * ((n : ℝ) + 1) / 2 - A * n := by
      have h := mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (sub_nonneg.mpr hlinear)
      nlinarith only [h]
    have hden : 0 < (n : ℝ) + 1 := by positivity
    calc
      c * exp (n : ℝ) = (c / ((n : ℝ) + 1)) * (((n : ℝ) + 1) * exp (n : ℝ)) := by
        field_simp [hden.ne']
      _ ≤ (c / ((n : ℝ) + 1)) * (exp (n : ℝ) * exp (n : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (add_one_le_exp (n : ℝ)) (exp_pos _).le) (by positivity)
      _ = (c / ((n : ℝ) + 1)) * exp (2 * (n : ℝ)) := by
        rw [← exp_add, show (n : ℝ) + (n : ℝ) = 2 * (n : ℝ) by ring]
      _ ≤ _ := mul_le_mul_of_nonneg_left (exp_le_exp.mpr hpoly) (by positivity)
  have hexp : Tendsto (fun n : ℕ => c * exp (n : ℝ)) atTop atTop :=
    (tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul_atTop hc
  apply tendsto_atTop.mpr
  intro B
  filter_upwards [hlower, (tendsto_atTop.mp hexp) B] with n hn hB
  exact hB.trans hn

/-- Every fixed real exponential damping rate leaves late impulse-response
magnitudes tending to infinity at every real shift. -/
theorem exists_weilLogShiftRecoveryMomentResponse_all_exponential_dampings_runaway :
    ∃ K : ℕ, 625 ≤ K ∧ ∀ k : ℕ, K ≤ k → ∀ y A : ℝ,
      Tendsto (fun n : ℕ => exp (-(A * n)) *
        |weilLogShiftRecoveryMomentResponse y n k|) atTop atTop := by
  obtain ⟨K, hK, hlower⟩ := exists_weilLogShiftRecoveryMomentResponse_quadratic_exponential_lower
  refine ⟨K, hK, fun k hk y A => ?_⟩
  obtain ⟨C, hC, hresponse⟩ := hlower k hk y
  have hmodel := tendsto_quadratic_exponential_div_linear C (A + (2 * π + 1)) hC
  have hbound : ∀ᶠ n : ℕ in atTop,
      (C / ((n : ℝ) + 1)) *
        exp ((n : ℝ) * ((n : ℝ) + 1) / 2 - (A + (2 * π + 1)) * n) ≤
          exp (-(A * n)) * |weilLogShiftRecoveryMomentResponse y n k| := by
    filter_upwards [hresponse] with n hn
    calc
      _ = exp (-(A * n)) * ((C / ((n : ℝ) + 1)) *
          exp ((n : ℝ) * ((n : ℝ) + 1) / 2 - (2 * π + 1) * n)) := by
        have he : (n : ℝ) * ((n : ℝ) + 1) / 2 - (A + (2 * π + 1)) * n =
            -(A * n) + ((n : ℝ) * ((n : ℝ) + 1) / 2 - (2 * π + 1) * n) := by ring
        rw [he, exp_add]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hn (exp_pos _).le
  apply tendsto_atTop.mpr
  intro B
  filter_upwards [hbound, (tendsto_atTop.mp hmodel) B] with n hn hB
  exact hB.trans hn

/-- No real exponential damping makes a sufficiently late fixed response
column signed summable, at any real shift. -/
theorem exists_weilLogShiftRecoveryMomentResponse_all_exponential_dampings_not_summable :
    ∃ K : ℕ, 625 ≤ K ∧ ∀ k : ℕ, K ≤ k → ∀ y A : ℝ,
      ¬ Summable (fun n : ℕ => exp (-(A * n)) * weilLogShiftRecoveryMomentResponse y n k) := by
  obtain ⟨K, hK, hrunaway⟩ := exists_weilLogShiftRecoveryMomentResponse_all_exponential_dampings_runaway
  refine ⟨K, hK, fun k hk y A hs => ?_⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_atTop.mp (hrunaway k hk y A)) 1)
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    ((tendsto_order.mp hs.norm.tendsto_atTop_zero).2 1 (by norm_num))
  have hlarge := hN (max N M) (le_max_left _ _)
  have hsmall := hM (max N M) (le_max_right _ _)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _)] at hsmall
  exact (not_lt_of_ge hlarge) hsmall

end RHTower
