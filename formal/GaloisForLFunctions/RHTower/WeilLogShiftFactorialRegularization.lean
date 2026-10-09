import GaloisForLFunctions.RHTower.WeilLogShiftFactorialEnvelope

/-!
# No finite factorial-power regularization of late columns

One native tail threshold works for every natural factorial power, every
real exponential rate, and every real shift. Normalized column magnitudes
still tend to infinity; the corresponding signed series are nonsummable,
and no eventual factorial-power/exponential majorant exists.
-/

open Filter Topology Real

namespace RHTower

open WeilExcess

/-- Every late coefficient column defeats every fixed factorial power and
real exponential damping, with a common threshold before all parameters. -/
theorem exists_weilLogShiftRecoveryCoefficientColumn_factorial_regularization_runaway :
    ∃ K : ℕ, 625 ≤ K ∧ ∀ k : ℕ, K ≤ k → ∀ (m : ℕ) (A : ℝ),
      Tendsto (fun n : ℕ => exp (-(A * n)) *
        |weilLogShiftRecoveryCoefficientColumn k n| / (n.factorial : ℝ) ^ m) atTop atTop := by
  obtain ⟨K, hK, hcoeff⟩ := exists_weilLogShiftRecoveryCoefficientColumn_quadratic_exponential_lower
  refine ⟨K, hK, fun k hk m A => ?_⟩
  obtain ⟨c, hc, hcol⟩ := hcoeff k hk
  have hmodel := tendsto_weilLogShift_factorial_normalized_quadratic_model c A hc m
  have hbound : ∀ᶠ n : ℕ in atTop,
      ((c / ((n : ℝ) + 1)) * exp ((n : ℝ) * ((n : ℝ) + 1) / 2 - A * n)) /
        (n.factorial : ℝ) ^ m ≤
          exp (-(A * n)) * |weilLogShiftRecoveryCoefficientColumn k n| / (n.factorial : ℝ) ^ m := by
    filter_upwards [eventually_ge_atTop (k + 2)] with n hn
    apply div_le_div_of_nonneg_right ?_ (by positivity)
    have hden1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      linarith only [Nat.cast_nonneg (α := ℝ) n]
    have hfrac : c / ((n : ℝ) + 1) ≤ c := by
      simpa only [div_one] using
        div_le_div_of_nonneg_left hc.le (by norm_num : (0 : ℝ) < 1) hden1
    calc
      _ = exp (-(A * n)) * ((c / ((n : ℝ) + 1)) *
          exp ((n : ℝ) * ((n : ℝ) + 1) / 2)) := by
        rw [sub_eq_add_neg, exp_add]
        ring
      _ ≤ exp (-(A * n)) * (c * exp ((n : ℝ) * ((n : ℝ) + 1) / 2)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hfrac (exp_pos _).le) (exp_pos _).le
      _ ≤ _ := mul_le_mul_of_nonneg_left (hcol n hn) (exp_pos _).le
  apply tendsto_atTop.mpr
  intro B
  filter_upwards [hbound, (tendsto_atTop.mp hmodel) B] with n hn hB
  exact hB.trans hn

/-- Factorial powers and exponential damping together fail to control
late response columns at every real shift, under one common threshold. -/
theorem exists_weilLogShiftRecoveryMomentResponse_factorial_regularization_runaway :
    ∃ K : ℕ, 625 ≤ K ∧ ∀ k : ℕ, K ≤ k → ∀ (y : ℝ) (m : ℕ) (A : ℝ),
      Tendsto (fun n : ℕ => exp (-(A * n)) *
        |weilLogShiftRecoveryMomentResponse y n k| / (n.factorial : ℝ) ^ m) atTop atTop := by
  obtain ⟨K, hK, hlower⟩ := exists_weilLogShiftRecoveryMomentResponse_quadratic_exponential_lower
  refine ⟨K, hK, fun k hk y m A => ?_⟩
  obtain ⟨C, hC, hresponse⟩ := hlower k hk y
  have hmodel := tendsto_weilLogShift_factorial_normalized_quadratic_model
    C (A + (2 * π + 1)) hC m
  have hbound : ∀ᶠ n : ℕ in atTop,
      ((C / ((n : ℝ) + 1)) *
        exp ((n : ℝ) * ((n : ℝ) + 1) / 2 - (A + (2 * π + 1)) * n)) /
          (n.factorial : ℝ) ^ m ≤
            exp (-(A * n)) * |weilLogShiftRecoveryMomentResponse y n k| / (n.factorial : ℝ) ^ m := by
    filter_upwards [hresponse] with n hn
    apply div_le_div_of_nonneg_right ?_ (by positivity)
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

private theorem not_summable_of_factorial_normalized_runaway
    (f : ℕ → ℝ) (m : ℕ) (A : ℝ)
    (h : Tendsto (fun n : ℕ => exp (-(A * n)) * |f n| / (n.factorial : ℝ) ^ m) atTop atTop) :
    ¬ Summable (fun n : ℕ => exp (-(A * n)) * f n / (n.factorial : ℝ) ^ m) := by
  intro hs
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_atTop.mp h) 1)
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    ((tendsto_order.mp hs.norm.tendsto_atTop_zero).2 1 (by norm_num))
  have hlarge := hN (max N M) (le_max_left _ _)
  have hsmall := hM (max N M) (le_max_right _ _)
  have hfacpos : 0 < ((max N M).factorial : ℝ) ^ m :=
    pow_pos (by exact_mod_cast Nat.factorial_pos (max N M)) m
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (exp_pos _), abs_of_pos hfacpos] at hsmall
  exact (not_lt_of_ge hlarge) hsmall

/-- Every factorial-and-exponentially normalized late coefficient series
is signed nonsummable. -/
theorem exists_weilLogShiftRecoveryCoefficientColumn_factorial_regularization_not_summable :
    ∃ K : ℕ, 625 ≤ K ∧ ∀ k : ℕ, K ≤ k → ∀ (m : ℕ) (A : ℝ),
      ¬ Summable (fun n : ℕ => exp (-(A * n)) *
        weilLogShiftRecoveryCoefficientColumn k n / (n.factorial : ℝ) ^ m) := by
  obtain ⟨K, hK, hrunaway⟩ := exists_weilLogShiftRecoveryCoefficientColumn_factorial_regularization_runaway
  exact ⟨K, hK, fun k hk m A => not_summable_of_factorial_normalized_runaway
    (weilLogShiftRecoveryCoefficientColumn k) m A (hrunaway k hk m A)⟩

/-- Every factorial-and-exponentially normalized late response series
is signed nonsummable at every real shift. -/
theorem exists_weilLogShiftRecoveryMomentResponse_factorial_regularization_not_summable :
    ∃ K : ℕ, 625 ≤ K ∧ ∀ k : ℕ, K ≤ k → ∀ (y : ℝ) (m : ℕ) (A : ℝ),
      ¬ Summable (fun n : ℕ => exp (-(A * n)) *
        weilLogShiftRecoveryMomentResponse y n k / (n.factorial : ℝ) ^ m) := by
  obtain ⟨K, hK, hrunaway⟩ := exists_weilLogShiftRecoveryMomentResponse_factorial_regularization_runaway
  exact ⟨K, hK, fun k hk y m A => not_summable_of_factorial_normalized_runaway
    (fun n => weilLogShiftRecoveryMomentResponse y n k) m A (hrunaway k hk y m A)⟩

private theorem no_eventual_factorial_majorant_of_runaway
    (f : ℕ → ℝ) (m : ℕ) (A : ℝ)
    (h : Tendsto (fun n : ℕ => exp (-(A * n)) * |f n| / (n.factorial : ℝ) ^ m) atTop atTop)
    (D : ℝ) :
    ¬ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |f n| ≤ D * exp (A * n) * (n.factorial : ℝ) ^ m := by
  rintro ⟨N, hN⟩
  obtain ⟨M, hM⟩ := eventually_atTop.mp ((tendsto_atTop.mp h) (D + 1))
  let n : ℕ := max N M
  have hbound := hN n (le_max_left _ _)
  have hlarge := hM n (le_max_right _ _)
  have hfacpos : 0 < (n.factorial : ℝ) ^ m :=
    pow_pos (by exact_mod_cast Nat.factorial_pos n) m
  have hnormalized : exp (-(A * n)) * |f n| / (n.factorial : ℝ) ^ m ≤ D := by
    calc
      _ ≤ (exp (-(A * n)) * (D * exp (A * n) * (n.factorial : ℝ) ^ m)) /
          (n.factorial : ℝ) ^ m := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hbound (exp_pos _).le) hfacpos.le
      _ = D := by
        have hid : exp (-(A * n)) * (D * exp (A * n) * (n.factorial : ℝ) ^ m) =
            D * (n.factorial : ℝ) ^ m := by
          calc
            _ = (exp (-(A * n)) * exp (A * n)) * (D * (n.factorial : ℝ) ^ m) := by ring
            _ = _ := by rw [← exp_add, neg_add_cancel, exp_zero, one_mul]
        rw [hid, mul_div_assoc, div_self hfacpos.ne', mul_one]
  linarith only [hlarge, hnormalized]

/-- No tail of a late coefficient column has any finite factorial-power
majorant, even with an arbitrary real exponential rate and prefactor. -/
theorem exists_weilLogShiftRecoveryCoefficientColumn_no_factorial_majorant :
    ∃ K : ℕ, 625 ≤ K ∧ ∀ k : ℕ, K ≤ k → ∀ (m : ℕ) (A D : ℝ),
      ¬ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |weilLogShiftRecoveryCoefficientColumn k n| ≤
        D * exp (A * n) * (n.factorial : ℝ) ^ m := by
  obtain ⟨K, hK, hrunaway⟩ := exists_weilLogShiftRecoveryCoefficientColumn_factorial_regularization_runaway
  exact ⟨K, hK, fun k hk m A D => no_eventual_factorial_majorant_of_runaway
    (weilLogShiftRecoveryCoefficientColumn k) m A (hrunaway k hk m A) D⟩

/-- No tail of a late response column has any finite factorial-power
majorant at any real shift. -/
theorem exists_weilLogShiftRecoveryMomentResponse_no_factorial_majorant :
    ∃ K : ℕ, 625 ≤ K ∧ ∀ k : ℕ, K ≤ k → ∀ (y : ℝ) (m : ℕ) (A D : ℝ),
      ¬ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |weilLogShiftRecoveryMomentResponse y n k| ≤
        D * exp (A * n) * (n.factorial : ℝ) ^ m := by
  obtain ⟨K, hK, hrunaway⟩ := exists_weilLogShiftRecoveryMomentResponse_factorial_regularization_runaway
  exact ⟨K, hK, fun k hk y m A D => no_eventual_factorial_majorant_of_runaway
    (fun n => weilLogShiftRecoveryMomentResponse y n k) m A (hrunaway k hk y m A) D⟩

end RHTower
