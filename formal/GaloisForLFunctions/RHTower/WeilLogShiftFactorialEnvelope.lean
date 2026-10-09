import GaloisForLFunctions.RHTower.WeilLogShiftSuperexponentialResponse
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Factorial powers are dominated by the native quadratic envelope

Every fixed natural power of the factorial is eventually below every
positive quadratic exponential. Dividing the native response model by such
a factorial power still leaves it tending to infinity after arbitrary
fixed real exponential damping.
-/

open Filter Topology Real

namespace RHTower

/-- Every fixed factorial power is eventually below every positive
quadratic exponential; no Stirling estimate is needed. -/
theorem eventually_weilLogShift_factorial_pow_le_quadratic_exp
    (m : ℕ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, (n.factorial : ℝ) ^ m ≤ exp (η * (n : ℝ) ^ 2) := by
  have hlog : Tendsto (fun n : ℕ => log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    have h := (tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [Function.comp_def, pow_one, one_mul, add_zero] using h
  have hsmall := (tendsto_order.mp hlog).2 (η / ((m : ℝ) + 1)) (by positivity)
  filter_upwards [hsmall, eventually_ge_atTop 1] with n hnlog hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog0 : 0 ≤ log (n : ℝ) := log_nonneg (by exact_mod_cast hn)
  have hcross := (div_le_div_iff₀ hnpos (show 0 < (m : ℝ) + 1 by positivity)).mp hnlog.le
  have hbudget : (m : ℝ) * log (n : ℝ) ≤ η * n := by
    nlinarith only [hcross, hlog0]
  have hscaled := mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg (α := ℝ) n)
  have hexponent : (m : ℝ) * (n : ℝ) * log (n : ℝ) ≤ η * (n : ℝ) ^ 2 := by
    nlinarith only [hscaled]
  have hfactorial : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by
    exact_mod_cast Nat.factorial_le_pow n
  calc
    (n.factorial : ℝ) ^ m ≤ ((n : ℝ) ^ n) ^ m :=
      pow_le_pow_left₀ (by positivity) hfactorial m
    _ = exp ((m : ℝ) * (n : ℝ) * log (n : ℝ)) := by
      rw [show (m : ℝ) * (n : ℝ) * log (n : ℝ) =
        (m : ℝ) * ((n : ℝ) * log (n : ℝ)) by ring,
        exp_nat_mul, exp_nat_mul, exp_log hnpos]
    _ ≤ _ := exp_le_exp.mpr hexponent

/-- The native quadratic response model defeats every fixed factorial
power and real exponential damping rate, including its linear denominator. -/
theorem tendsto_weilLogShift_factorial_normalized_quadratic_model
    (c A : ℝ) (hc : 0 < c) (m : ℕ) :
    Tendsto (fun n : ℕ => ((c / ((n : ℝ) + 1)) *
      exp ((n : ℝ) * ((n : ℝ) + 1) / 2 - A * n)) / (n.factorial : ℝ) ^ m)
      atTop atTop := by
  obtain ⟨N, hN⟩ := exists_nat_gt (4 * A + 6)
  have hfactorial := eventually_weilLogShift_factorial_pow_le_quadratic_exp m
    (1 / 4 : ℝ) (by norm_num)
  have hlower : ∀ᶠ n : ℕ in atTop,
      c * exp (n : ℝ) ≤ ((c / ((n : ℝ) + 1)) *
        exp ((n : ℝ) * ((n : ℝ) + 1) / 2 - A * n)) / (n.factorial : ℝ) ^ m := by
    filter_upwards [hfactorial, eventually_ge_atTop N] with n hfac hn
    have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hlinear : 4 * A + 6 ≤ (n : ℝ) := hN.le.trans hnR
    have hpoly : 2 * (n : ℝ) ≤ (n : ℝ) * ((n : ℝ) + 1) / 2 - A * n -
        (1 / 4 : ℝ) * (n : ℝ) ^ 2 := by
      have h := mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (sub_nonneg.mpr hlinear)
      nlinarith only [h]
    have hden : 0 < (n : ℝ) + 1 := by positivity
    have hfacpos : 0 < (n.factorial : ℝ) ^ m :=
      pow_pos (by exact_mod_cast Nat.factorial_pos n) m
    calc
      c * exp (n : ℝ) = (c / ((n : ℝ) + 1)) * (((n : ℝ) + 1) * exp (n : ℝ)) := by
        field_simp [hden.ne']
      _ ≤ (c / ((n : ℝ) + 1)) * (exp (n : ℝ) * exp (n : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (add_one_le_exp (n : ℝ)) (exp_pos _).le) (by positivity)
      _ = (c / ((n : ℝ) + 1)) * exp (2 * (n : ℝ)) := by
        rw [← exp_add, show (n : ℝ) + (n : ℝ) = 2 * (n : ℝ) by ring]
      _ ≤ (c / ((n : ℝ) + 1)) * exp ((n : ℝ) * ((n : ℝ) + 1) / 2 - A * n -
          (1 / 4 : ℝ) * (n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left (exp_le_exp.mpr hpoly) (by positivity)
      _ = ((c / ((n : ℝ) + 1)) * exp ((n : ℝ) * ((n : ℝ) + 1) / 2 - A * n)) /
          exp ((1 / 4 : ℝ) * (n : ℝ) ^ 2) := by
        rw [exp_sub]
        ring
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hfacpos hfac
  have hexp : Tendsto (fun n : ℕ => c * exp (n : ℝ)) atTop atTop :=
    (tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul_atTop hc
  apply tendsto_atTop.mpr
  intro B
  filter_upwards [hlower, (tendsto_atTop.mp hexp) B] with n hn hB
  exact hB.trans hn

end RHTower
