import GaloisForLFunctions.RHTower.Sieve.InghamFixedGabrielBudget

open Complex MeasureTheory Set

namespace RHTower.Sieve

noncomputable section

/-- Elementary detector inequality on the full exponent range used by Gabriel interpolation. -/
theorem log_one_add_sq_le_two_mul_rpow
    {x p : ℝ} (hx : 0 ≤ x) (hp1 : 1 ≤ p) (hp2 : p ≤ 2) :
    Real.log (1 + x ^ 2) ≤ 2 * x ^ p := by
  have hlogquad : Real.log (1 + x ^ 2) ≤ x ^ 2 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < 1 + x ^ 2 by positivity)
    nlinarith
  rcases eq_or_lt_of_le hx with rfl | hxpos
  · rw [Real.zero_rpow (by linarith : p ≠ 0)]
    norm_num
  by_cases hxone : x ≤ 1
  · have hrpow : x ^ (2 : ℝ) ≤ x ^ p :=
      Real.rpow_le_rpow_of_exponent_ge hxpos hxone hp2
    have hsq : x ^ 2 = x ^ (2 : ℝ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hpnonneg : 0 ≤ x ^ p := Real.rpow_nonneg hxpos.le _
    calc
      Real.log (1 + x ^ 2) ≤ x ^ 2 := hlogquad
      _ = x ^ (2 : ℝ) := hsq
      _ ≤ x ^ p := hrpow
      _ ≤ 2 * x ^ p := by linarith
  · have hxone' : 1 ≤ x := le_of_not_ge hxone
    have hsq : 1 + x ^ 2 ≤ (1 + x) ^ 2 := by nlinarith
    have hlogmono : Real.log (1 + x ^ 2) ≤ Real.log ((1 + x) ^ 2) :=
      Real.strictMonoOn_log.monotoneOn
        (show 0 < 1 + x ^ 2 by positivity)
        (show 0 < (1 + x) ^ 2 by positivity) hsq
    have hloglin : Real.log (1 + x) ≤ x := by
      have h := Real.log_le_sub_one_of_pos (show 0 < 1 + x by positivity)
      linarith
    have hxpow : x ≤ x ^ p := by
      simpa only [Real.rpow_one] using
        (Real.rpow_le_rpow_of_exponent_le hxone' hp1)
    calc
      Real.log (1 + x ^ 2) ≤ Real.log ((1 + x) ^ 2) := hlogmono
      _ = 2 * Real.log (1 + x) := by rw [Real.log_pow]; norm_num
      _ ≤ 2 * x := by linarith
      _ ≤ 2 * x ^ p := by linarith

/-- Logarithm of the classical quadratic detector is controlled by the interpolated moment. -/
theorem log_norm_one_sub_sq_le_two_mul_norm_rpow
    (z : ℂ) {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2) :
    Real.log ‖1 - z ^ 2‖ ≤ 2 * ‖z‖ ^ p := by
  have hnorm : ‖1 - z ^ 2‖ ≤ 1 + ‖z‖ ^ 2 := by
    calc
      ‖1 - z ^ 2‖ ≤ ‖(1 : ℂ)‖ + ‖z ^ 2‖ := norm_sub_le _ _
      _ = 1 + ‖z‖ ^ 2 := by rw [norm_one, norm_pow]
  have hrightpos : 0 < 1 + ‖z‖ ^ 2 := by positivity
  have hmoment := log_one_add_sq_le_two_mul_rpow (norm_nonneg z) hp1 hp2
  by_cases hz : ‖1 - z ^ 2‖ = 0
  · rw [hz, Real.log_zero]
    positivity
  · have hleftpos : 0 < ‖1 - z ^ 2‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    exact (Real.strictMonoOn_log.monotoneOn
      (show ‖1 - z ^ 2‖ ∈ Set.Ioi (0 : ℝ) by exact hleftpos)
      (show 1 + ‖z‖ ^ 2 ∈ Set.Ioi (0 : ℝ) by exact hrightpos)
      hnorm).trans hmoment

/-- Literal unregularized Ingham detector bound at Route T's fixed Gabriel power. -/
theorem log_norm_inghamClassicalDetector_le_fixedMoment
    (X : ℕ) (s : ℂ) :
    Real.log ‖1 - (riemannZeta s * inghamMollifier X s - 1) ^ 2‖ ≤
      2 * ‖riemannZeta s * inghamMollifier X s - 1‖ ^
        inghamFixedGabrielInteriorPower := by
  exact log_norm_one_sub_sq_le_two_mul_norm_rpow _
    (le_trans (by norm_num : (1 : ℝ) ≤ 4 / 3)
      four_thirds_le_inghamFixedGabrielInteriorPower)
    inghamFixedGabrielInteriorPower_le_two

end

end RHTower.Sieve
