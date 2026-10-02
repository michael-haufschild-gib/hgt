import GaloisForLFunctions.RHTower.MobiusDivisorLatePrimeHeadAsymptotic
import GaloisForLFunctions.HTGeometry.ZetaVerticalAlmostPeriodic

/-!
# Logarithmic moments of the literal critical defect

Strong PNT gives every absolute logarithmic moment at the first Mellin
boundary. The fixed Euler correction is retained. These moments supply
domination for the old-cutoff part of the signed prime-head transfer.
-/

noncomputable section
open Filter Topology
namespace RHTower

private theorem summable_psiError_log_moment (k : ℕ) :
    Summable (fun n : ℕ =>
      |Chebyshev.psi n - n| * Real.log n ^ k / (n : ℝ) ^ (2 : ℕ)) := by
  obtain ⟨C, c, hc, hC, hbound⟩ := exists_psi_error_eventually
  have hc2 : 0 < c / 2 := by linarith
  have hsaving : Tendsto
      (fun x : ℝ => Real.log x ^ k * Real.exp (-(c / 2 * Real.sqrt (Real.log x))))
      atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast, ← Real.sqrt_eq_rpow] using
      Sieve.tendsto_logRpow_mul_expSaving (d := (1 : ℝ) / 2)
        (by norm_num) hc2 (k : ℝ)
  have hsum := (GaloisForLFunctions.HTGeometry.summable_exp_neg_sqrt_log_div hc2).mul_left C
  apply hsum.of_norm_bounded_eventually_nat
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hbound,
    tendsto_natCast_atTop_atTop.eventually
      (hsaving.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))),
    eventually_ge_atTop (1 : ℕ)] with n hn hs hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
  have hp : 0 ≤ Real.log n ^ k := pow_nonneg hlog k
  have he : 0 < Real.exp (-(c / 2 * Real.sqrt (Real.log n))) := Real.exp_pos _
  have hsplit : Real.exp (-c * Real.sqrt (Real.log n)) =
      Real.exp (-(c / 2 * Real.sqrt (Real.log n))) *
        Real.exp (-(c / 2 * Real.sqrt (Real.log n))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    |Chebyshev.psi n - n| * Real.log n ^ k / (n : ℝ) ^ (2 : ℕ) ≤
        (C * ((n : ℝ) * Real.exp (-c * Real.sqrt (Real.log n)))) *
          Real.log n ^ k / (n : ℝ) ^ (2 : ℕ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hn hp) (sq_nonneg _)
    _ = C * (Real.log n ^ k * Real.exp (-(c / 2 * Real.sqrt (Real.log n)))) *
        (Real.exp (-(c / 2 * Real.sqrt (Real.log n))) / n) := by
      rw [hsplit]
      field_simp [hnpos.ne']
    _ ≤ C * (Real.exp (-(c / 2 * Real.sqrt (Real.log n))) / n) := by
      have hb := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hs.le hC) (div_nonneg he.le hnpos.le)
      simpa only [mul_one] using hb

/-- Every absolute logarithmic moment of the actual critical step defect is
summable at the boundary. No RH-strength error bound is assumed. -/
theorem summable_psiDefect_log_moment (k : ℕ) :
    Summable (fun n : ℕ =>
      |psiDefect n| * Real.log n ^ k / (n : ℝ) ^ (2 : ℕ)) := by
  have hconstant : Summable (fun n : ℕ =>
      (2 * |Real.eulerMascheroniConstant|) *
        (Real.log n ^ k / (n : ℝ) ^ (2 : ℕ))) := by
    have h := (HTGeometry.summable_log_pow_div_nat_rpow k
      (sigma := 2) (by norm_num)).mul_left (2 * |Real.eulerMascheroniConstant|)
    simpa only [Real.rpow_two] using h
  apply ((summable_psiError_log_moment k).add hconstant).of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hdef : psiDefect n = (Chebyshev.psi n - n) + 2 * Real.eulerMascheroniConstant := by
    rw [psiDefect, chebyshevPsi_eq_psi]
  have hb : |psiDefect n| ≤ |Chebyshev.psi n - n| + 2 * |Real.eulerMascheroniConstant| := by
    rw [hdef]
    simpa only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using
      abs_add_le (Chebyshev.psi n - n) (2 * Real.eulerMascheroniConstant)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hb (pow_nonneg hlog k)) (sq_nonneg (n : ℝ))
  simpa only [Pi.add_apply, add_mul, add_div, mul_div_assoc] using h

end RHTower
