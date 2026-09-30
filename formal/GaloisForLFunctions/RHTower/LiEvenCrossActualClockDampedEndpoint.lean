import GaloisForLFunctions.RHTower.LiEvenCrossActualClockVolterra
import GaloisForLFunctions.RHTower.XiEndpointCentralMomentBoundaryValue
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Exact endpoint-damped signed area of the actual clock

The literal odd source coefficients retain their raw factorial normalization. Integrating
the complete absolute damped series yields the geometric envelope `A / (4 * 600^j)`.
This closes the interchange and identifies the signed area with one quarter of the
installed arithmetic endpoint curvature. The absolute mass is at most `150 * A / 599`.

No zero-location or pointwise clock-sign premise enters these statements.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace RHTower
noncomputable section
private theorem integral_exp_neg_two_mul_pow (n : ℕ) :
    (∫ t : ℝ in Ioi 0, Real.exp (-2*t) * t^n) =
      (n.factorial : ℝ) / 2^(n+1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (n:ℝ)+1) (r := 2) (by positivity) (by norm_num)
  simp only [add_sub_cancel_right, Real.rpow_natCast] at h
  rw [Real.Gamma_nat_eq_factorial] at h
  have hp : ((1/2:ℝ)^((n:ℝ)+1)) = (1/2:ℝ)^(n+1) := by
    rw [show (n:ℝ)+1 = ((n+1:ℕ):ℝ) by norm_cast, Real.rpow_natCast]
  rw [hp] at h
  simpa only [mul_comm, one_div_pow, div_eq_mul_inv, one_mul, neg_mul, mul_neg, inv_pow] using h

private theorem integrable_exp_neg_two_mul_pow (n : ℕ) :
    IntegrableOn (fun t : ℝ => Real.exp (-2*t) * t^n) (Ioi 0) := by
  have h := Real.GammaIntegral_convergent (s := (n:ℝ)+1) (by positivity)
  simp only [add_sub_cancel_right, Real.rpow_natCast] at h
  apply h.mono' (by fun_prop)
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  have ht0 : 0 ≤ t := le_of_lt ht
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith))
    (pow_nonneg ht0 _)

private def dampedTerm (j : ℕ) (t : ℝ) : ℝ :=
  Real.exp (-2*t) * liEvenCrossActualClockResponseTerm t j
private theorem dampedTerm_eq (j : ℕ) (t : ℝ) :
    dampedTerm j t = ((-1:ℝ)^j * normalizedPrimeArchMoment j /
      ((2*j+1).factorial:ℝ)) * (Real.exp (-2*t)*t^(2*j+1)) := by
  unfold dampedTerm liEvenCrossActualClockResponseTerm
  ring
private theorem integrable_dampedTerm (j : ℕ) :
    IntegrableOn (dampedTerm j) (Ioi 0) := by
  exact ((integrable_exp_neg_two_mul_pow (2*j+1)).const_mul
    ((-1:ℝ)^j * normalizedPrimeArchMoment j / ((2*j+1).factorial:ℝ))).congr
    (Filter.Eventually.of_forall (fun t => (dampedTerm_eq j t).symm))
private theorem integral_dampedTerm (j : ℕ) :
    (∫t:ℝ in Ioi 0, dampedTerm j t) =
      (1/4:ℝ)*normalizedPrimeArchMoment j*(-1/4:ℝ)^j := by
  simp_rw [dampedTerm_eq]
  rw [integral_const_mul, integral_exp_neg_two_mul_pow]
  have hf : ((2*j+1).factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hpow : (2:ℝ)^(2*j+1+1) = 4 * 4^j := by
    rw [show 2*j+1+1 = 2*j+2 by omega, pow_add, pow_mul]
    norm_num
    ring
  rw [hpow]
  have h4 : (4:ℝ)^j * (-(1/4:ℝ))^j = (-1:ℝ)^j := by
    rw [← mul_pow]
    congr 1
    norm_num
  field_simp
  calc
    _ = normalizedPrimeArchMoment j * ((4:ℝ)^j * (-(1/4:ℝ))^j) := by rw [h4]; ring
    _ = _ := by ring

@[fun_prop] private theorem continuous_dampedTerm (j : ℕ) : Continuous (dampedTerm j) := by
  unfold dampedTerm liEvenCrossActualClockResponseTerm
  fun_prop
private theorem norm_dampedTerm_eq (j : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖dampedTerm j t‖ = (|normalizedPrimeArchMoment j| /
      ((2*j+1).factorial:ℝ)) * (Real.exp (-2*t)*t^(2*j+1)) := by
  rw [dampedTerm_eq]
  simp [norm_mul, norm_div, norm_pow, Real.norm_eq_abs, abs_of_nonneg ht]
private theorem integral_norm_dampedTerm (j : ℕ) :
    (∫t:ℝ in Ioi 0, ‖dampedTerm j t‖) =
      |normalizedPrimeArchMoment j| / (2:ℝ)^(2*j+2) := by
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun t ht => norm_dampedTerm_eq j (le_of_lt ht))]
  rw [integral_const_mul, integral_exp_neg_two_mul_pow]
  have hf : ((2*j+1).factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  rw [show 2*j+1+1 = 2*j+2 by omega]
  field_simp
private theorem integral_norm_dampedTerm_le (j : ℕ) :
    (∫t:ℝ in Ioi 0, ‖dampedTerm j t‖) ≤
      (xiShiftAbsoluteMass 0/4) * (1/600:ℝ)^j := by
  rw [integral_norm_dampedTerm]
  have hm := abs_normalizedPrimeArchMoment_add_le_secondMomentRadius 0 j
  simp only [zero_add] at hm
  have hp : (2:ℝ)^(2*j+2) = 4*4^j := by
    rw [pow_add, pow_mul]
    norm_num
    ring
  calc
    _ ≤ ((1/150:ℝ)^j * xiShiftAbsoluteMass 0)/(2:ℝ)^(2*j+2) := by
      exact div_le_div_of_nonneg_right hm (by positivity)
    _ = _ := by
      rw [hp]
      have hpow : (1/600:ℝ)^j = (1/150:ℝ)^j / (4:ℝ)^j := by
        rw [← div_pow]
        congr 1
        norm_num
      rw [hpow]
      ring
private theorem summable_integral_norm_dampedTerm :
    Summable (fun j : ℕ => ∫t:ℝ in Ioi 0, ‖dampedTerm j t‖) := by
  apply Summable.of_nonneg_of_le (fun j => integral_nonneg (fun t => norm_nonneg _))
    integral_norm_dampedTerm_le
  exact (hasSum_geometric_of_lt_one (r := (1/600:ℝ)) (by norm_num) (by norm_num)).summable.mul_left _
private theorem moment_abs_le_mass (j : ℕ) :
    |normalizedPrimeArchMoment j| ≤ xiShiftAbsoluteMass 0 := by
  have h := abs_normalizedPrimeArchMoment_add_le_secondMomentRadius 0 j
  simp only [zero_add] at h
  have hp : (1/150:ℝ)^j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  exact h.trans (by simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hp (xiShiftAbsoluteMass_pos 0).le)
private theorem summable_norm_dampedTerm (t : ℝ) :
    Summable (fun j : ℕ => ‖dampedTerm j t‖) := by
  simpa only [dampedTerm] using
    ((summable_liEvenCrossActualClockResponseTerm t).mul_left (Real.exp (-2*t))).norm
private theorem damped_eq_tsum (t : ℝ) :
    Real.exp (-2*t)*liEvenCrossActualClockResponse t = ∑'j:ℕ, dampedTerm j t := by
  rw [liEvenCrossActualClockResponse_eq_tsum]
  simp only [dampedTerm, tsum_mul_left]
private theorem tsum_norm_dampedTerm_le {t : ℝ} (ht : 0 ≤ t) :
    (∑'j:ℕ, ‖dampedTerm j t‖) ≤ xiShiftAbsoluteMass 0 * Real.exp (-t) := by
  have hmajor := (Real.hasSum_sinh t).summable.mul_left
    (xiShiftAbsoluteMass 0 * Real.exp (-2*t))
  have hterm (j : ℕ) : ‖dampedTerm j t‖ ≤
      (xiShiftAbsoluteMass 0 * Real.exp (-2*t)) *
        (t^(2*j+1)/((2*j+1).factorial:ℝ)) := by
    rw [norm_dampedTerm_eq j ht]
    calc
      _ ≤ (xiShiftAbsoluteMass 0/((2*j+1).factorial:ℝ)) *
          (Real.exp (-2*t)*t^(2*j+1)) := by
        gcongr
        exact moment_abs_le_mass j
      _ = _ := by ring
  calc
    _ ≤ ∑'j:ℕ, (xiShiftAbsoluteMass 0 * Real.exp (-2*t)) *
        (t^(2*j+1)/((2*j+1).factorial:ℝ)) :=
      (summable_norm_dampedTerm t).tsum_le_tsum hterm hmajor
    _ = (xiShiftAbsoluteMass 0 * Real.exp (-2*t))*Real.sinh t := by
      rw [tsum_mul_left, (Real.hasSum_sinh t).tsum_eq]
    _ ≤ (xiShiftAbsoluteMass 0 * Real.exp (-2*t))*Real.exp t := by
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg (xiShiftAbsoluteMass_pos 0).le (Real.exp_pos _).le)
      rw [Real.sinh_eq]
      linarith [Real.exp_pos t, Real.exp_pos (-t)]
    _ = xiShiftAbsoluteMass 0*Real.exp (-t) := by
      rw [mul_assoc, ← Real.exp_add, show -2*t+t = -t by ring]
private theorem integrable_tsum_norm_dampedTerm :
    IntegrableOn (fun t:ℝ => ∑'j:ℕ, ‖dampedTerm j t‖) (Ioi 0) := by
  have hg := (exp_neg_integrableOn_Ioi 0 (b := 1) (by norm_num)).const_mul (xiShiftAbsoluteMass 0)
  simp only [neg_one_mul] at hg
  apply hg.mono' (AEStronglyMeasurable.tsum (fun j => (continuous_dampedTerm j).norm.aestronglyMeasurable))
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg (fun j => norm_nonneg _))]
  exact tsum_norm_dampedTerm_le (le_of_lt ht)

/-- Absolute integrability of the literal actual clock with endpoint damping. -/
theorem integrableOn_liEvenCrossActualClock_dampedEndpoint :
    IntegrableOn (fun t:ℝ => Real.exp (-2*t)*liEvenCrossActualClockResponse t) (Ioi 0) := by
  apply integrable_tsum_norm_dampedTerm.mono'
    (((by fun_prop : Continuous (fun t:ℝ => Real.exp (-2*t))).mul
      continuous_liEvenCrossActualClockResponse).aestronglyMeasurable)
  filter_upwards with t
  change ‖Real.exp (-2*t)*liEvenCrossActualClockResponse t‖ ≤ _
  rw [damped_eq_tsum]
  exact norm_tsum_le_tsum_norm (summable_norm_dampedTerm t)

/-- The complete endpoint-damped absolute mass retains the sharp integrated source envelope. -/
theorem integral_norm_liEvenCrossActualClock_dampedEndpoint_le :
    (∫t:ℝ in Ioi 0, ‖Real.exp (-2*t)*liEvenCrossActualClockResponse t‖) ≤
      150*xiShiftAbsoluteMass 0/599 := by
  have hmono : (∫t:ℝ in Ioi 0, ‖Real.exp (-2*t)*liEvenCrossActualClockResponse t‖) ≤
      ∫t:ℝ in Ioi 0, ∑'j:ℕ, ‖dampedTerm j t‖ := by
    apply integral_mono_ae integrableOn_liEvenCrossActualClock_dampedEndpoint.norm
      integrable_tsum_norm_dampedTerm
    filter_upwards with t
    rw [damped_eq_tsum]
    exact norm_tsum_le_tsum_norm (summable_norm_dampedTerm t)
  have hsum := integral_tsum_of_summable_integral_norm
    (fun j => (integrable_dampedTerm j).norm)
    (summable_integral_norm_dampedTerm.congr (fun j => by simp only [norm_norm]))
  rw [← hsum] at hmono
  apply hmono.trans
  calc
    _ ≤ ∑'j:ℕ, (xiShiftAbsoluteMass 0/4)*(1/600:ℝ)^j :=
      summable_integral_norm_dampedTerm.tsum_le_tsum integral_norm_dampedTerm_le
        ((hasSum_geometric_of_lt_one (r := (1/600:ℝ)) (by norm_num) (by norm_num)).summable.mul_left _)
    _ = _ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      norm_num
      ring
private theorem moment_endpoint_real :
    (∑'j:ℕ, normalizedPrimeArchMoment j*(-1/4:ℝ)^j) = xiEndpointCompletedCurvature := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_tsum]
  convert tsum_normalizedPrimeArchMoment_endpointCurvature using 1
  push_cast
  rfl

/-- Exact signed actual-clock area at the arithmetic endpoint. -/
theorem integral_liEvenCrossActualClock_dampedEndpoint :
    (∫t:ℝ in Ioi 0, Real.exp (-2*t)*liEvenCrossActualClockResponse t) =
      xiEndpointCompletedCurvature/4 := by
  have hsum := integral_tsum_of_summable_integral_norm integrable_dampedTerm
    summable_integral_norm_dampedTerm
  calc
    _ = ∫t:ℝ in Ioi 0, ∑'j:ℕ, dampedTerm j t := by
      apply integral_congr_ae
      filter_upwards with t using damped_eq_tsum t
    _ = ∑'j:ℕ, ∫t:ℝ in Ioi 0, dampedTerm j t := hsum.symm
    _ = (1/4:ℝ) * ∑'j:ℕ, normalizedPrimeArchMoment j*(-1/4:ℝ)^j := by
      simp_rw [integral_dampedTerm, mul_assoc]
      rw [tsum_mul_left]
    _ = _ := by rw [moment_endpoint_real]; ring

/-- The endpoint area equals the literal Euler--Gamma/logarithmic arithmetic constant. -/
theorem integral_liEvenCrossActualClock_dampedEndpoint_specialValue :
    (∫t:ℝ in Ioi 0, Real.exp (-2*t)*liEvenCrossActualClockResponse t) =
      (2+Real.eulerMascheroniConstant-Real.log (4*Real.pi))/4 := by
  rw [integral_liEvenCrossActualClock_dampedEndpoint,
    xiEndpointCompletedCurvature_eq_eulerMascheroni_log]

/-- The signed endpoint area is strictly positive without a zero-location hypothesis. -/
theorem integral_liEvenCrossActualClock_dampedEndpoint_pos :
    0 < ∫t:ℝ in Ioi 0, Real.exp (-2*t)*liEvenCrossActualClockResponse t := by
  rw [integral_liEvenCrossActualClock_dampedEndpoint]
  exact div_pos xiEndpointCompletedCurvature_pos (by norm_num)
end
end RHTower
