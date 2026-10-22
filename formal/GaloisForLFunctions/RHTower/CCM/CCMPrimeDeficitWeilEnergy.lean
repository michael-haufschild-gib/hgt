import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitWeilFlux
import GaloisForLFunctions.RHTower.WeilLagFunctionDense

/-!
# The archimedean flux correction has bounded total energy

The actual outgoing flux and Weil lag differ by an exponentially decaying
term with a uniform squared-integral bound. The critical deficit energy is
therefore bounded by twice the actual lag energy plus an explicit constant.
This controls the entire correction; the prime correlation estimate for
the lag energy remains separate.
-/

noncomputable section
open MeasureTheory Filter Set

namespace RHTower

theorem abs_ccmPrimeDeficitOutgoing_sub_weilLag {t : ℝ} (ht : 0 < t) :
    |ccmPrimeDeficitOutgoing t - weilLagFunctionReal t| ≤
      Real.exp (-t / 2) * (|Real.log (2 * Real.pi)| + 1) := by
  have hexp : 1 ≤ Real.exp t := Real.one_le_exp_iff.mpr ht.le
  have hz0 := trivialZeroSeriesReal_nonneg hexp
  have hz1 := trivialZeroSeriesReal_le_one hexp
  rw [ccmPrimeDeficitOutgoing_eq_weilLag ht, add_sub_cancel_left,
    abs_mul, abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  calc
    |Real.log (2 * Real.pi) - trivialZeroSeriesReal (Real.exp t)| ≤
        |Real.log (2 * Real.pi)| + |trivialZeroSeriesReal (Real.exp t)| := abs_sub _ _
    _ ≤ |Real.log (2 * Real.pi)| + 1 := by rw [abs_of_nonneg hz0]; linarith only [hz1]

theorem ccmPrimeDeficitOutgoing_sub_weilLag_sq_le {t : ℝ} (ht : 0 < t) :
    (ccmPrimeDeficitOutgoing t - weilLagFunctionReal t) ^ 2 ≤
      (|Real.log (2 * Real.pi)| + 1) ^ 2 * Real.exp (-t) := by
  calc
    _ = |ccmPrimeDeficitOutgoing t - weilLagFunctionReal t| ^ 2 := (sq_abs _).symm
    _ ≤ (Real.exp (-t / 2) * (|Real.log (2 * Real.pi)| + 1)) ^ 2 := by
      gcongr
      exact abs_ccmPrimeDeficitOutgoing_sub_weilLag ht
    _ = _ := by
      rw [mul_pow, ← Real.exp_nat_mul]
      norm_num only [Nat.cast_ofNat]
      rw [show (2 : ℝ) * (-t / 2) = -t by ring]
      ring

/-- The entire archimedean correction has a bounded energy budget,
independently of the terminal time. -/
theorem integral_ccmPrimeDeficitOutgoing_sub_weilLag_sq_le {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, (ccmPrimeDeficitOutgoing t - weilLagFunctionReal t) ^ 2) ≤
      (|Real.log (2 * Real.pi)| + 1) ^ 2 := by
  have hc : Continuous (fun t => (ccmPrimeDeficitOutgoing t - weilLagFunctionReal t) ^ 2) :=
    (continuous_ccmPrimeDeficitOutgoing.sub continuous_weilLagFunctionReal).pow 2
  have hb : Continuous (fun t : ℝ => (|Real.log (2 * Real.pi)| + 1) ^ 2 * Real.exp (-t)) := by
    fun_prop
  calc
    _ ≤ ∫ t in (0 : ℝ)..T, (|Real.log (2 * Real.pi)| + 1) ^ 2 * Real.exp (-t) := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo hT (hc.intervalIntegrable 0 T)
        (hb.intervalIntegrable 0 T)
      intro t ht
      exact ccmPrimeDeficitOutgoing_sub_weilLag_sq_le ht.1
    _ ≤ _ := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_neg, integral_exp]
      simp only [neg_zero, Real.exp_zero]
      have he := mul_nonneg (sq_nonneg (|Real.log (2 * Real.pi)| + 1)) (Real.exp_pos (-T)).le
      nlinarith only [he]

/-- An unconditional comparison for the full signed deficit, with a fixed
allowance for the initial state and the archimedean correction. -/
theorem ccmPrimeDeficitCriticalEnergy_integral_le_weilLag_sq {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, ccmPrimeDeficitCriticalEnergy t) ≤
      2 * (∫ t in (0 : ℝ)..T, weilLagFunctionReal t ^ 2) +
        2 * (|Real.log (2 * Real.pi)| + 1) ^ 2 +
          (Real.eulerMascheroniConstant + 1) ^ 2 := by
  have ho : IntervalIntegrable (fun t => ccmPrimeDeficitOutgoing t ^ 2) volume 0 T :=
    (continuous_ccmPrimeDeficitOutgoing.pow 2).intervalIntegrable 0 T
  have hl : IntervalIntegrable (fun t => weilLagFunctionReal t ^ 2) volume 0 T :=
    (continuous_weilLagFunctionReal.pow 2).intervalIntegrable 0 T
  have hc : IntervalIntegrable
      (fun t => (ccmPrimeDeficitOutgoing t - weilLagFunctionReal t) ^ 2) volume 0 T :=
    ((continuous_ccmPrimeDeficitOutgoing.sub continuous_weilLagFunctionReal).pow 2).intervalIntegrable 0 T
  have hp : (∫ t in (0 : ℝ)..T, ccmPrimeDeficitOutgoing t ^ 2) ≤
      ∫ t in (0 : ℝ)..T, 2 * weilLagFunctionReal t ^ 2 +
        2 * (ccmPrimeDeficitOutgoing t - weilLagFunctionReal t) ^ 2 := by
    apply intervalIntegral.integral_mono hT ho ((hl.const_mul 2).add (hc.const_mul 2))
    intro t
    nlinarith only [sq_nonneg (ccmPrimeDeficitOutgoing t - 2 * weilLagFunctionReal t)]
  rw [intervalIntegral.integral_add (hl.const_mul 2) (hc.const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hp
  have he := ccmPrimeDeficitCriticalEnergy_integral_le_outgoing T
  have ha := integral_ccmPrimeDeficitOutgoing_sub_weilLag_sq_le hT
  linarith only [hp, he, ha]

end RHTower
