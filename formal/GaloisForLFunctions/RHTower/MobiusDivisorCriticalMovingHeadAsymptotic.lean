import GaloisForLFunctions.RHTower.MobiusDivisorCriticalPrimeTailError
import GaloisForLFunctions.RHTower.MobiusDivisorCriticalLogProfileTail
import GaloisForLFunctions.RHTower.MobiusDivisorCriticalCompensatedCauchy

/-!
# Pointwise asymptotic of the actual moving prime head

The literal finite prime sum, its signed source primitive, and the
quadratically negligible Mertens error give the negative coefficient at
every sufficiently large clock. The conclusion is not a Tauberian
inference from the earlier Mellin boundary jet.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace RHTower

private theorem movingHead_error_decomposition {t : ℝ} (ht : 0 < t) :
    Real.exp (-(3 / 2 : ℝ) * t) * criticalMovingPrimeHead (Real.exp t) =
      criticalAbelLogProfile t +
        (∫ s in (0 : ℝ)..t / 2, criticalAbelLogProfile s / (t - s)) +
        (∫ s in (0 : ℝ)..t / 2, criticalAbelLogVelocity s *
          (criticalMertensLogError (t - s) - criticalMertensLogError (t / 2))) := by
  have hb : (0 : ℝ) ≤ t / 2 := by linarith
  have hL : ContinuousOn (fun s : ℝ => Real.log (t - s) - Real.log (t / 2))
      (uIcc 0 (t / 2)) := by
    rw [uIcc_of_le hb]
    apply ((continuousOn_const.sub continuousOn_id).log _).sub continuousOn_const
    intro s hs
    change t - s ≠ 0
    linarith [hs.2]
  have hv : IntervalIntegrable criticalAbelLogVelocity volume 0 (t / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hb).mpr
      (integrableOn_criticalAbelLogVelocity.mono_set (fun _ hx => hx.1))
  have hlog : IntervalIntegrable (fun s => criticalAbelLogVelocity s *
      (Real.log (t - s) - Real.log (t / 2))) volume 0 (t / 2) :=
    hv.mul_continuousOn hL
  have herr : (∫ s in (0 : ℝ)..t / 2, criticalAbelLogVelocity s *
      (criticalMertensLogError (t - s) - criticalMertensLogError (t / 2))) =
      (∑ p ∈ criticalLogLatePrimes t, criticalAbelLogProfile (t - Real.log p) / p) -
        ∫ s in (0 : ℝ)..t / 2, criticalAbelLogProfile s / (t - s) := by
    calc
      _ = ∫ s in (0 : ℝ)..t / 2,
          (criticalAbelLogVelocity s *
            (Sieve.mertensS ⌊Real.exp (t - s)⌋₊ - Sieve.mertensS ⌊Real.exp (t / 2)⌋₊) -
          criticalAbelLogVelocity s * (Real.log (t - s) - Real.log (t / 2))) := by
        apply intervalIntegral.integral_congr
        intro s _
        dsimp [criticalMertensLogError]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub (intervalIntegrable_criticalLogLatePrimes_mertens t ht.le)
          hlog, ← criticalLogLatePrimes_profile_eq_mertens_integral ht.le,
          criticalAbelLogVelocity_log_increment ht]
  rw [criticalMovingPrimeHead_exp_eq_log_late_sum ht, herr]
  ring

/-- Exact second-order limit on the actual logarithmic clock. -/
theorem tendsto_criticalMovingPrimeHead_log_scaled :
    Tendsto (fun t : ℝ => t ^ (2 : ℕ) *
      (Real.exp (-(3 / 2 : ℝ) * t) * criticalMovingPrimeHead (Real.exp t)))
      atTop (𝓝 (-(divisorHarmonicBoundary / 3))) := by
  have h := (tendsto_criticalAbelLogProfile_quadratic_zero.add
    tendsto_criticalAbelLogProfile_cauchy_main).add tendsto_criticalPrimeTail_scaled_error_zero
  simp only [zero_add, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [movingHead_error_decomposition ht]
  ring

/-- The moving head has its negative asymptotic at every real cutoff,
with the exact coefficient supplied by the source's first signed moment. -/
theorem tendsto_criticalMovingPrimeHead_pointwise_scaled :
    Tendsto (fun x : ℝ => criticalMovingPrimeHead x * Real.log x ^ (2 : ℕ) /
      x ^ (3 / 2 : ℝ)) atTop (𝓝 (-(divisorHarmonicBoundary / 3))) := by
  have h := tendsto_criticalMovingPrimeHead_log_scaled.comp Real.tendsto_log_atTop
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  dsimp only [Function.comp_apply]
  rw [Real.exp_log hx0, Real.rpow_def_of_pos hx0,
    show -(3 / 2 : ℝ) * Real.log x = -(Real.log x * (3 / 2 : ℝ)) by ring,
    Real.exp_neg]
  ring

end RHTower
