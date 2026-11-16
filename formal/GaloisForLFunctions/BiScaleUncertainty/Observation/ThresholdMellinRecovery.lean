import GaloisForLFunctions.RHTower.Deninger.DeningerFloquetPoissonSample

/-!
# Stable threshold inversion of Poisson--Mellin samples

The squared threshold used for multiplicative measurement error bounds
inverse gain by the sample size. Applied to the existing Poisson--Mellin
factorization, it recovers exactly the retained critical-line Mellin values.
The full error splits into amplified noise and discarded source values.
-/

open RHTower
open scoped SchwartzMap

noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.Observation

/-- Reciprocal retained only when its squared gain is at most `N + 1`. -/
def thresholdInverse (N : ℕ) (z : ℂ) : ℂ :=
  if 1 ≤ (N + 1 : ℝ) * ‖z‖ ^ 2 then z⁻¹ else 0

theorem thresholdInverse_zero (N : ℕ) : thresholdInverse N 0 = 0 := by
  simp [thresholdInverse]

/-- Uniform squared amplification bound, including at zero multipliers. -/
theorem thresholdInverse_norm_sq (N : ℕ) (z : ℂ) :
    ‖thresholdInverse N z‖ ^ 2 ≤ (N + 1 : ℝ) := by
  unfold thresholdInverse
  split_ifs with h
  · have hz : ‖z‖ ≠ 0 := by intro hz; norm_num [hz] at h
    rw [norm_inv, inv_pow]
    have hh := mul_le_mul_of_nonneg_right h (inv_nonneg.mpr (sq_nonneg ‖z‖))
    simpa only [one_mul, mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hz), mul_one] using hh
  · simp only [norm_zero, zero_pow (by omega : 2 ≠ 0)]
    positivity

theorem thresholdInverse_mul (N : ℕ) (z u : ℂ) :
    thresholdInverse N z * (z * u) =
      if 1 ≤ (N + 1 : ℝ) * ‖z‖ ^ 2 then u else 0 := by
  unfold thresholdInverse
  split_ifs with h
  · have hz : z ≠ 0 := by intro hz; norm_num [hz] at h
    rw [← mul_assoc, inv_mul_cancel₀ hz, one_mul]
  · exact zero_mul _

/-- Exact error: inverse-amplified noise on retained modes, source bias elsewhere. -/
theorem thresholdInverse_noisy_error (N : ℕ) (z u e : ℂ) :
    ‖thresholdInverse N z * (z * u + e) - u‖ ^ 2 =
      if 1 ≤ (N + 1 : ℝ) * ‖z‖ ^ 2 then ‖e‖ ^ 2 / ‖z‖ ^ 2 else ‖u‖ ^ 2 := by
  rw [mul_add, thresholdInverse_mul]
  by_cases h : 1 ≤ (N + 1 : ℝ) * ‖z‖ ^ 2
  · rw [if_pos h, if_pos h]
    have he : u + thresholdInverse N z * e - u = thresholdInverse N z * e := by ring
    rw [he, thresholdInverse, if_pos h, norm_mul, norm_inv, mul_pow, inv_pow]
    ring
  · simp only [if_neg h, thresholdInverse, zero_mul, zero_add, zero_sub, norm_neg]

theorem thresholdInverse_noisy_bound (N : ℕ) (z u e : ℂ) :
    ‖thresholdInverse N z * (z * u + e) - u‖ ^ 2 ≤
      (N + 1 : ℝ) * ‖e‖ ^ 2 +
        if 1 ≤ (N + 1 : ℝ) * ‖z‖ ^ 2 then 0 else ‖u‖ ^ 2 := by
  by_cases h : 1 ≤ (N + 1 : ℝ) * ‖z‖ ^ 2
  · rw [mul_add, thresholdInverse_mul, if_pos h, if_pos h, add_zero]
    have he : u + thresholdInverse N z * e - u = thresholdInverse N z * e := by ring
    rw [he, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (thresholdInverse_norm_sq N z) (sq_nonneg _)
  · rw [thresholdInverse_noisy_error, if_neg h, if_neg h]
    exact le_add_of_nonneg_left (by positivity)

/-- Threshold reconstruction from a noisy sample of the actual Poisson source. -/
def thresholdFloquetRecovery (N : ℕ) (f : DeningerMeyerCap) (ξ : ℝ) (e : ℂ) : ℂ :=
  thresholdInverse N (riemannZeta (deningerCriticalLine ξ)) *
    (deningerFloquetSample (deningerPoissonSource f) ξ + e)

/-- Noiseless reconstruction equals the source Mellin transform on the retained set. -/
theorem thresholdFloquetRecovery_exact (N : ℕ) (f : DeningerMeyerCap) (ξ : ℝ) :
    thresholdFloquetRecovery N f ξ 0 =
      if 1 ≤ (N + 1 : ℝ) * ‖riemannZeta (deningerCriticalLine ξ)‖ ^ 2 then
        mellin ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (deningerCriticalLine ξ) else 0 := by
  rw [thresholdFloquetRecovery, add_zero, deningerFloquetSample_poissonSource,
    thresholdInverse_mul]

/-- The sample-size threshold gives an exact bias/noise alternative at every frequency. -/
theorem thresholdFloquetRecovery_error (N : ℕ) (f : DeningerMeyerCap) (ξ : ℝ) (e : ℂ) :
    ‖thresholdFloquetRecovery N f ξ e -
        mellin ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (deningerCriticalLine ξ)‖ ^ 2 =
      if 1 ≤ (N + 1 : ℝ) * ‖riemannZeta (deningerCriticalLine ξ)‖ ^ 2 then
        ‖e‖ ^ 2 / ‖riemannZeta (deningerCriticalLine ξ)‖ ^ 2 else
        ‖mellin ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (deningerCriticalLine ξ)‖ ^ 2 := by
  rw [thresholdFloquetRecovery, deningerFloquetSample_poissonSource,
    thresholdInverse_noisy_error]

/-- A frequency-uniform stability estimate with the exact discarded-source term. -/
theorem thresholdFloquetRecovery_bound (N : ℕ) (f : DeningerMeyerCap) (ξ : ℝ) (e : ℂ) :
    ‖thresholdFloquetRecovery N f ξ e -
        mellin ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (deningerCriticalLine ξ)‖ ^ 2 ≤
      (N + 1 : ℝ) * ‖e‖ ^ 2 +
        if 1 ≤ (N + 1 : ℝ) * ‖riemannZeta (deningerCriticalLine ξ)‖ ^ 2 then 0 else
          ‖mellin ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (deningerCriticalLine ξ)‖ ^ 2 := by
  rw [thresholdFloquetRecovery, deningerFloquetSample_poissonSource]
  exact thresholdInverse_noisy_bound N _ _ e

/-- Inversion using an estimated multiplier rather than the exact zeta value. -/
def calibratedFloquetRecovery (N : ℕ) (z : ℂ) (f : DeningerMeyerCap) (ξ : ℝ) (e : ℂ) : ℂ :=
  thresholdInverse N z * (deningerFloquetSample (deningerPoissonSource f) ξ + e)

/-- Calibration error and observation noise enter through one exact effective-noise term. -/
theorem calibratedFloquetRecovery_error (N : ℕ) (z : ℂ) (f : DeningerMeyerCap)
    (ξ : ℝ) (e : ℂ) :
    ‖calibratedFloquetRecovery N z f ξ e -
        mellin ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (deningerCriticalLine ξ)‖ ^ 2 =
      if 1 ≤ (N + 1 : ℝ) * ‖z‖ ^ 2 then
        ‖(riemannZeta (deningerCriticalLine ξ) - z) *
          mellin ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (deningerCriticalLine ξ) + e‖ ^ 2 / ‖z‖ ^ 2
      else ‖mellin ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (deningerCriticalLine ξ)‖ ^ 2 := by
  rw [calibratedFloquetRecovery, deningerFloquetSample_poissonSource]
  have he (u : ℂ) : riemannZeta (deningerCriticalLine ξ) * u + e =
      z * u + ((riemannZeta (deningerCriticalLine ξ) - z) * u + e) := by ring
  rw [he, thresholdInverse_noisy_error]

/-- Stability under simultaneous calibration and observation errors. -/
theorem calibratedFloquetRecovery_bound (N : ℕ) (z : ℂ) (f : DeningerMeyerCap)
    (ξ : ℝ) (e : ℂ) :
    ‖calibratedFloquetRecovery N z f ξ e -
        mellin ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (deningerCriticalLine ξ)‖ ^ 2 ≤
      (N + 1 : ℝ) * ‖(riemannZeta (deningerCriticalLine ξ) - z) *
        mellin ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (deningerCriticalLine ξ) + e‖ ^ 2 +
        if 1 ≤ (N + 1 : ℝ) * ‖z‖ ^ 2 then 0 else
          ‖mellin ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (deningerCriticalLine ξ)‖ ^ 2 := by
  rw [calibratedFloquetRecovery, deningerFloquetSample_poissonSource]
  have he (u : ℂ) : riemannZeta (deningerCriticalLine ξ) * u + e =
      z * u + ((riemannZeta (deningerCriticalLine ξ) - z) * u + e) := by ring
  rw [he]
  exact thresholdInverse_noisy_bound N _ _ _

#print axioms thresholdInverse_norm_sq
#print axioms thresholdFloquetRecovery_exact
#print axioms thresholdFloquetRecovery_error
#print axioms thresholdFloquetRecovery_bound
#print axioms calibratedFloquetRecovery_error
#print axioms calibratedFloquetRecovery_bound

end GaloisForLFunctions.BiScaleUncertainty.Observation

