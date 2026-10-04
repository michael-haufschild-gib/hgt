import GaloisForLFunctions.RHTower.RoutePNativeSignedPairComparison

/-! # Native biased mean and complete covariance on the same moving cutoff -/

open Finset MeasureTheory

namespace RHTower.RoutePWindow

noncomputable def nativeBiasedMean (t : ℝ) : ℝ :=
  head (clockPrimes t) (fun p => Real.log (p : ℝ)) (meanGain (primeGain 0))
    (unitClockSource 0) t

private theorem prime_head_damping (P : Finset Nat.Primes) (ε t : ℝ) :
    head P (fun p => Real.log (p : ℝ)) (meanGain (primeGain ε)) (unitClockSource ε) t =
      damping ε t*head P (fun p => Real.log (p : ℝ))
        (meanGain (primeGain 0)) (unitClockSource 0) t := by
  have hb : meanGain (primeGain ε) = fun p : Nat.Primes =>
      damping ε (Real.log (p : ℝ))*meanGain (primeGain 0) p := by
    funext p
    unfold meanGain
    rw [primeGain_eq_damping]
    ring
  have hf : unitClockSource ε = fun t => damping ε t*unitClockSource 0 t := by
    funext t
    simp [unitClockSource, damping]
  rw [hb, hf, head_damping]

theorem nativeBiasedMean_stable {t T : ℝ} (ht : t ≤ T) :
    head (clockPrimes T) (fun p => Real.log (p : ℝ)) (meanGain (primeGain 0))
      (unitClockSource 0) t = nativeBiasedMean t := by
  have ha (p : Nat.Primes) : 0 ≤ Real.log (p : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast p.property.one_lt.le
  apply head_eq_of_extra_beyond (clockPrimes t) (clockPrimes T) _ _ _
    ha (fun _ hs => unitClockSource_zero hs) (clockPrimes_mono ht)
  intro p _ hp
  apply (Real.le_log_iff_exp_le (by exact_mod_cast p.property.pos)).mpr
  exact (lt_of_not_ge (fun h => hp ((mem_clockPrimes p t).mpr h))).le

private theorem biased_integral_eq {ε T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T,
      (head (clockPrimes T) (fun p => Real.log (p : ℝ)) (meanGain (primeGain ε))
        (unitClockSource ε) t)^2) =
      ∫ t in (0 : ℝ)..T, Real.exp (-ε*t)*(nativeBiasedMean t)^2 := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le hT] at ht
  dsimp only
  rw [prime_head_damping, nativeBiasedMean_stable ht.2, mul_pow, damping_sq]

private theorem original_integral_eq {ε T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T,
      (head (clockPrimes T) (fun p => Real.log (p : ℝ)) (primeGain ε)
        (unitClockSource ε) t)^2) =
      ∫ t in (0 : ℝ)..T,
        Real.exp (-ε*t)*(mobiusDivisorFullHead (Real.exp t)/Real.exp t)^2 := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le hT] at ht
  dsimp only
  rw [head_primeGain_eq_clock, clockPrimes_head_eq_full ht.2, mul_pow, damping_sq]

private theorem covariance_integral_eq {ε T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T,
      covariance (clockPrimes T) (fun p => Real.log (p : ℝ)) (meanGain (primeGain ε))
        (noiseGain (primeGain ε)) (unitClockSource ε) t) =
      ∫ t in (0 : ℝ)..T, Real.exp (-ε*t)*nativeSignedPairCovariance t := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le hT] at ht
  dsimp only
  rw [prime_covariance_damping, covariance_clockPrimes_stable ht.2,
    nativeCofactorCovariance_eq_signedPair]

/-- The complete native covariance and its own mean have uniformly
comparable energies, on the identical physical moving cutoff. -/
theorem native_covariance_mean_comparison {ε T : ℝ} (hε : 0 ≤ ε) (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, Real.exp (-ε*t)*(nativeBiasedMean t)^2) ≤
      (∫ t in (0 : ℝ)..T, Real.exp (-ε*t)*nativeSignedPairCovariance t) ∧
    (∫ t in (0 : ℝ)..T, Real.exp (-ε*t)*nativeSignedPairCovariance t) ≤
      covarianceBudget*(∫ t in (0 : ℝ)..T, Real.exp (-ε*t)*(nativeBiasedMean t)^2) := by
  have hq0 := fun p => (primeGain_bounds hε p).1
  have hq := fun p => (primeGain_bounds hε p).2
  have hlow := integral_head_sq_le_covariance (clockPrimes T)
    (fun p => Real.log (p : ℝ)) (meanGain (primeGain ε)) (noiseGain (primeGain ε))
    (fun p => (prime_gain_bounds (primeGain ε) p (hq0 p) (hq p)).2.2.1)
    _ (continuous_unitClockSource ε) hT
  have hhigh := integral_prime_covariance_le (clockPrimes T) (primeGain ε) hq0 hq _
    (continuous_unitClockSource ε) (fun _ ht => unitClockSource_zero ht) hT
  rw [biased_integral_eq hT, covariance_integral_eq hT] at hlow hhigh
  exact ⟨hlow, hhigh⟩

/-- Removing the literal prime bias costs one absolute energy factor
in either direction, uniformly in the native window and damping. -/
theorem native_bias_comparison {ε T : ℝ} (hε : 0 ≤ ε) (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T,
      Real.exp (-ε*t)*(mobiusDivisorFullHead (Real.exp t)/Real.exp t)^2) ≤
      biasBudget*(∫ t in (0 : ℝ)..T, Real.exp (-ε*t)*(nativeBiasedMean t)^2) ∧
    (∫ t in (0 : ℝ)..T, Real.exp (-ε*t)*(nativeBiasedMean t)^2) ≤
      biasBudget*(∫ t in (0 : ℝ)..T,
        Real.exp (-ε*t)*(mobiusDivisorFullHead (Real.exp t)/Real.exp t)^2) := by
  have h := integral_prime_bias_comparison (clockPrimes T) (primeGain ε)
    (fun p => (primeGain_bounds hε p).1) (fun p => (primeGain_bounds hε p).2)
    _ (continuous_unitClockSource ε) (fun _ ht => unitClockSource_zero ht) hT
  rwa [biased_integral_eq hT, original_integral_eq hT] at h

end RHTower.RoutePWindow
