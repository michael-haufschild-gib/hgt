import GaloisForLFunctions.RHTower.RoutePNativeCovarianceWindow
import GaloisForLFunctions.RHTower.RoutePPrimePairExpansion

/-!
# Native covariance comparison with every signed pair retained

The channels are the literal terms of the causal prime expansion of
the original full Möbius divisor head. Their common prime factors
are retained; only the symmetric difference contributes a bias.
-/

open Finset MeasureTheory
open scoped symmDiff

namespace RHTower.RoutePWindow

noncomputable def nativePrimeChannel (S : Finset Nat.Primes) (t : ℝ) : ℝ :=
  (∏ p ∈ S, -primeGain 0 p)*unitClockSource 0 (t-∑ p ∈ S, Real.log (p : ℝ))

/-- The complete channel sum is exactly the original native source. -/
theorem sum_nativePrimeChannel (t : ℝ) :
    (∑ S ∈ (clockPrimes t).powerset, nativePrimeChannel S t) =
      mobiusDivisorFullHead (Real.exp t)/Real.exp t := by
  change head (clockPrimes t) (fun p => Real.log (p : ℝ)) (primeGain 0)
    (unitClockSource 0) t = _
  rw [head_primeGain_eq_clock, clockPrimes_head_eq_full le_rfl]
  simp [damping]

/-- Products beyond the original physical cutoff contribute exactly zero. -/
theorem nativePrimeChannel_zero {S : Finset Nat.Primes} {t : ℝ}
    (hS : t ≤ ∑ p ∈ S, Real.log (p : ℝ)) : nativePrimeChannel S t = 0 := by
  unfold nativePrimeChannel
  rw [unitClockSource_zero (sub_nonpos.mpr hS), mul_zero]

noncomputable def nativeSignedPairCovariance (t : ℝ) : ℝ :=
  ∑ S ∈ (clockPrimes t).powerset, ∑ T ∈ (clockPrimes t).powerset,
    (∏ p ∈ S ∆ T, (1-1/(p : ℝ)))*nativePrimeChannel S t*nativePrimeChannel T t

/-- Complete signed-pair expansion of the native cofactor covariance. -/
theorem nativeCofactorCovariance_eq_signedPair (t : ℝ) :
    nativeCofactorCovariance t = nativeSignedPairCovariance t := by
  unfold nativeCofactorCovariance nativeSignedPairCovariance
  rw [covariance_eq_sourcePair]
  apply sum_congr rfl
  intro S hS
  apply sum_congr rfl
  intro T hT
  have hk := pairKernel_bias (clockPrimes t) S T (fun p : Nat.Primes => 1-1/(p : ℝ))
    (primeGain 0) (mem_powerset.mp hS) (mem_powerset.mp hT)
  change pairKernel (clockPrimes t) (meanGain (primeGain 0)) (noiseGain (primeGain 0)) S T =
    (∏ p ∈ S, -primeGain 0 p)*(∏ p ∈ T, -primeGain 0 p)*
      (∏ p ∈ S ∆ T, (1-1/(p : ℝ))) at hk
  rw [hk]
  unfold nativePrimeChannel
  ring

/-- The additional complete covariance cost is uniformly paid relative
to the literal native head, for every nonnegative damping and cutoff.
No cancellation or global square-admission premise occurs. -/
theorem native_signed_pair_comparison {ε T : ℝ} (hε : 0 ≤ ε) (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, Real.exp (-ε*t)*nativeSignedPairCovariance t) ≤
      (covarianceBudget*biasBudget)*(∫ t in (0 : ℝ)..T,
        Real.exp (-ε*t)*(mobiusDivisorFullHead (Real.exp t)/Real.exp t)^2) ∧
    (∫ t in (0 : ℝ)..T,
      Real.exp (-ε*t)*(mobiusDivisorFullHead (Real.exp t)/Real.exp t)^2) ≤
      biasBudget*(∫ t in (0 : ℝ)..T, Real.exp (-ε*t)*nativeSignedPairCovariance t) := by
  simpa only [nativeCofactorCovariance_eq_signedPair] using
    native_cofactor_covariance_comparison hε hT

end RHTower.RoutePWindow
