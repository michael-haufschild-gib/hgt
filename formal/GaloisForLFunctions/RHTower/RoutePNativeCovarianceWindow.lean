import GaloisForLFunctions.RHTower.RoutePCovarianceDamping
import GaloisForLFunctions.RHTower.RoutePCausalPrimeHorizon

/-!
# Covariance comparison on the native moving prime horizon

Every source at clock `t` uses exactly the primes up to `exp t`.
The proof freezes that core only on one finite integration window,
where equality follows from causal clipping. All constants are uniform.
The covariance is presently in its cofactor-square form.
-/

open Finset MeasureTheory

namespace RHTower.RoutePWindow

private def primeWindowEmbedding : {n : ℕ // n.Prime} ↪ Nat.Primes where
  toFun p := ⟨p.val, p.property⟩
  inj' := fun _ _ h => Subtype.ext (congrArg (fun p : Nat.Primes => (p : ℕ)) h)

noncomputable def clockPrimes (t : ℝ) : Finset Nat.Primes :=
  ((Finset.range (⌊Real.exp t⌋₊+1)).subtype Nat.Prime).map primeWindowEmbedding

theorem mem_clockPrimes (p : Nat.Primes) (t : ℝ) :
    p ∈ clockPrimes t ↔ (p : ℝ) ≤ Real.exp t := by
  rw [clockPrimes, mem_map]
  constructor
  · rintro ⟨r, hr, hrp⟩
    have hr' : r.val ≤ ⌊Real.exp t⌋₊ := by
      simpa only [mem_subtype, mem_range, Nat.lt_succ_iff] using hr
    have he : r.val = (p : ℕ) := congrArg (fun p : Nat.Primes => (p : ℕ)) hrp
    rw [← he]
    exact (Nat.le_floor_iff (Real.exp_pos t).le).mp hr'
  · intro hp
    refine ⟨⟨(p : ℕ), p.property⟩, ?_, ?_⟩
    · rw [mem_subtype, mem_range, Nat.lt_succ_iff]
      exact Nat.le_floor hp
    · exact Subtype.ext rfl

theorem clockPrimes_mono {s t : ℝ} (hst : s ≤ t) : clockPrimes s ⊆ clockPrimes t := by
  intro p hp
  exact (mem_clockPrimes p t).mpr (((mem_clockPrimes p s).mp hp).trans
    (Real.exp_le_exp.mpr hst))

private theorem primeDelay_nonneg (p : Nat.Primes) : 0 ≤ Real.log (p : ℝ) := by
  apply Real.log_nonneg
  exact_mod_cast p.property.one_lt.le

private theorem beyond_clock {p : Nat.Primes} {t : ℝ} (hp : p ∉ clockPrimes t) :
    t ≤ Real.log (p : ℝ) := by
  apply (Real.le_log_iff_exp_le (by exact_mod_cast p.property.pos)).mpr
  exact (lt_of_not_ge (fun h => hp ((mem_clockPrimes p t).mpr h))).le

/-- Literal agreement with the original full head throughout a finite window. -/
theorem clockPrimes_head_eq_full {t T : ℝ} (ht : t ≤ T) :
    mobiusDivisorCriticalClockHead
      ((clockPrimes T).image (fun p : Nat.Primes => (p : ℕ))) t =
        mobiusDivisorFullHead (Real.exp t)/Real.exp t := by
  unfold mobiusDivisorCriticalClockHead
  congr 1
  apply mobiusDivisorContinuousHead_eq_fullHead
    ((clockPrimes T).image (fun p : Nat.Primes => (p : ℕ)))
  · intro n hn
    obtain ⟨p, _, rfl⟩ := mem_image.mp hn
    exact p.property
  · intro n hn hnt
    exact mem_image.mpr ⟨⟨n, hn⟩, (mem_clockPrimes ⟨n, hn⟩ T).mpr hnt, rfl⟩
  · exact Real.exp_le_exp.mpr ht

noncomputable def nativeCofactorCovariance (t : ℝ) : ℝ :=
  covariance (clockPrimes t) (fun p => Real.log (p : ℝ))
    (meanGain (primeGain 0)) (noiseGain (primeGain 0)) (unitClockSource 0) t

theorem covariance_clockPrimes_stable {t T : ℝ} (ht : t ≤ T) :
    covariance (clockPrimes T) (fun p => Real.log (p : ℝ))
      (meanGain (primeGain 0)) (noiseGain (primeGain 0)) (unitClockSource 0) t =
        nativeCofactorCovariance t := by
  exact covariance_eq_of_extra_beyond (clockPrimes t) (clockPrimes T) _ _ _ _
    primeDelay_nonneg (fun _ hs => unitClockSource_zero hs) (clockPrimes_mono ht)
    (fun _ _ hp => beyond_clock hp)

/-- Uniform two-sided comparison with the literal full native source,
on every finite window and for every nonnegative damping. This imposes
no premise on the growth of either energy as the window increases. -/
theorem native_cofactor_covariance_comparison {ε T : ℝ} (hε : 0 ≤ ε) (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, Real.exp (-ε*t)*nativeCofactorCovariance t) ≤
      (covarianceBudget*biasBudget)*(∫ t in (0 : ℝ)..T,
        Real.exp (-ε*t)*(mobiusDivisorFullHead (Real.exp t)/Real.exp t)^2) ∧
    (∫ t in (0 : ℝ)..T,
      Real.exp (-ε*t)*(mobiusDivisorFullHead (Real.exp t)/Real.exp t)^2) ≤
      biasBudget*(∫ t in (0 : ℝ)..T, Real.exp (-ε*t)*nativeCofactorCovariance t) := by
  have hcov : (∫ t in (0 : ℝ)..T,
      covariance (clockPrimes T) (fun p => Real.log (p : ℝ))
        (meanGain (primeGain ε)) (noiseGain (primeGain ε)) (unitClockSource ε) t) =
      ∫ t in (0 : ℝ)..T, Real.exp (-ε*t)*nativeCofactorCovariance t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    rw [prime_covariance_damping, covariance_clockPrimes_stable ht.2]
  have hhead : (∫ t in (0 : ℝ)..T,
      (damping ε t*mobiusDivisorCriticalClockHead
        ((clockPrimes T).image (fun p : Nat.Primes => (p : ℕ))) t)^2) =
      ∫ t in (0 : ℝ)..T,
        Real.exp (-ε*t)*(mobiusDivisorFullHead (Real.exp t)/Real.exp t)^2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    dsimp only
    rw [clockPrimes_head_eq_full ht.2, mul_pow, damping_sq]
  have h := finite_native_covariance_comparison (clockPrimes T) hε hT
  rwa [hcov, hhead] at h

end RHTower.RoutePWindow
