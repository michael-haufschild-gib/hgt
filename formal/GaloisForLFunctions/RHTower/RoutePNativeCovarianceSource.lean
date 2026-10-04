import GaloisForLFunctions.RHTower.RoutePFiniteBiasTransfer
import GaloisForLFunctions.RHTower.MobiusDivisorCriticalClockProductTransport
import GaloisForLFunctions.RHTower.MobiusDivisorUniformLocalRegularity
import GaloisForLFunctions.RHTower.MobiusDivisorFullHeadCompletion

/-!
# Identification with the actual Möbius divisor source

The finite causal product is exactly the repository's physical source,
including its original clipping. Damping is conjugated through each
prime, rather than imposed as an unproved energy admission.
-/

open Finset MeasureTheory

namespace RHTower.RoutePWindow

noncomputable def damping (ε t : ℝ) : ℝ := Real.exp (-ε*t/2)

noncomputable def primeGain (ε : ℝ) (p : Nat.Primes) : ℝ :=
  damping ε (Real.log (p : ℝ))/Real.sqrt (p : ℝ)

noncomputable def unitClockSource (ε t : ℝ) : ℝ :=
  damping ε t*mobiusDivisorCriticalClockHead ∅ t

theorem damping_delay (ε t a : ℝ) : damping ε a*damping ε (t-a) = damping ε t := by
  unfold damping
  rw [← Real.exp_add]
  congr 1
  ring

theorem primeGain_bounds {ε : ℝ} (hε : 0 ≤ ε) (p : Nat.Primes) :
    0 ≤ primeGain ε p ∧ primeGain ε p ≤ 1/Real.sqrt (p : ℝ) := by
  have hl : 0 ≤ Real.log (p : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast p.property.one_lt.le
  have he : damping ε (Real.log (p : ℝ)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hε) hl) (by norm_num)
  exact ⟨div_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _),
    div_le_div_of_nonneg_right he (Real.sqrt_nonneg _)⟩

theorem continuous_unitClockSource (ε : ℝ) : Continuous (unitClockSource ε) := by
  have hU : Continuous divisorContinuousUnitHead := by
    have hL : LipschitzWith 12 divisorContinuousUnitHead :=
      lipschitzWith_iff_dist_le_mul.mpr (fun x y => by
        simpa only [Real.dist_eq, NNReal.coe_ofNat] using abs_divisorContinuousUnitHead_sub_le x y)
    exact hL.continuous
  have hbase : Continuous (mobiusDivisorCriticalClockHead ∅) := by
    have he : mobiusDivisorCriticalClockHead ∅ =
        fun t => divisorContinuousUnitHead (Real.exp t)/Real.exp t := by
      funext t
      simp [mobiusDivisorCriticalClockHead, mobiusDivisorContinuousHead]
    rw [he]
    exact (hU.comp Real.continuous_exp).div Real.continuous_exp (fun t => (Real.exp_pos t).ne')
  exact (Real.continuous_exp.comp
    ((continuous_const.mul continuous_id).div_const 2)).mul hbase

theorem unitClockSource_zero {ε t : ℝ} (ht : t ≤ 0) : unitClockSource ε t = 0 := by
  unfold unitClockSource mobiusDivisorCriticalClockHead
  rw [mobiusDivisorContinuousHead_eq_zero ∅ (Real.exp_le_one_iff.mpr ht)]
  simp

/-- Exact finite-core identification, valid for every real damping. -/
theorem head_primeGain_eq_clock (P : Finset Nat.Primes) (ε t : ℝ) :
    head P (fun p => Real.log (p : ℝ)) (primeGain ε) (unitClockSource ε) t =
      damping ε t*mobiusDivisorCriticalClockHead (P.image (fun p : Nat.Primes => (p : ℕ))) t := by
  induction P using Finset.induction_on generalizing t with
  | empty => simp [unitClockSource]
  | @insert p P hp ih =>
    rw [head_insert P _ _ _ hp,
      mobiusDivisorCriticalClockHead_prime_delay, erase_eq_of_notMem hp, ih]
    have hprev := ih (t := t-Real.log (p : ℝ))
    rw [hprev]
    have he := damping_delay ε t (Real.log (p : ℝ))
    dsimp [primeGain]
    calc
      _ = damping ε t*mobiusDivisorCriticalClockHead (P.image (fun p : Nat.Primes => (p : ℕ))) t -
          (damping ε (Real.log (p : ℝ))*damping ε (t-Real.log (p : ℝ)))*
            mobiusDivisorCriticalClockHead (P.image (fun p : Nat.Primes => (p : ℕ)))
              (t-Real.log (p : ℝ))/Real.sqrt (p : ℝ) := by ring
      _ = _ := by rw [he]; ring

/-- The covariance is bounded by the actual finite-core native head.
The only energy remaining on the right is the original source energy. -/
theorem finite_native_covariance_comparison (P : Finset Nat.Primes)
    {ε T : ℝ} (hε : 0 ≤ ε) (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T,
      covariance P (fun p => Real.log (p : ℝ))
        (meanGain (primeGain ε)) (noiseGain (primeGain ε)) (unitClockSource ε) t) ≤
      (covarianceBudget*biasBudget)*(∫ t in (0 : ℝ)..T,
        (damping ε t*mobiusDivisorCriticalClockHead
          (P.image (fun p : Nat.Primes => (p : ℕ))) t)^2) ∧
    (∫ t in (0 : ℝ)..T, (damping ε t*mobiusDivisorCriticalClockHead
      (P.image (fun p : Nat.Primes => (p : ℕ))) t)^2) ≤
      biasBudget*(∫ t in (0 : ℝ)..T,
        covariance P (fun p => Real.log (p : ℝ))
          (meanGain (primeGain ε)) (noiseGain (primeGain ε)) (unitClockSource ε) t) := by
  have hq0 := fun p => (primeGain_bounds hε p).1
  have hq := fun p => (primeGain_bounds hε p).2
  have hf := continuous_unitClockSource ε
  have hz : ∀ t ≤ 0, unitClockSource ε t = 0 := fun _ ht => unitClockSource_zero ht
  have hcov := integral_prime_covariance_le P (primeGain ε) hq0 hq _ hf hz hT
  have hb := integral_prime_bias_comparison P (primeGain ε) hq0 hq _ hf hz hT
  simp_rw [head_primeGain_eq_clock] at hb
  have hlow := integral_head_sq_le_covariance P (fun p => Real.log (p : ℝ))
    (meanGain (primeGain ε)) (noiseGain (primeGain ε))
    (fun p => (prime_gain_bounds (primeGain ε) p (hq0 p) (hq p)).2.2.1)
    _ hf hT
  constructor
  · exact hcov.trans (by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hb.2 covarianceBudget_pos.le)
  · exact hb.1.trans (mul_le_mul_of_nonneg_left hlow biasBudget_pos.le)

end RHTower.RoutePWindow
