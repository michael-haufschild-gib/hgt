import GaloisForLFunctions.RHTower.Sieve.MertensFirst
import GaloisForLFunctions.RHTower.PrimeDepthBVWoldSourceDaggerAtlasTransition
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# The prime-depth BV–Wold Schatten wall

For a prime `p`, a depth `e` and a scalar `a` put

    c_e(p) = (1 − 1/p)³ · log p / p^e,     w_{a,e} = a · c_e,     r(p) = 2 log p / p².

The all-prime anomaly is summable **exactly from depth two onward**, and adding the trace-class
remainder does not move the threshold:

    Summable c_e        ↔ 2 ≤ e,
    Summable w_{a,e}    ↔ a = 0 ∨ 2 ≤ e,
    Summable (w_{a,e}+r)↔ a = 0 ∨ 2 ≤ e.

Both directions are elementary once the Euler factor is trapped between `1/8` and `1`: above the
wall `c_e(p) ≤ log p/p²`, which is summable because `log p ≤ 2√p`; below it
`c_e(p) ≥ (log 2/8)·(1/p)`, and the reciprocals of the primes diverge.

The consequence is a classification, not an estimate: depth `0` and `1` carry a globally
non-summable orientation anomaly, while from depth `2` the *same* nonzero anomaly is trace-class.
No fixed trace-class correction can hide the depth-one anomaly.
-/

namespace RHTower

open Filter

/-- The BV–Wold depth-`e` prime coefficient. -/
noncomputable def woldCoeff (e : ℕ) (p : Nat.Primes) : ℝ :=
  (1 - 1 / ((p : ℕ) : ℝ)) ^ 3 * Real.log ((p : ℕ) : ℝ) / ((p : ℕ) : ℝ) ^ e

/-- The physical/unit-double trace-class remainder. -/
noncomputable def woldRemainder (p : Nat.Primes) : ℝ :=
  2 * Real.log ((p : ℕ) : ℝ) / ((p : ℕ) : ℝ) ^ 2

theorem two_le_prime_cast (p : Nat.Primes) : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by
  exact_mod_cast p.2.two_le

theorem log_prime_pos (p : Nat.Primes) : 0 < Real.log ((p : ℕ) : ℝ) :=
  Real.log_pos (by linarith [two_le_prime_cast p])

/-- The Euler factor is trapped between `1/8` and `1`. -/
theorem woldFactor_mem (p : Nat.Primes) :
    1 / 8 ≤ (1 - 1 / ((p : ℕ) : ℝ)) ^ 3 ∧ (1 - 1 / ((p : ℕ) : ℝ)) ^ 3 ≤ 1 := by
  have hp2 := two_le_prime_cast p
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
  have hinv : 1 / ((p : ℕ) : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hp0 (by norm_num)]
    linarith
  have hinv0 : (0 : ℝ) < 1 / ((p : ℕ) : ℝ) := by positivity
  have hu1 : (1 : ℝ) / 2 ≤ 1 - 1 / ((p : ℕ) : ℝ) := by linarith
  have hu2 : 1 - 1 / ((p : ℕ) : ℝ) ≤ 1 := by linarith
  constructor
  · calc (1 : ℝ) / 8 = (1 / 2 : ℝ) ^ 3 := by norm_num
      _ ≤ (1 - 1 / ((p : ℕ) : ℝ)) ^ 3 :=
          pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hu1 3
  · calc (1 - 1 / ((p : ℕ) : ℝ)) ^ 3 ≤ (1 : ℝ) ^ 3 :=
          pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 1 - 1 / ((p : ℕ) : ℝ)) hu2 3
      _ = 1 := by norm_num

theorem woldCoeff_nonneg (e : ℕ) (p : Nat.Primes) : 0 ≤ woldCoeff e p := by
  have hp2 := two_le_prime_cast p
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
  have hfac := (woldFactor_mem p).1
  have hlog := (log_prime_pos p).le
  rw [woldCoeff]
  have hpow : (0 : ℝ) < ((p : ℕ) : ℝ) ^ e := by positivity
  positivity

/-- **The summable majorant above the wall.**  `log p/p²` is summable because `log p ≤ 2√p`. -/
theorem summable_log_div_sq :
    Summable (fun p : Nat.Primes => Real.log ((p : ℕ) : ℝ) / ((p : ℕ) : ℝ) ^ 2) := by
  have hmaj : Summable (fun p : Nat.Primes => 2 * ((p : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) :=
    (Nat.Primes.summable_rpow.2 (by norm_num)).mul_left 2
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) hmaj
  · have hp2 := two_le_prime_cast p
    have hlog := (log_prime_pos p).le
    positivity
  · have hp2 := two_le_prime_cast p
    have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
    have hs0 : (0 : ℝ) < Real.sqrt ((p : ℕ) : ℝ) := Real.sqrt_pos.2 hp0
    have hsq : Real.sqrt ((p : ℕ) : ℝ) * Real.sqrt ((p : ℕ) : ℝ) = ((p : ℕ) : ℝ) :=
      Real.mul_self_sqrt hp0.le
    have hlog := Sieve.log_le_two_mul_sqrt hp0
    have hrpow : ((p : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))
        = 1 / (((p : ℕ) : ℝ) * Real.sqrt ((p : ℕ) : ℝ)) := by
      rw [Real.rpow_neg hp0.le, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
        Real.rpow_add hp0, Real.rpow_one, ← Real.sqrt_eq_rpow, one_div]
    rw [hrpow]
    rw [div_le_iff₀ (by positivity)]
    have hkey : Real.log ((p : ℕ) : ℝ) ≤ 2 * Real.sqrt ((p : ℕ) : ℝ) := hlog
    have hexp : 2 * (1 / (((p : ℕ) : ℝ) * Real.sqrt ((p : ℕ) : ℝ))) * ((p : ℕ) : ℝ) ^ 2
        = 2 * Real.sqrt ((p : ℕ) : ℝ) := by
      field_simp
      nlinarith [hsq]
    rw [hexp]
    exact hkey

/-- **Above the wall the anomaly is summable.** -/
theorem summable_woldCoeff_of_two_le {e : ℕ} (he : 2 ≤ e) : Summable (woldCoeff e) := by
  refine Summable.of_nonneg_of_le (fun p => woldCoeff_nonneg e p) (fun p => ?_)
    summable_log_div_sq
  have hp2 := two_le_prime_cast p
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
  have hfac := woldFactor_mem p
  have hlog := (log_prime_pos p).le
  have hpow : ((p : ℕ) : ℝ) ^ 2 ≤ ((p : ℕ) : ℝ) ^ e := by
    refine pow_le_pow_right₀ (by linarith) he
  have hpow0 : (0 : ℝ) < ((p : ℕ) : ℝ) ^ 2 := by positivity
  rw [woldCoeff]
  calc (1 - 1 / ((p : ℕ) : ℝ)) ^ 3 * Real.log ((p : ℕ) : ℝ) / ((p : ℕ) : ℝ) ^ e
      ≤ Real.log ((p : ℕ) : ℝ) / ((p : ℕ) : ℝ) ^ e := by
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        nlinarith [hfac.2, hlog]
    _ ≤ Real.log ((p : ℕ) : ℝ) / ((p : ℕ) : ℝ) ^ 2 :=
        div_le_div_of_nonneg_left hlog hpow0 hpow

/-- **Below the wall the anomaly is not summable.** -/
theorem not_summable_woldCoeff_of_lt_two {e : ℕ} (he : e < 2) : ¬ Summable (woldCoeff e) := by
  intro hsum
  have hc0 : (0 : ℝ) < Real.log 2 / 8 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    positivity
  have hlow : ∀ p : Nat.Primes, Real.log 2 / 8 * (1 / ((p : ℕ) : ℝ)) ≤ woldCoeff e p := by
    intro p
    have hp2 := two_le_prime_cast p
    have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
    have hfac := (woldFactor_mem p).1
    have hlog2 : Real.log 2 ≤ Real.log ((p : ℕ) : ℝ) := Real.log_le_log (by norm_num) hp2
    have hlogpos := (log_prime_pos p).le
    have hpow : ((p : ℕ) : ℝ) ^ e ≤ ((p : ℕ) : ℝ) := by
      have hstep : ((p : ℕ) : ℝ) ^ e ≤ ((p : ℕ) : ℝ) ^ 1 :=
        pow_le_pow_right₀ (by linarith) (by omega)
      simpa using hstep
    have hpowpos : (0 : ℝ) < ((p : ℕ) : ℝ) ^ e := by positivity
    have hstep1 : Real.log 2 / 8 * (1 / ((p : ℕ) : ℝ))
        ≤ Real.log 2 / 8 * (1 / ((p : ℕ) : ℝ) ^ e) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact one_div_le_one_div_of_le hpowpos hpow
    have hnum : Real.log 2 / 8 ≤ (1 - 1 / ((p : ℕ) : ℝ)) ^ 3 * Real.log ((p : ℕ) : ℝ) := by
      nlinarith [hfac, hlog2, hlogpos]
    rw [woldCoeff]
    calc Real.log 2 / 8 * (1 / ((p : ℕ) : ℝ))
        ≤ Real.log 2 / 8 * (1 / ((p : ℕ) : ℝ) ^ e) := hstep1
      _ = Real.log 2 / 8 / ((p : ℕ) : ℝ) ^ e := by rw [mul_one_div]
      _ ≤ (1 - 1 / ((p : ℕ) : ℝ)) ^ 3 * Real.log ((p : ℕ) : ℝ) / ((p : ℕ) : ℝ) ^ e :=
          div_le_div_of_nonneg_right hnum (by positivity)
  have hsum2 : Summable (fun p : Nat.Primes => Real.log 2 / 8 * (1 / ((p : ℕ) : ℝ))) := by
    refine Summable.of_nonneg_of_le (fun p => ?_) hlow hsum
    have hp2 := two_le_prime_cast p
    have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
    positivity
  exact Nat.Primes.not_summable_one_div ((summable_mul_left_iff (ne_of_gt hc0)).1 hsum2)

/-- **The depth wall.** -/
theorem summable_woldCoeff_iff (e : ℕ) : Summable (woldCoeff e) ↔ 2 ≤ e := by
  constructor
  · intro hsum
    by_contra hcon
    exact not_summable_woldCoeff_of_lt_two (by omega) hsum
  · exact summable_woldCoeff_of_two_le

/-- **The wall is unmoved by a nonzero scalar.** -/
theorem summable_smul_woldCoeff_iff (a : ℝ) (e : ℕ) :
    Summable (fun p => a * woldCoeff e p) ↔ (a = 0 ∨ 2 ≤ e) := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · rw [summable_mul_left_iff ha, summable_woldCoeff_iff]
    constructor
    · exact fun h => Or.inr h
    · rintro (h | h)
      · exact absurd h ha
      · exact h

/-- **The wall is unmoved by the trace-class remainder.** -/
theorem summable_smul_woldCoeff_add_remainder_iff (a : ℝ) (e : ℕ) :
    Summable (fun p => a * woldCoeff e p + woldRemainder p) ↔ (a = 0 ∨ 2 ≤ e) := by
  have hr : Summable woldRemainder := by
    have := summable_log_div_sq.mul_left 2
    refine this.congr fun p => ?_
    rw [woldRemainder]
    ring
  constructor
  · intro hsum
    have : Summable (fun p => a * woldCoeff e p) := by
      have hdiff := hsum.sub hr
      refine hdiff.congr fun p => ?_
      ring
    exact (summable_smul_woldCoeff_iff a e).1 this
  · intro h
    exact ((summable_smul_woldCoeff_iff a e).2 h).add hr

/-- The atlas transition writes the log anomaly as the depth coefficient scaled by `a`. -/
theorem log_anomaly_eq (a : ℝ) (p : Nat.Primes) (e : ℕ) :
    Real.log (primeDepthBVWoldPrimeConsecutiveTriangleAnomaly a p e) = a * woldCoeff e p := by
  rw [primeDepthBVWoldPrimeConsecutiveTriangleAnomaly_eq, Real.log_exp, woldCoeff]
  have hinv : ((p : ℕ) : ℝ)⁻¹ = 1 / ((p : ℕ) : ℝ) := (one_div _).symm
  rw [hinv, div_pow, one_pow]
  field_simp

/-- **The wall, for the atlas anomaly itself.** -/
theorem summable_log_anomaly_iff (a : ℝ) (e : ℕ) :
    Summable (fun p : Nat.Primes =>
        Real.log (primeDepthBVWoldPrimeConsecutiveTriangleAnomaly a p e))
      ↔ (a = 0 ∨ 2 ≤ e) := by
  have hcongr : (fun p : Nat.Primes =>
      Real.log (primeDepthBVWoldPrimeConsecutiveTriangleAnomaly a p e))
      = fun p : Nat.Primes => a * woldCoeff e p := by
    funext p
    exact log_anomaly_eq a p e
  rw [hcongr]
  exact summable_smul_woldCoeff_iff a e

/-- **The wall, for the atlas anomaly against the trace-class remainder.** -/
theorem summable_log_anomaly_add_remainder_iff (a : ℝ) (e : ℕ) :
    Summable (fun p : Nat.Primes =>
        Real.log (primeDepthBVWoldPrimeConsecutiveTriangleAnomaly a p e) + woldRemainder p)
      ↔ (a = 0 ∨ 2 ≤ e) := by
  have hcongr : (fun p : Nat.Primes =>
      Real.log (primeDepthBVWoldPrimeConsecutiveTriangleAnomaly a p e) + woldRemainder p)
      = fun p : Nat.Primes => a * woldCoeff e p + woldRemainder p := by
    funext p
    rw [log_anomaly_eq a p e]
  rw [hcongr]
  exact summable_smul_woldCoeff_add_remainder_iff a e

/-- **The depth-one criterion.**  At depth one the anomaly plus the trace-class remainder is
summable exactly on the critical line. -/
theorem summable_depthOne_log_anomaly_add_remainder_iff (s : ℂ) :
    Summable (fun p : Nat.Primes =>
        Real.log (primeDepthBVWoldPrimeConsecutiveTriangleAnomaly (2 * s.re - 1) p 1)
          + woldRemainder p)
      ↔ s.re = 1 / 2 := by
  rw [summable_log_anomaly_add_remainder_iff]
  constructor
  · rintro (h | h)
    · linarith
    · omega
  · intro h
    exact Or.inl (by rw [h]; ring)

end RHTower
