import GaloisForLFunctions.RHTower.MobiusDivisorCriticalLogProfilePrimitive
import GaloisForLFunctions.RHTower.Sieve.MertensSecond

/-!
# Exact logarithmic prime-tail source

The old-prime cancellation leaves a finite late-prime convolution. Taking
the primitive inside that finite sum gives the literal Mertens increment,
including its arithmetic endpoints. No prime-density approximation is used.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace RHTower

/-- The prime atoms strictly above the moving square-root cutoff. -/
def criticalLogLatePrimes (t : ℝ) : Finset ℕ :=
  (Nat.primesLE ⌊Real.exp t⌋₊).filter (fun p => t / 2 < Real.log p)

private theorem mem_logPrimeCutoff {p : ℕ} (hp : p.Prime) (u : ℝ) :
    p ∈ Nat.primesLE ⌊Real.exp u⌋₊ ↔ Real.log p ≤ u := by
  rw [Nat.mem_primesLE, and_iff_left hp,
    Nat.le_floor_iff (Real.exp_pos u).le, ← Real.log_le_iff_le_exp]
  exact_mod_cast hp.pos

private theorem late_prime_bounds {t : ℝ} {p : ℕ} (hp : p ∈ criticalLogLatePrimes t) :
    p.Prime ∧ 0 ≤ t - Real.log p ∧ t - Real.log p ≤ t / 2 := by
  obtain ⟨hpc, hpl⟩ := Finset.mem_filter.mp hp
  have hpp := (Nat.mem_primesLE.mp hpc).2
  have hpt := (mem_logPrimeCutoff hpp t).mp hpc
  exact ⟨hpp, by linarith, by linarith⟩

private theorem late_prime_set (t : ℝ) :
    (retainedPrimeCutoff (Real.exp t)).filter (fun p : ℕ => Real.exp t < (p : ℝ) ^ (2 : ℕ)) =
      criticalLogLatePrimes t := by
  ext p
  by_cases hp : p.Prime
  · have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have he : Real.exp (2 * Real.log p) = (p : ℝ) ^ (2 : ℕ) := by
      rw [show (2 : ℝ) * Real.log p = Real.log p + Real.log p by ring,
        Real.exp_add, Real.exp_log hp0]
      ring
    have hs : Real.exp t < (p : ℝ) ^ (2 : ℕ) ↔ t / 2 < Real.log p := by
      rw [← he, Real.exp_lt_exp]
      constructor <;> intro h <;> linarith
    have hp1 : 1 ≤ p := hp.one_lt.le
    simp [retainedPrimeCutoff, criticalLogLatePrimes, Nat.mem_primesLE, hp, hp1, hs]
  · simp [retainedPrimeCutoff, criticalLogLatePrimes, Nat.mem_primesLE, hp]

private theorem logProfile_prime_atom (t : ℝ) {p : ℕ} (hp : p.Prime) :
    Real.exp (-(3 / 2 : ℝ) * t) *
      (Real.sqrt p * criticalContinuousAbel (Real.exp t / p)) =
      criticalAbelLogProfile (t - Real.log p) / p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hs : Real.exp (Real.log p / 2) = Real.sqrt p := by
    rw [Real.exp_half, Real.exp_log hp0]
  have he : Real.exp (-(3 / 2 : ℝ) * t) * Real.sqrt p =
      (1 / (p : ℝ)) * Real.exp (-(3 / 2 : ℝ) * (t - Real.log p)) := by
    calc
      _ = Real.exp (-(3 / 2 : ℝ) * t + Real.log p / 2) := by rw [← hs, ← Real.exp_add]
      _ = Real.exp (-Real.log p + (-(3 / 2 : ℝ) * (t - Real.log p))) := by
        congr 1
        ring
      _ = _ := by rw [Real.exp_add, Real.exp_neg, Real.exp_log hp0, one_div]
  rw [← mul_assoc, he, criticalAbelLogProfile, Real.exp_sub, Real.exp_log hp0]
  ring

/-- The literal moving head, normalized on its actual logarithmic clock,
is the exact late-prime convolution. -/
theorem criticalMovingPrimeHead_exp_eq_log_late_sum {t : ℝ} (ht : 0 < t) :
    Real.exp (-(3 / 2 : ℝ) * t) * criticalMovingPrimeHead (Real.exp t) =
      criticalAbelLogProfile t +
        ∑ p ∈ criticalLogLatePrimes t, criticalAbelLogProfile (t - Real.log p) / p := by
  rw [criticalMovingPrimeHead_eq_late_sum (Real.one_lt_exp_iff.mpr ht),
    mul_add, Finset.mul_sum, late_prime_set]
  change criticalAbelLogProfile t + _ = criticalAbelLogProfile t + _
  congr 1
  exact Finset.sum_congr rfl (fun p hp => logProfile_prime_atom t (late_prime_bounds hp).1)

private theorem logPrimeCutoff_subset {a b : ℝ} (hab : a ≤ b) :
    Nat.primesLE ⌊Real.exp a⌋₊ ⊆ Nat.primesLE ⌊Real.exp b⌋₊ := by
  intro p hp
  have hpp := (Nat.mem_primesLE.mp hp).2
  exact (mem_logPrimeCutoff hpp b).mpr ((mem_logPrimeCutoff hpp a).mp hp |>.trans hab)

private theorem late_prime_count {t s : ℝ} (hs : s ∈ Icc (0 : ℝ) (t / 2)) :
    Sieve.mertensS ⌊Real.exp (t - s)⌋₊ - Sieve.mertensS ⌊Real.exp (t / 2)⌋₊ =
      ∑ p ∈ (criticalLogLatePrimes t).filter (fun p : ℕ => s ≤ t - Real.log p), 1 / (p : ℝ) := by
  have hsub := logPrimeCutoff_subset (show t / 2 ≤ t - s by linarith [hs.2])
  have hsum := Finset.sum_sdiff (f := fun p : ℕ => 1 / (p : ℝ)) hsub
  have hset : (criticalLogLatePrimes t).filter (fun p : ℕ => s ≤ t - Real.log p) =
      Nat.primesLE ⌊Real.exp (t - s)⌋₊ \ Nat.primesLE ⌊Real.exp (t / 2)⌋₊ := by
    ext p
    by_cases hp : p.Prime
    · simp only [criticalLogLatePrimes, Finset.mem_filter, Finset.mem_sdiff,
        mem_logPrimeCutoff hp, not_le]
      constructor
      · rintro ⟨⟨hpt, hpl⟩, hsp⟩
        exact ⟨by linarith, hpl⟩
      · rintro ⟨hps, hpl⟩
        exact ⟨⟨by linarith [hs.1], hpl⟩, by linarith⟩
    · simp [criticalLogLatePrimes, Nat.mem_primesLE, hp]
  rw [hset, Sieve.mertensS, Sieve.mertensS]
  linarith

private def primeVelocityAtom (t : ℝ) (p : ℕ) (s : ℝ) : ℝ :=
  (Iic (t - Real.log p)).indicator (fun s => criticalAbelLogVelocity s / p) s

private theorem primeVelocityAtom_integrable (t : ℝ) (p : ℕ) :
    IntegrableOn (primeVelocityAtom t p) (Ioc (0 : ℝ) (t / 2)) :=
  ((integrableOn_criticalAbelLogVelocity.mono_set (fun _ hx => hx.1)).div_const p).indicator
    measurableSet_Iic

private theorem primeVelocityAtom_integral {t : ℝ} {p : ℕ}
    (hp : p ∈ criticalLogLatePrimes t) :
    (∫ s in Ioc (0 : ℝ) (t / 2), primeVelocityAtom t p s) =
      criticalAbelLogProfile (t - Real.log p) / p := by
  obtain ⟨_, hd0, hdt⟩ := late_prime_bounds hp
  simp only [primeVelocityAtom]
  rw [integral_indicator measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic]
  have hs : Iic (t - Real.log p) ∩ Ioc (0 : ℝ) (t / 2) = Ioc 0 (t - Real.log p) := by
    ext s
    simp only [mem_inter_iff, mem_Iic, mem_Ioc]
    exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, h.2.trans hdt⟩⟩
  rw [hs, ← intervalIntegral.integral_of_le hd0, intervalIntegral.integral_div,
    criticalAbelLogVelocity_integral hd0]

private theorem primeVelocityAtom_sum {t s : ℝ} (hs : s ∈ Icc (0 : ℝ) (t / 2)) :
    (∑ p ∈ criticalLogLatePrimes t, primeVelocityAtom t p s) =
      criticalAbelLogVelocity s *
        (Sieve.mertensS ⌊Real.exp (t - s)⌋₊ - Sieve.mertensS ⌊Real.exp (t / 2)⌋₊) := by
  rw [late_prime_count hs, Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : s ≤ t - Real.log p
  · simp only [primeVelocityAtom, Set.indicator_apply, mem_Iic, if_pos hp]
    ring
  · simp only [primeVelocityAtom, Set.indicator_apply, mem_Iic, if_neg hp]

/-- The finite arithmetic prime convolution equals the integral against
the actual stepwise Mertens increment. -/
theorem criticalLogLatePrimes_profile_eq_mertens_integral {t : ℝ} (ht : 0 ≤ t) :
    (∑ p ∈ criticalLogLatePrimes t, criticalAbelLogProfile (t - Real.log p) / p) =
      ∫ s in (0 : ℝ)..t / 2, criticalAbelLogVelocity s *
        (Sieve.mertensS ⌊Real.exp (t - s)⌋₊ - Sieve.mertensS ⌊Real.exp (t / 2)⌋₊) := by
  rw [intervalIntegral.integral_of_le (by linarith : (0 : ℝ) ≤ t / 2)]
  calc
    _ = ∑ p ∈ criticalLogLatePrimes t,
        ∫ s in Ioc (0 : ℝ) (t / 2), primeVelocityAtom t p s := by
      exact Finset.sum_congr rfl (fun p hp => (primeVelocityAtom_integral hp).symm)
    _ = ∫ s in Ioc (0 : ℝ) (t / 2), ∑ p ∈ criticalLogLatePrimes t,
        primeVelocityAtom t p s :=
      (integral_finsetSum _ (fun p _ => primeVelocityAtom_integrable t p)).symm
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro s hs
      exact primeVelocityAtom_sum ⟨hs.1.le, hs.2⟩

/-- Absolute admission follows from the actual finite prime interchange. -/
theorem intervalIntegrable_criticalLogLatePrimes_mertens (t : ℝ) (ht : 0 ≤ t) :
    IntervalIntegrable (fun s => criticalAbelLogVelocity s *
      (Sieve.mertensS ⌊Real.exp (t - s)⌋₊ - Sieve.mertensS ⌊Real.exp (t / 2)⌋₊)) volume 0 (t / 2) := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : (0 : ℝ) ≤ t / 2)).mpr
  apply IntegrableOn.congr_fun
    (integrable_finsetSum (criticalLogLatePrimes t) (fun p _ => primeVelocityAtom_integrable t p))
    _ measurableSet_Ioc
  intro s hs
  exact primeVelocityAtom_sum ⟨hs.1.le, hs.2⟩

/-- The continuous part of the exact prime increment is the Cauchy kernel.
Both boundary products vanish before any absolute value is taken. -/
theorem criticalAbelLogVelocity_log_increment {t : ℝ} (ht : 0 < t) :
    (∫ s in (0 : ℝ)..t / 2, criticalAbelLogVelocity s *
      (Real.log (t - s) - Real.log (t / 2))) =
      ∫ s in (0 : ℝ)..t / 2, criticalAbelLogProfile s / (t - s) := by
  have hb : (0 : ℝ) ≤ t / 2 := by linarith
  have hn (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (t / 2)) : t - s ≠ 0 := by
    linarith [hs.2]
  have hL : ContinuousOn (fun s : ℝ => Real.log (t - s) - Real.log (t / 2))
      (Icc 0 (t / 2)) :=
    ((continuousOn_const.sub continuousOn_id).log hn).sub continuousOn_const
  have hD : ContinuousOn (fun s : ℝ => (-1) / (t - s)) (Icc 0 (t / 2)) :=
    continuousOn_const.div (continuousOn_const.sub continuousOn_id) hn
  have hLp (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) (t / 2)) :
      HasDerivWithinAt (fun s : ℝ => Real.log (t - s) - Real.log (t / 2))
        ((-1) / (t - s)) (Ioi s) s := by
    exact ((((hasDerivAt_id s).const_sub t).log (hn s ⟨hs.1.le, hs.2.le⟩)).sub_const
      (Real.log (t / 2))).hasDerivWithinAt
  have ha : ContinuousOn criticalAbelLogProfile (uIcc (0 : ℝ) (t / 2)) := by
    simpa only [uIcc_of_le hb] using continuousOn_criticalAbelLogProfile hb
  have hLi : ContinuousOn (fun s : ℝ => Real.log (t - s) - Real.log (t / 2))
      (uIcc 0 (t / 2)) := by simpa only [uIcc_of_le hb] using hL
  have hvi : IntervalIntegrable criticalAbelLogVelocity volume 0 (t / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hb).mpr
      (integrableOn_criticalAbelLogVelocity.mono_set (fun _ hx => hx.1))
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right hLi ha
    (by simpa only [min_eq_left hb, max_eq_right hb] using hLp)
    (by
      intro s hs
      rw [min_eq_left hb, max_eq_right hb] at hs
      exact criticalAbelLogProfile_hasDeriv_right hs.1.le)
    (hD.intervalIntegrable_of_Icc hb) hvi
  have ha0 : criticalAbelLogProfile 0 = 0 := by
    rw [← criticalAbelLogVelocity_integral (le_refl (0 : ℝ)), intervalIntegral.integral_same]
  have hbzero : Real.log (t - t / 2) - Real.log (t / 2) = 0 := by
    rw [show t - t / 2 = t / 2 by ring, sub_self]
  rw [hbzero, ha0, zero_mul, mul_zero, sub_zero, zero_sub] at h
  calc
    _ = ∫ s in (0 : ℝ)..t / 2,
        (Real.log (t - s) - Real.log (t / 2)) * criticalAbelLogVelocity s := by
      apply intervalIntegral.integral_congr
      intro s _
      ring
    _ = _ := by
      rw [h, ← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro s _
      ring

end RHTower
