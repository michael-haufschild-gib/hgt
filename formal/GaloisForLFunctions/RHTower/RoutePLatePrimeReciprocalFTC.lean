import GaloisForLFunctions.RHTower.RoutePLatePrimeReciprocalAdmission
import GaloisForLFunctions.RHTower.RoutePLatePrimeRightVelocity
import GaloisForLFunctions.RHTower.RoutePNativeSignedMixedPrimitive
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Exact reciprocal calculus across physical prime removals

Subtracting the cumulative actual reciprocal jumps makes the inverse
continuous on a native late ray. Its right derivative exists at every
clock, including the removal clocks. Right-derivative FTC then retains
the complete atomic correction.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace RHTower

private def removalSum (w : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊Real.exp (t / 2)⌋₊, w p

/-- Cumulative actual reciprocal atoms. Early atoms cancel from every late
finite-window difference; total division introduces no denominator premise. -/
def routePLatePrimeReciprocalJumpPrimitive : ℝ → ℝ :=
  removalSum routePLatePrimeReciprocalJump

/-- Reciprocal after subtracting all physical removal jumps. -/
def routePLatePrimeCorrectedReciprocal (t : ℝ) : ℝ :=
  1 / routePLatePrimeIncrement t - routePLatePrimeReciprocalJumpPrimitive t

private theorem primeClock_mem {p : ℕ} (hp : p.Prime) (t : ℝ) :
    p ∈ Nat.primesLE ⌊Real.exp t⌋₊ ↔ Real.log p ≤ t := by
  rw [Nat.mem_primesLE, and_iff_left hp,
    Nat.le_floor_iff (Real.exp_pos t).le, ← Real.log_le_iff_le_exp]
  exact_mod_cast hp.pos

private theorem removalSum_eq_finite (w : ℕ → ℝ) {s t : ℝ} (hst : s ≤ t) :
    removalSum w s = ∑ p ∈ Nat.primesLE ⌊Real.exp (t / 2)⌋₊,
      if 2 * Real.log p ≤ s then w p else 0 := by
  classical
  have hfilter : (Nat.primesLE ⌊Real.exp (t / 2)⌋₊).filter
      (fun p : ℕ => 2 * Real.log p ≤ s) = Nat.primesLE ⌊Real.exp (s / 2)⌋₊ := by
    ext p
    by_cases hp : p.Prime
    · simp only [Finset.mem_filter, primeClock_mem hp]
      constructor
      · intro h
        linarith [h.2]
      · intro h
        constructor <;> linarith
    · simp [Nat.mem_primesLE, hp]
  rw [removalSum, ← hfilter, Finset.sum_filter]

private theorem step_eventually_right (τ c x : ℝ) :
    (fun t : ℝ => if τ ≤ t then c else 0) =ᶠ[𝓝[Ici x] x]
      (fun _ => if τ ≤ x then c else 0) := by
  by_cases hτ : τ ≤ x
  · filter_upwards [self_mem_nhdsWithin] with t ht
    rw [if_pos hτ, if_pos (hτ.trans ht)]
  · filter_upwards [(eventually_lt_nhds (lt_of_not_ge hτ)).filter_mono
      nhdsWithin_le_nhds] with t ht
    rw [if_neg hτ, if_neg (not_le.mpr ht)]

private theorem step_left (τ c x : ℝ) :
    Tendsto (fun t : ℝ => if τ ≤ t then c else 0) (𝓝[Iio x] x)
      (𝓝 (if τ < x then c else 0)) := by
  by_cases hτ : τ < x
  · rw [if_pos hτ]
    apply tendsto_const_nhds.congr'
    filter_upwards [(eventually_gt_nhds hτ).filter_mono nhdsWithin_le_nhds] with t ht
    exact (if_pos ht.le).symm
  · rw [if_neg hτ]
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (if_neg (not_le.mpr (ht.trans_le (le_of_not_gt hτ)))).symm

private theorem removalSum_right (w : ℕ → ℝ) (x : ℝ) :
    ContinuousWithinAt (removalSum w) (Ici x) x := by
  have hsum := tendsto_finsetSum (Nat.primesLE ⌊Real.exp ((x + 1) / 2)⌋₊)
    (fun p _ => tendsto_const_nhds.congr' (step_eventually_right (2 * Real.log p) (w p) x).symm)
  rw [← removalSum_eq_finite w (show x ≤ x + 1 by linarith)] at hsum
  apply hsum.congr'
  filter_upwards [(eventually_lt_nhds (show x < x + 1 by linarith)).filter_mono
    nhdsWithin_le_nhds] with t ht
  exact (removalSum_eq_finite w ht.le).symm

private theorem removalSum_hasDeriv_right (w : ℕ → ℝ) (x : ℝ) :
    HasDerivWithinAt (removalSum w) 0 (Ioi x) x := by
  have hstep (p : ℕ) : HasDerivWithinAt
      (fun t : ℝ => if 2 * Real.log p ≤ t then w p else 0) 0 (Ioi x) x := by
    apply (hasDerivWithinAt_const x (Ioi x)
      (if 2 * Real.log p ≤ x then w p else 0)).congr_of_eventuallyEq
    · exact (step_eventually_right (2 * Real.log p) (w p) x).filter_mono
        (nhdsWithin_mono _ Ioi_subset_Ici_self)
    · rfl
  have hsum := HasDerivWithinAt.fun_sum
    (u := Nat.primesLE ⌊Real.exp ((x + 1) / 2)⌋₊) (fun p _ => hstep p)
  simp only [Finset.sum_const_zero] at hsum
  apply hsum.congr_of_eventuallyEq
  · filter_upwards [(eventually_lt_nhds (show x < x + 1 by linarith)).filter_mono
      nhdsWithin_le_nhds] with t ht
    exact removalSum_eq_finite w ht.le
  · exact removalSum_eq_finite w (show x ≤ x + 1 by linarith)

private theorem removalSum_left_prime (w : ℕ → ℝ) {q : ℕ} (hq : q.Prime) :
    Tendsto (removalSum w) (𝓝[Iio (2 * Real.log q)] (2 * Real.log q))
      (𝓝 (removalSum w (2 * Real.log q) - w q)) := by
  classical
  let P := Nat.primesLE ⌊Real.exp ((2 * Real.log q + 1) / 2)⌋₊
  have hqP : q ∈ P := (primeClock_mem hq _).mpr (by linarith)
  have hdiff : removalSum w (2 * Real.log q) -
      (∑ p ∈ P, if 2 * Real.log p < 2 * Real.log q then w p else 0) = w q := by
    rw [removalSum_eq_finite w
      (show 2 * Real.log (q : ℝ) ≤ 2 * Real.log q + 1 by linarith)]
    change (∑ p ∈ P, if 2 * Real.log p ≤ 2 * Real.log q then w p else 0) - _ = _
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single q]
    · simp
    · intro p hp hpq
      have hp0 : 0 < (p : ℝ) := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.pos
      have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq.pos
      have hne : 2 * Real.log (p : ℝ) ≠ 2 * Real.log q := by
        intro h
        have hl : Real.log (p : ℝ) = Real.log q := by linarith
        exact hpq (by exact_mod_cast Real.log_injOn_pos hp0 hq0 hl)
      by_cases hle : 2 * Real.log (p : ℝ) ≤ 2 * Real.log q
      · simp [hle, lt_of_le_of_ne hle hne]
      · simp [hle, not_lt.mpr (le_of_not_ge hle)]
    · exact fun hnot => False.elim (hnot hqP)
  have hsum := tendsto_finsetSum P (fun p _ => step_left (2 * Real.log p) (w p)
    (2 * Real.log q))
  have hval : (∑ p ∈ P, if 2 * Real.log p < 2 * Real.log q then w p else 0) =
      removalSum w (2 * Real.log q) - w q := by linarith [hdiff]
  rw [hval] at hsum
  apply hsum.congr'
  filter_upwards [(eventually_lt_nhds
    (show 2 * Real.log (q : ℝ) < 2 * Real.log q + 1 by linarith)).filter_mono
      nhdsWithin_le_nhds] with t ht
  exact (removalSum_eq_finite w ht.le).symm

private theorem removalSum_left_nonclock (w : ℕ → ℝ) {x : ℝ}
    (hx : ∀ p : ℕ, p.Prime → x ≠ 2 * Real.log p) :
    ContinuousWithinAt (removalSum w) (Iio x) x := by
  have hsum := tendsto_finsetSum (Nat.primesLE ⌊Real.exp ((x + 1) / 2)⌋₊)
    (fun p _ => step_left (2 * Real.log p) (w p) x)
  have hval : (∑ p ∈ Nat.primesLE ⌊Real.exp ((x + 1) / 2)⌋₊,
      if 2 * Real.log p < x then w p else 0) = removalSum w x := by
    rw [removalSum_eq_finite w (show x ≤ x + 1 by linarith)]
    apply Finset.sum_congr rfl
    intro p hp
    have hne := (hx p (Nat.mem_primesLE.mp hp).2).symm
    have heq : 2 * Real.log (p : ℝ) < x ↔ 2 * Real.log (p : ℝ) ≤ x :=
      ⟨le_of_lt, fun h => lt_of_le_of_ne h hne⟩
    simp only [heq]
  rw [hval] at hsum
  apply hsum.congr'
  filter_upwards [(eventually_lt_nhds (show x < x + 1 by linarith)).filter_mono
    nhdsWithin_le_nhds] with t ht
  exact (removalSum_eq_finite w ht.le).symm

private theorem corrected_continuous {T : ℝ} (hT : 0 < T)
    (hr : ∀ t, T < t → routePLatePrimeIncrement t ≠ 0)
    (hl : ∀ p : ℕ, p.Prime → T < 2 * Real.log p →
      routePLatePrimeIncrement (2 * Real.log p) + criticalAbelLogProfile (Real.log p) / p ≠ 0)
    {x : ℝ} (hx : T < x) : ContinuousAt routePLatePrimeCorrectedReciprocal x := by
  have hx0 := hT.trans hx
  have hrightInv : ContinuousWithinAt (fun t => 1 / routePLatePrimeIncrement t)
      (Ici x) x := by
    simpa only [one_div, Pi.inv_def] using
      (continuousWithinAt_routePLatePrimeIncrement_right hx0).inv₀ (hr x hx)
  have hright : ContinuousWithinAt routePLatePrimeCorrectedReciprocal (Ici x) x :=
    hrightInv.sub (removalSum_right routePLatePrimeReciprocalJump x)
  apply continuousAt_iff_continuous_left'_right'.mpr
  refine ⟨?_, hright.mono Ioi_subset_Ici_self⟩
  by_cases hclock : ∃ p : ℕ, p.Prime ∧ x = 2 * Real.log p
  · obtain ⟨p, hp, rfl⟩ := hclock
    have hleftInv : Tendsto (fun t => 1 / routePLatePrimeIncrement t)
        (𝓝[Iio (2 * Real.log p)] (2 * Real.log p))
        (𝓝 (1 / (routePLatePrimeIncrement (2 * Real.log p) +
          criticalAbelLogProfile (Real.log p) / p))) := by
      simpa only [one_div] using
        (tendsto_routePLatePrimeIncrement_left_prime hp).inv₀ (hl p hp hx)
    have h := hleftInv.sub (removalSum_left_prime routePLatePrimeReciprocalJump hp)
    have hval : 1 / (routePLatePrimeIncrement (2 * Real.log p) +
          criticalAbelLogProfile (Real.log p) / p) -
        (removalSum routePLatePrimeReciprocalJump (2 * Real.log p) -
          routePLatePrimeReciprocalJump p) =
        routePLatePrimeCorrectedReciprocal (2 * Real.log p) := by
      unfold routePLatePrimeCorrectedReciprocal routePLatePrimeReciprocalJumpPrimitive
      rw [routePLatePrimeReciprocalJump]
      field_simp [hr _ hx, hl p hp hx]
      ring
    rw [hval] at h
    exact h
  · have hnon : ∀ p : ℕ, p.Prime → x ≠ 2 * Real.log p :=
      fun p hp heq => hclock ⟨p, hp, heq⟩
    have ha : ContinuousWithinAt routePLatePrimeRemovalMass (Iio x) x :=
      removalSum_left_nonclock (fun p => criticalAbelLogProfile (Real.log p) / p) hnon
    have hj := ((continuousAt_routePLatePrimeVelocityPrimitive hx0).tendsto.mono_left
      nhdsWithin_le_nhds).sub ha
    rw [← routePLatePrimeIncrement_eq_velocity_sub_removals hx0.le] at hj
    have hj' : ContinuousWithinAt routePLatePrimeIncrement (Iio x) x := by
      apply hj.congr'
      filter_upwards [(eventually_gt_nhds hx0).filter_mono nhdsWithin_le_nhds] with t ht
      exact (routePLatePrimeIncrement_eq_velocity_sub_removals ht.le).symm
    have hi : ContinuousWithinAt (fun t => 1 / routePLatePrimeIncrement t) (Iio x) x := by
      simpa only [one_div, Pi.inv_def] using hj'.inv₀ (hr x hx)
    exact hi.sub (removalSum_left_nonclock routePLatePrimeReciprocalJump hnon)

private theorem corrected_hasDeriv_right {t : ℝ} (ht : routePLatePrimeIncrement t ≠ 0) :
    HasDerivWithinAt routePLatePrimeCorrectedReciprocal
      (-(routePLatePrimeRightVelocity t / routePLatePrimeIncrement t ^ 2)) (Ioi t) t := by
  change HasDerivWithinAt
    (fun s => 1 / routePLatePrimeIncrement s - removalSum routePLatePrimeReciprocalJump s)
    (-(routePLatePrimeRightVelocity t / routePLatePrimeIncrement t ^ 2)) (Ioi t) t
  simpa only [one_div, Pi.inv_def, Pi.sub_def, sub_zero, neg_div] using
      ((routePLatePrimeIncrement_hasDeriv_right t).inv ht).sub
        (removalSum_hasDeriv_right routePLatePrimeReciprocalJump t)

/-- The corrected reciprocal is genuinely continuous, with the exact right
derivative at every clock on an unconditionally obtained native late ray. -/
theorem exists_routePLatePrimeCorrectedReciprocalCalculus :
    ∃ T : ℝ, 0 < T ∧ ContinuousOn routePLatePrimeCorrectedReciprocal (Ioi T) ∧
      ∀ t : ℝ, T < t → HasDerivWithinAt routePLatePrimeCorrectedReciprocal
        (-(routePLatePrimeRightVelocity t / routePLatePrimeIncrement t ^ 2)) (Ioi t) t := by
  obtain ⟨T, C, hT, _, hr, hl⟩ := exists_routePLatePrimeReciprocalBounds
  refine ⟨T, hT, ?_, ?_⟩
  · intro x hx
    exact (corrected_continuous hT (fun t ht => (hr t ht).1)
      (fun p hp ht => (hl p hp ht).1) hx).continuousWithinAt
  · intro t ht
    exact corrected_hasDeriv_right (hr t ht).1

private theorem reciprocalDensity_intervalIntegrable {T : ℝ}
    (hI : IntegrableOn (fun t => Real.exp (-1 * t) * routePLatePrimeVelocity t /
      routePLatePrimeIncrement t ^ 2) (Ioi T))
    {a b : ℝ} (hTa : T < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => routePLatePrimeVelocity t / routePLatePrimeIncrement t ^ 2)
      volume a b := by
  have hi := hI.mono_set (show Ioc a b ⊆ Ioi T from fun t ht => hTa.trans ht.1)
  have hw := hi.mul_continuousOn_of_subset
    (show ContinuousOn (fun t : ℝ => Real.exp t) (Icc a b) by fun_prop)
    measurableSet_Ioc isCompact_Icc Ioc_subset_Icc_self
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
  apply hw.congr
  filter_upwards [] with t
  calc
    (Real.exp (-1 * t) * routePLatePrimeVelocity t / routePLatePrimeIncrement t ^ 2) *
        Real.exp t = (Real.exp (-t) * Real.exp t) *
          (routePLatePrimeVelocity t / routePLatePrimeIncrement t ^ 2) := by
      simp only [neg_mul, one_mul]
      ring
    _ = _ := by rw [← Real.exp_add]; simp

/-- Exact native reciprocal FTC. Both endpoints take the literal right value;
the cumulative difference retains precisely the removals in `(a,b]`. -/
theorem exists_routePLatePrimeReciprocalFTC :
    ∃ T : ℝ, 0 < T ∧ ∀ a b : ℝ, T < a → a ≤ b →
      1 / routePLatePrimeIncrement b - 1 / routePLatePrimeIncrement a =
        -(∫ t in a..b, routePLatePrimeVelocity t / routePLatePrimeIncrement t ^ 2) +
          (routePLatePrimeReciprocalJumpPrimitive b -
            routePLatePrimeReciprocalJumpPrimitive a) := by
  obtain ⟨Tc, hTc, hc, hd⟩ := exists_routePLatePrimeCorrectedReciprocalCalculus
  obtain ⟨Ti, hTi, hi⟩ := exists_routePLatePrimeReciprocalAdmission
  refine ⟨max Tc Ti, lt_of_lt_of_le hTc (le_max_left _ _), ?_⟩
  intro a b hTa hab
  have hca : Tc < a := (le_max_left _ _).trans_lt hTa
  have hia : Ti < a := (le_max_right _ _).trans_lt hTa
  have hv := reciprocalDensity_intervalIntegrable (hi 1 zero_lt_one).1 hia hab
  have hvr : IntervalIntegrable
      (fun t => routePLatePrimeRightVelocity t / routePLatePrimeIncrement t ^ 2)
        volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
    apply ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hv).congr
    apply ae_restrict_of_ae
    filter_upwards [routePLatePrimeRightVelocity_ae_eq] with t ht
    rw [ht]
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab
    (hc.mono (show Icc a b ⊆ Ioi Tc from fun t ht => hca.trans_le ht.1))
    (fun t ht => hd t (hca.trans ht.1)) hvr.neg
  rw [intervalIntegral.integral_neg] at hftc
  have hvel : (∫ t in a..b, routePLatePrimeRightVelocity t / routePLatePrimeIncrement t ^ 2) =
      ∫ t in a..b, routePLatePrimeVelocity t / routePLatePrimeIncrement t ^ 2 := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [routePLatePrimeRightVelocity_ae_eq] with t ht _
    rw [ht]
  rw [hvel] at hftc
  unfold routePLatePrimeCorrectedReciprocal at hftc
  linarith

/-- The literal mixed primitive divided by the native increment, with every
physical product jump removed before integration. -/
def routePNativeMixedCorrectedPrimitive (ε t : ℝ) : ℝ :=
  routePNativeLatePrimeMixedPrimitive ε t * (1 / routePLatePrimeIncrement t) -
    removalSum (fun p => routePNativeLatePrimeMixedPrimitive ε (2 * Real.log p) *
      routePLatePrimeReciprocalJump p) t

private theorem mixedCorrected_continuous {T : ℝ} (hT : 0 < T)
    (hr : ∀ t, T < t → routePLatePrimeIncrement t ≠ 0)
    (hl : ∀ p : ℕ, p.Prime → T < 2 * Real.log p →
      routePLatePrimeIncrement (2 * Real.log p) + criticalAbelLogProfile (Real.log p) / p ≠ 0)
    (ε : ℝ) {x : ℝ} (hx : T < x) :
    ContinuousAt (routePNativeMixedCorrectedPrimitive ε) x := by
  let w : ℕ → ℝ := fun p => routePNativeLatePrimeMixedPrimitive ε (2 * Real.log p) *
    routePLatePrimeReciprocalJump p
  have hx0 := hT.trans hx
  have hQ := continuousAt_routePNativeLatePrimeMixedPrimitive ε hx0
  have hrightInv : ContinuousWithinAt (fun t => 1 / routePLatePrimeIncrement t)
      (Ici x) x := by
    simpa only [one_div, Pi.inv_def] using
      (continuousWithinAt_routePLatePrimeIncrement_right hx0).inv₀ (hr x hx)
  have hright : ContinuousWithinAt (routePNativeMixedCorrectedPrimitive ε) (Ici x) x :=
    (hQ.continuousWithinAt.mul hrightInv).sub (removalSum_right w x)
  apply continuousAt_iff_continuous_left'_right'.mpr
  refine ⟨?_, hright.mono Ioi_subset_Ici_self⟩
  by_cases hclock : ∃ p : ℕ, p.Prime ∧ x = 2 * Real.log p
  · obtain ⟨p, hp, rfl⟩ := hclock
    have hleftInv : Tendsto (fun t => 1 / routePLatePrimeIncrement t)
        (𝓝[Iio (2 * Real.log p)] (2 * Real.log p))
        (𝓝 (1 / (routePLatePrimeIncrement (2 * Real.log p) +
          criticalAbelLogProfile (Real.log p) / p))) := by
      simpa only [one_div] using
        (tendsto_routePLatePrimeIncrement_left_prime hp).inv₀ (hl p hp hx)
    have h := ((hQ.tendsto.mono_left nhdsWithin_le_nhds).mul hleftInv).sub
      (removalSum_left_prime w hp)
    have hval : routePNativeLatePrimeMixedPrimitive ε (2 * Real.log p) *
          (1 / (routePLatePrimeIncrement (2 * Real.log p) +
            criticalAbelLogProfile (Real.log p) / p)) -
        (removalSum w (2 * Real.log p) - w p) =
        routePNativeMixedCorrectedPrimitive ε (2 * Real.log p) := by
      change _ = routePNativeLatePrimeMixedPrimitive ε (2 * Real.log p) *
        (1 / routePLatePrimeIncrement (2 * Real.log p)) - removalSum w (2 * Real.log p)
      have hw : w p = routePNativeLatePrimeMixedPrimitive ε (2 * Real.log p) *
          ((criticalAbelLogProfile (Real.log p) / p) /
            (routePLatePrimeIncrement (2 * Real.log p) *
              (routePLatePrimeIncrement (2 * Real.log p) +
                criticalAbelLogProfile (Real.log p) / p))) := rfl
      rw [hw]
      field_simp [hr _ hx, hl p hp hx]
      ring
    rw [hval] at h
    exact h
  · have hnon : ∀ p : ℕ, p.Prime → x ≠ 2 * Real.log p :=
      fun p hp heq => hclock ⟨p, hp, heq⟩
    have ha : ContinuousWithinAt routePLatePrimeRemovalMass (Iio x) x :=
      removalSum_left_nonclock (fun p => criticalAbelLogProfile (Real.log p) / p) hnon
    have hj := ((continuousAt_routePLatePrimeVelocityPrimitive hx0).tendsto.mono_left
      nhdsWithin_le_nhds).sub ha
    rw [← routePLatePrimeIncrement_eq_velocity_sub_removals hx0.le] at hj
    have hj' : ContinuousWithinAt routePLatePrimeIncrement (Iio x) x := by
      apply hj.congr'
      filter_upwards [(eventually_gt_nhds hx0).filter_mono nhdsWithin_le_nhds] with t ht
      exact (routePLatePrimeIncrement_eq_velocity_sub_removals ht.le).symm
    have hi : ContinuousWithinAt (fun t => 1 / routePLatePrimeIncrement t) (Iio x) x := by
      simpa only [one_div, Pi.inv_def] using hj'.inv₀ (hr x hx)
    exact (hQ.continuousWithinAt.mul hi).sub (removalSum_left_nonclock w hnon)

private theorem mixedCorrected_hasDeriv_right (ε : ℝ) {t : ℝ}
    (ht : 0 < t) (hne : routePLatePrimeIncrement t ≠ 0) :
    HasDerivWithinAt (routePNativeMixedCorrectedPrimitive ε)
      (Real.exp ((1 / 2 - ε) * t) * routePNativeCriticalProfile t -
        routePNativeLatePrimeMixedPrimitive ε t * routePLatePrimeRightVelocity t /
          routePLatePrimeIncrement t ^ 2) (Ioi t) t := by
  have hcancel : routePNativeLatePrimeMixedWork ε t * (routePLatePrimeIncrement t)⁻¹ =
      Real.exp ((1 / 2 - ε) * t) * routePNativeCriticalProfile t := by
    calc
      _ = Real.exp ((1 - ε) * t) * criticalAbelLogProfile t := by
        unfold routePNativeLatePrimeMixedWork
        rw [mul_assoc, mul_inv_cancel₀ hne, mul_one]
      _ = _ := by
        rw [routePNativeCriticalProfile_eq_exp_mul_logProfile, ← mul_assoc, ← Real.exp_add]
        congr 2
        ring
  have h := ((routePNativeLatePrimeMixedPrimitive_hasDeriv_right ε ht).mul
    ((routePLatePrimeIncrement_hasDeriv_right t).inv hne)).sub
      (removalSum_hasDeriv_right (fun p =>
        routePNativeLatePrimeMixedPrimitive ε (2 * Real.log p) * routePLatePrimeReciprocalJump p) t)
  have hcoeff : routePNativeLatePrimeMixedWork ε t * (routePLatePrimeIncrement t)⁻¹ +
      routePNativeLatePrimeMixedPrimitive ε t *
        (-routePLatePrimeRightVelocity t / routePLatePrimeIncrement t ^ 2) - 0 =
      Real.exp ((1 / 2 - ε) * t) * routePNativeCriticalProfile t -
        routePNativeLatePrimeMixedPrimitive ε t * routePLatePrimeRightVelocity t /
          routePLatePrimeIncrement t ^ 2 := by
    rw [hcancel]
    ring
  have h' := h.congr_deriv hcoeff
  change HasDerivWithinAt (fun s => routePNativeLatePrimeMixedPrimitive ε s *
    (1 / routePLatePrimeIncrement s) - removalSum (fun p =>
      routePNativeLatePrimeMixedPrimitive ε (2 * Real.log p) * routePLatePrimeReciprocalJump p) s)
    _ (Ioi t) t
  simpa only [Pi.mul_def, Pi.inv_def, Pi.sub_def, one_div] using h'

/-- Every product jump of the literal signed primitive is absorbed, leaving
an everywhere right derivative with the exact native profile coefficient. -/
theorem exists_routePNativeMixedCorrectedPrimitiveCalculus :
    ∃ T : ℝ, 0 < T ∧ ∀ ε : ℝ,
      ContinuousOn (routePNativeMixedCorrectedPrimitive ε) (Ioi T) ∧
      ∀ t : ℝ, T < t → HasDerivWithinAt (routePNativeMixedCorrectedPrimitive ε)
        (Real.exp ((1 / 2 - ε) * t) * routePNativeCriticalProfile t -
          routePNativeLatePrimeMixedPrimitive ε t * routePLatePrimeRightVelocity t /
            routePLatePrimeIncrement t ^ 2) (Ioi t) t := by
  obtain ⟨T, C, hT, _, hr, hl⟩ := exists_routePLatePrimeReciprocalBounds
  refine ⟨T, hT, ?_⟩
  intro ε
  constructor
  · intro x hx
    exact (mixedCorrected_continuous hT (fun t ht => (hr t ht).1)
      (fun p hp ht => (hl p hp ht).1) ε hx).continuousWithinAt
  · intro t ht
    exact mixedCorrected_hasDeriv_right ε (hT.trans ht) (hr t ht).1

/-- Exact native product identity after absorbing all removal atoms. It is
the finite-window input for the signed primitive's Laplace representation. -/
theorem exists_routePNativeMixedCorrectedPrimitiveFTC :
    ∃ T : ℝ, 0 < T ∧ ∀ ε a b : ℝ, T < a → a ≤ b →
      routePNativeMixedCorrectedPrimitive ε b - routePNativeMixedCorrectedPrimitive ε a =
        (∫ t in a..b, Real.exp ((1 / 2 - ε) * t) * routePNativeCriticalProfile t) -
          ∫ t in a..b, routePNativeLatePrimeMixedPrimitive ε t * routePLatePrimeVelocity t /
            routePLatePrimeIncrement t ^ 2 := by
  obtain ⟨Tc, hTc, hcalc⟩ := exists_routePNativeMixedCorrectedPrimitiveCalculus
  obtain ⟨Ti, _, hi⟩ := exists_routePLatePrimeReciprocalAdmission
  refine ⟨max Tc Ti, lt_of_lt_of_le hTc (le_max_left _ _), ?_⟩
  intro ε a b hTa hab
  have hca : Tc < a := (le_max_left _ _).trans_lt hTa
  have hia : Ti < a := (le_max_right _ _).trans_lt hTa
  have hQ : ContinuousOn (routePNativeLatePrimeMixedPrimitive ε) (Icc a b) := by
    intro t ht
    exact (continuousAt_routePNativeLatePrimeMixedPrimitive ε
      ((hTc.trans hca).trans_le ht.1)).continuousWithinAt
  have hv := reciprocalDensity_intervalIntegrable (hi 1 zero_lt_one).1 hia hab
  have hDprod := ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hv).mul_continuousOn_of_subset
    hQ measurableSet_Ioc isCompact_Icc Ioc_subset_Icc_self
  have hD : IntervalIntegrable (fun t => routePNativeLatePrimeMixedPrimitive ε t *
      routePLatePrimeVelocity t / routePLatePrimeIncrement t ^ 2) volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
    apply hDprod.congr
    filter_upwards [] with t
    ring
  have hDr : IntervalIntegrable (fun t => routePNativeLatePrimeMixedPrimitive ε t *
      routePLatePrimeRightVelocity t / routePLatePrimeIncrement t ^ 2) volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
    apply ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hD).congr
    apply ae_restrict_of_ae
    filter_upwards [routePLatePrimeRightVelocity_ae_eq] with t ht
    rw [ht]
  have hF : IntervalIntegrable (fun t => Real.exp ((1 / 2 - ε) * t) *
      routePNativeCriticalProfile t) volume a b :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      continuous_routePNativeCriticalProfile).intervalIntegrable a b
  have hint : IntervalIntegrable (fun t => Real.exp ((1 / 2 - ε) * t) *
      routePNativeCriticalProfile t - routePNativeLatePrimeMixedPrimitive ε t *
        routePLatePrimeRightVelocity t / routePLatePrimeIncrement t ^ 2) volume a b := by
    simpa only [Pi.sub_def] using hF.sub hDr
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab
    ((hcalc ε).1.mono (show Icc a b ⊆ Ioi Tc from fun t ht => hca.trans_le ht.1))
    (fun t ht => (hcalc ε).2 t (hca.trans ht.1)) hint
  rw [intervalIntegral.integral_sub hF hDr] at hftc
  have hvel : (∫ t in a..b, routePNativeLatePrimeMixedPrimitive ε t *
      routePLatePrimeRightVelocity t / routePLatePrimeIncrement t ^ 2) =
      ∫ t in a..b, routePNativeLatePrimeMixedPrimitive ε t *
        routePLatePrimeVelocity t / routePLatePrimeIncrement t ^ 2 := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [routePLatePrimeRightVelocity_ae_eq] with t ht _
    rw [ht]
  rw [hvel] at hftc
  exact hftc.symm

end RHTower
