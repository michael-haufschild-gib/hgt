import GaloisForLFunctions.RHTower.RoutePLatePrimeIncrementJumps
import Mathlib.Topology.Order.LeftRightLim

/-!
# One-sided limits at the actual prime-removal clocks

The cumulative removal mass is a finite step sum on each finite window.
Its left limit omits the endpoint atom; its right limit includes it.
Subtracting from the continuous velocity primitive identifies the literal
increment's jump without imposing smoothness across a prime square.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace RHTower

private theorem primeClock_mem {p : ℕ} (hp : p.Prime) (t : ℝ) :
    p ∈ Nat.primesLE ⌊Real.exp t⌋₊ ↔ Real.log p ≤ t := by
  rw [Nat.mem_primesLE, and_iff_left hp,
    Nat.le_floor_iff (Real.exp_pos t).le, ← Real.log_le_iff_le_exp]
  exact_mod_cast hp.pos

/-- Freeze the removal primes only through a finite terminal clock. -/
theorem routePLatePrimeRemovalMass_eq_finite {s t : ℝ} (hst : s ≤ t) :
    routePLatePrimeRemovalMass s =
      ∑ p ∈ Nat.primesLE ⌊Real.exp (t / 2)⌋₊,
        if 2 * Real.log p ≤ s then criticalAbelLogProfile (Real.log p) / p else 0 := by
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
  rw [routePLatePrimeRemovalMass, ← hfilter, Finset.sum_filter]

private theorem step_right (τ c x : ℝ) :
    Tendsto (fun t : ℝ => if τ ≤ t then c else 0) (𝓝[Ici x] x)
      (𝓝 (if τ ≤ x then c else 0)) := by
  by_cases hτ : τ ≤ x
  · rw [if_pos hτ]
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (if_pos (hτ.trans ht)).symm
  · rw [if_neg hτ]
    apply tendsto_const_nhds.congr'
    filter_upwards [(eventually_lt_nhds (lt_of_not_ge hτ)).filter_mono
      nhdsWithin_le_nhds] with t ht
    exact (if_neg (not_le.mpr ht)).symm

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

/-- Removal mass takes its right-continuous value at every clock. -/
theorem continuousWithinAt_routePLatePrimeRemovalMass_right (x : ℝ) :
    ContinuousWithinAt routePLatePrimeRemovalMass (Ici x) x := by
  have hsum := tendsto_finsetSum (Nat.primesLE ⌊Real.exp ((x + 1) / 2)⌋₊)
    (fun p _ => step_right (2 * Real.log p)
      (criticalAbelLogProfile (Real.log p) / p) x)
  rw [← routePLatePrimeRemovalMass_eq_finite (show x ≤ x + 1 by linarith)] at hsum
  apply hsum.congr'
  filter_upwards [(eventually_lt_nhds (show x < x + 1 by linarith)).filter_mono
    nhdsWithin_le_nhds] with t ht
  exact (routePLatePrimeRemovalMass_eq_finite ht.le).symm

/-- The left limit removes precisely the prime at the endpoint. -/
theorem tendsto_routePLatePrimeRemovalMass_left_prime {q : ℕ} (hq : q.Prime) :
    Tendsto routePLatePrimeRemovalMass (𝓝[Iio (2 * Real.log q)] (2 * Real.log q))
      (𝓝 (routePLatePrimeRemovalMass (2 * Real.log q) -
        criticalAbelLogProfile (Real.log q) / q)) := by
  classical
  let P := Nat.primesLE ⌊Real.exp ((2 * Real.log q + 1) / 2)⌋₊
  have hqP : q ∈ P := (primeClock_mem hq _).mpr (by linarith)
  have hdiff : routePLatePrimeRemovalMass (2 * Real.log q) -
      (∑ p ∈ P, if 2 * Real.log p < 2 * Real.log q then
        criticalAbelLogProfile (Real.log p) / p else 0) =
      criticalAbelLogProfile (Real.log q) / q := by
    rw [routePLatePrimeRemovalMass_eq_finite
      (show 2 * Real.log (q : ℝ) ≤ 2 * Real.log q + 1 by linarith)]
    change (∑ p ∈ P, if 2 * Real.log p ≤ 2 * Real.log q then
        criticalAbelLogProfile (Real.log p) / p else 0) - _ = _
    rw [← Finset.sum_sub_distrib]
    rw [Finset.sum_eq_single q]
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
  have hsum := tendsto_finsetSum P (fun p _ =>
    step_left (2 * Real.log p) (criticalAbelLogProfile (Real.log p) / p)
      (2 * Real.log q))
  have hval : (∑ p ∈ P, if 2 * Real.log p < 2 * Real.log q then
      criticalAbelLogProfile (Real.log p) / p else 0) =
      routePLatePrimeRemovalMass (2 * Real.log q) -
        criticalAbelLogProfile (Real.log q) / q := by linarith [hdiff]
  rw [hval] at hsum
  apply hsum.congr'
  filter_upwards [(eventually_lt_nhds
    (show 2 * Real.log (q : ℝ) < 2 * Real.log q + 1 by linarith)).filter_mono
      nhdsWithin_le_nhds] with t ht
  exact (routePLatePrimeRemovalMass_eq_finite ht.le).symm

/-- The integrated continuous velocity is continuous at each positive clock. -/
theorem continuousAt_routePLatePrimeVelocityPrimitive {x : ℝ} (hx : 0 < x) :
    ContinuousAt (fun t => ∫ s in (0 : ℝ)..t, routePLatePrimeVelocity s) x := by
  have hT : 0 ≤ x + 1 := by linarith
  have hi : IntervalIntegrable routePLatePrimeVelocity volume 0 (x + 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr
      (integrableOn_routePLatePrimeVelocity_Ioc (x + 1))
  have hc : ContinuousOn (fun t => ∫ s in (0 : ℝ)..t, routePLatePrimeVelocity s)
      (Icc 0 (x + 1)) := by
    simpa only [uIcc_of_le hT] using
      intervalIntegral.continuousOn_primitive_interval' hi
        (left_mem_uIcc : (0 : ℝ) ∈ uIcc 0 (x + 1))
  exact hc.continuousAt (Icc_mem_nhds hx (by linarith))

/-- The actual increment, including removals, is right-continuous. -/
theorem continuousWithinAt_routePLatePrimeIncrement_right {x : ℝ} (hx : 0 < x) :
    ContinuousWithinAt routePLatePrimeIncrement (Ici x) x := by
  have h := ((continuousAt_routePLatePrimeVelocityPrimitive hx).tendsto.mono_left
      nhdsWithin_le_nhds).sub (continuousWithinAt_routePLatePrimeRemovalMass_right x)
  rw [← routePLatePrimeIncrement_eq_velocity_sub_removals hx.le] at h
  apply h.congr'
  filter_upwards [(eventually_gt_nhds hx).filter_mono nhdsWithin_le_nhds] with t ht
  exact (routePLatePrimeIncrement_eq_velocity_sub_removals ht.le).symm

/-- Exact left limit at a physical prime-square removal. -/
theorem tendsto_routePLatePrimeIncrement_left_prime {p : ℕ} (hp : p.Prime) :
    Tendsto routePLatePrimeIncrement (𝓝[Iio (2 * Real.log p)] (2 * Real.log p))
      (𝓝 (routePLatePrimeIncrement (2 * Real.log p) +
        criticalAbelLogProfile (Real.log p) / p)) := by
  have hx : 0 < 2 * Real.log (p : ℝ) := by
    have := Real.log_pos (show (1 : ℝ) < p by exact_mod_cast hp.one_lt)
    linarith
  have h := ((continuousAt_routePLatePrimeVelocityPrimitive hx).tendsto.mono_left
      nhdsWithin_le_nhds).sub (tendsto_routePLatePrimeRemovalMass_left_prime hp)
  have hval : (∫ s in (0 : ℝ)..(2 * Real.log p), routePLatePrimeVelocity s) -
      (routePLatePrimeRemovalMass (2 * Real.log p) -
        criticalAbelLogProfile (Real.log p) / p) =
      routePLatePrimeIncrement (2 * Real.log p) +
        criticalAbelLogProfile (Real.log p) / p := by
    rw [routePLatePrimeIncrement_eq_velocity_sub_removals hx.le]
    ring
  rw [hval] at h
  apply h.congr'
  filter_upwards [(eventually_gt_nhds hx).filter_mono nhdsWithin_le_nhds] with t ht
  exact (routePLatePrimeIncrement_eq_velocity_sub_removals ht.le).symm

theorem routePLatePrimeIncrement_rightLim {x : ℝ} (hx : 0 < x) :
    Function.rightLim routePLatePrimeIncrement x = routePLatePrimeIncrement x :=
  (continuousWithinAt_routePLatePrimeIncrement_right hx).rightLim_eq

theorem routePLatePrimeIncrement_leftLim_prime {p : ℕ} (hp : p.Prime) :
    Function.leftLim routePLatePrimeIncrement (2 * Real.log p) =
      routePLatePrimeIncrement (2 * Real.log p) + criticalAbelLogProfile (Real.log p) / p :=
  leftLim_eq_of_tendsto (tendsto_routePLatePrimeIncrement_left_prime hp)

end RHTower
