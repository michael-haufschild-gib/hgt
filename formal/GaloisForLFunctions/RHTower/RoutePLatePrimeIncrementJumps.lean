import GaloisForLFunctions.RHTower.RoutePNativeLatePrimeMixedAdmission

/-!
# The continuous velocity and removal jumps of the actual prime increment

The velocity uses an a.e. representative on `(log p, 2 log p]`.
The removal mass is retained explicitly, including the value at every
prime-square clock. No smoothness across those clocks is asserted.
-/

noncomputable section
open MeasureTheory Set Finset

namespace RHTower

/-- A prime channel's continuous velocity before its removal. -/
def routePLatePrimeVelocityAtom (p : ℕ) (t : ℝ) : ℝ :=
  (Ioc (Real.log p) (2 * Real.log p)).indicator
    (fun s => criticalAbelLogVelocity (s - Real.log p) / p) t

/-- Continuous part of the native increment's distributional derivative. -/
def routePLatePrimeVelocity (t : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊Real.exp t⌋₊, routePLatePrimeVelocityAtom p t

/-- Cumulative removal mass at the actual prime-square clocks. -/
def routePLatePrimeRemovalMass (t : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊Real.exp (t / 2)⌋₊, criticalAbelLogProfile (Real.log p) / p

theorem measurable_routePLatePrimeVelocityAtom (p : ℕ) :
    Measurable (routePLatePrimeVelocityAtom p) := by
  have hv : Measurable criticalAbelLogVelocity :=
    (measurable_criticalAbelLogDefect.div_const 2).sub
      (measurable_const.mul measurable_criticalAbelLogProfile)
  exact ((hv.comp (measurable_id.sub_const (Real.log p))).div_const (p : ℝ)).indicator
    measurableSet_Ioc

theorem measurable_routePLatePrimeVelocity : Measurable routePLatePrimeVelocity := by
  have hm : Measurable (fun z : ℝ × ℕ =>
      ∑ p ∈ Nat.primesLE z.2, routePLatePrimeVelocityAtom p z.1) := by
    apply measurable_from_prod_countable_left
    intro n
    dsimp only
    exact Finset.measurable_sum _ (fun p _ => measurable_routePLatePrimeVelocityAtom p)
  exact hm.comp (measurable_id.prodMk Real.measurable_exp.nat_floor)

private theorem primeClock_mem {p : ℕ} (hp : p.Prime) (t : ℝ) :
    p ∈ Nat.primesLE ⌊Real.exp t⌋₊ ↔ Real.log p ≤ t := by
  rw [Nat.mem_primesLE, and_iff_left hp,
    Nat.le_floor_iff (Real.exp_pos t).le, ← Real.log_le_iff_le_exp]
  exact_mod_cast hp.pos

private theorem primeClock_subset {s t : ℝ} (hst : s ≤ t) :
    Nat.primesLE ⌊Real.exp s⌋₊ ⊆ Nat.primesLE ⌊Real.exp t⌋₊ := by
  intro p hp
  have hprime := (Nat.mem_primesLE.mp hp).2
  exact (primeClock_mem hprime t).mpr (((primeClock_mem hprime s).mp hp).trans hst)

/-- Every individual velocity atom is absolutely integrable. -/
theorem integrable_routePLatePrimeVelocityAtom {p : ℕ} (hp : p.Prime) :
    Integrable (routePLatePrimeVelocityAtom p) := by
  have hl : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hv : IntervalIntegrable criticalAbelLogVelocity volume 0 (Real.log p) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hl).mpr
      (integrableOn_criticalAbelLogVelocity.mono_set (fun _ hs => hs.1))
  have hs : IntervalIntegrable (fun t : ℝ => criticalAbelLogVelocity (t - Real.log p))
      volume (Real.log p) (2 * Real.log p) := by
    simpa only [zero_add, two_mul] using hv.comp_sub_right (Real.log p)
  unfold routePLatePrimeVelocityAtom
  exact (integrable_indicator_iff measurableSet_Ioc).mpr
    (((intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp hs).div_const p)

private theorem velocityAtom_integral {p : ℕ} (hp : p.Prime) {t : ℝ}
    (hpt : Real.log p ≤ t) :
    (∫ s in Ioc (0 : ℝ) t, routePLatePrimeVelocityAtom p s) =
      criticalAbelLogProfile (min (t - Real.log p) (Real.log p)) / p := by
  have hl : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hset : Ioc (Real.log p) (2 * Real.log p) ∩ Ioc (0 : ℝ) t =
      Ioc (Real.log p) (min t (2 * Real.log p)) := by
    ext s
    constructor
    · rintro ⟨⟨hps, hs2⟩, ⟨_, hst⟩⟩
      exact ⟨hps, le_min hst hs2⟩
    · rintro ⟨hps, hsmin⟩
      exact ⟨⟨hps, (le_min_iff.mp hsmin).2⟩,
        ⟨hl.trans hps, (le_min_iff.mp hsmin).1⟩⟩
  have hmin : min t (2 * Real.log p) - Real.log p =
      min (t - Real.log p) (Real.log p) := by
    by_cases ht : t ≤ 2 * Real.log p
    · rw [min_eq_left ht, min_eq_left (by linarith)]
    · rw [min_eq_right (le_of_not_ge ht), min_eq_right (by linarith)]
      ring
  unfold routePLatePrimeVelocityAtom
  rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
    hset, ← intervalIntegral.integral_of_le (le_min hpt (by linarith)),
    intervalIntegral.integral_div, intervalIntegral.integral_comp_sub_right,
    sub_self, hmin,
    criticalAbelLogVelocity_integral (le_min (sub_nonneg.mpr hpt) hl.le)]

/-- The moving prime set can be frozen through a finite terminal clock. -/
theorem routePLatePrimeVelocity_eq_finite {s t : ℝ} (hst : s ≤ t) :
    routePLatePrimeVelocity s =
      ∑ p ∈ Nat.primesLE ⌊Real.exp t⌋₊, routePLatePrimeVelocityAtom p s := by
  unfold routePLatePrimeVelocity
  apply Finset.sum_subset (primeClock_subset hst)
  intro p hp hnot
  have hprime := (Nat.mem_primesLE.mp hp).2
  have hn : ¬ Real.log (p : ℝ) < s := by
    intro h
    exact hnot ((primeClock_mem hprime s).mpr h.le)
  simp only [routePLatePrimeVelocityAtom, Set.indicator_apply, Set.mem_Ioc, hn, false_and,
    if_false]

/-- The literal continuous velocity is admitted on each finite positive window. -/
theorem integrableOn_routePLatePrimeVelocity_Ioc (t : ℝ) :
    IntegrableOn routePLatePrimeVelocity (Ioc (0 : ℝ) t) := by
  have hi : Integrable (fun s => ∑ p ∈ Nat.primesLE ⌊Real.exp t⌋₊,
      routePLatePrimeVelocityAtom p s) := by
    apply integrable_finsetSum
    intro p hp
    exact integrable_routePLatePrimeVelocityAtom (Nat.mem_primesLE.mp hp).2
  exact hi.integrableOn.congr_fun
    (fun s hs => (routePLatePrimeVelocity_eq_finite hs.2).symm) measurableSet_Ioc

private theorem continuousVelocity_integral {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t, routePLatePrimeVelocity s) =
      ∑ p ∈ Nat.primesLE ⌊Real.exp t⌋₊,
        criticalAbelLogProfile (min (t - Real.log p) (Real.log p)) / p := by
  rw [intervalIntegral.integral_of_le ht]
  calc
    _ = ∫ s in Ioc (0 : ℝ) t,
        ∑ p ∈ Nat.primesLE ⌊Real.exp t⌋₊, routePLatePrimeVelocityAtom p s := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro s hs
      exact routePLatePrimeVelocity_eq_finite hs.2
    _ = ∑ p ∈ Nat.primesLE ⌊Real.exp t⌋₊,
        ∫ s in Ioc (0 : ℝ) t, routePLatePrimeVelocityAtom p s := by
      apply integral_finsetSum
      intro p hp
      exact (integrable_routePLatePrimeVelocityAtom (Nat.mem_primesLE.mp hp).2).integrableOn
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      have hprime := (Nat.mem_primesLE.mp hp).2
      exact velocityAtom_integral hprime ((primeClock_mem hprime t).mp hp)

/-- Exact decomposition into integrated continuous velocity and all removed
prime atoms. It includes every prime-square endpoint. -/
theorem routePLatePrimeIncrement_eq_velocity_sub_removals {t : ℝ} (ht : 0 ≤ t) :
    routePLatePrimeIncrement t =
      (∫ s in (0 : ℝ)..t, routePLatePrimeVelocity s) - routePLatePrimeRemovalMass t := by
  classical
  have hremoved : (Nat.primesLE ⌊Real.exp t⌋₊).filter
      (fun p : ℕ => ¬ t / 2 < Real.log p) = Nat.primesLE ⌊Real.exp (t / 2)⌋₊ := by
    ext p
    by_cases hp : p.Prime
    · simp only [Finset.mem_filter, primeClock_mem hp, not_lt]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨h.trans (by linarith), h⟩
    · simp [Nat.mem_primesLE, hp]
  have hsplit : (∑ p ∈ Nat.primesLE ⌊Real.exp t⌋₊,
        criticalAbelLogProfile (min (t - Real.log p) (Real.log p)) / p) =
      routePLatePrimeIncrement t + routePLatePrimeRemovalMass t := by
    rw [routePLatePrimeIncrement, criticalLogLatePrimes, routePLatePrimeRemovalMass,
      ← hremoved, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : t / 2 < Real.log p
    · rw [if_pos hp, if_neg (not_not.mpr hp), add_zero, min_eq_left (by linarith)]
    · rw [if_neg hp, if_pos hp, zero_add, min_eq_right (by linarith)]
  rw [continuousVelocity_integral ht, hsplit]
  ring

end RHTower
