import GaloisForLFunctions.RHTower.RoutePLatePrimeIncrementJumps

/-!
# The literal right velocity, including entry and removal clocks

The right-derivative representative uses `[log p, 2 log p)`. It agrees
almost everywhere with the admitted continuous velocity, whose opposite
endpoint convention was chosen for the integral decomposition.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace RHTower

def routePLatePrimeRightVelocityAtom (p : ℕ) (t : ℝ) : ℝ :=
  (Ico (Real.log p) (2 * Real.log p)).indicator
    (fun s => criticalAbelLogVelocity (s - Real.log p) / p) t

def routePLatePrimeRightVelocity (t : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊Real.exp t⌋₊, routePLatePrimeRightVelocityAtom p t

private def profileAtom (p : ℕ) (t : ℝ) : ℝ :=
  if t < 2 * Real.log p then criticalAbelLogProfile (t - Real.log p) / p else 0

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

private theorem increment_eq_finite {s t : ℝ} (hst : s ≤ t) :
    routePLatePrimeIncrement s =
      ∑ p ∈ Nat.primesLE ⌊Real.exp t⌋₊, profileAtom p s := by
  classical
  calc
    _ = ∑ p ∈ Nat.primesLE ⌊Real.exp s⌋₊, profileAtom p s := by
      rw [routePLatePrimeIncrement, criticalLogLatePrimes, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p _
      unfold profileAtom
      have heq : s / 2 < Real.log (p : ℝ) ↔ s < 2 * Real.log p := by
        constructor <;> intro h <;> linarith
      simp only [heq]
    _ = _ := by
      apply Finset.sum_subset (primeClock_subset hst)
      intro p hp hn
      have hprime := (Nat.mem_primesLE.mp hp).2
      have hs : s < Real.log (p : ℝ) :=
        lt_of_not_ge (fun h => hn ((primeClock_mem hprime s).mpr h))
      simp [profileAtom, criticalAbelLogProfile_zero_of_nonpos (sub_nonpos.mpr hs.le)]

/-- The right velocity admits the same exact finite terminal freezing. -/
theorem routePLatePrimeRightVelocity_eq_finite {s t : ℝ} (hst : s ≤ t) :
    routePLatePrimeRightVelocity s =
      ∑ p ∈ Nat.primesLE ⌊Real.exp t⌋₊, routePLatePrimeRightVelocityAtom p s := by
  unfold routePLatePrimeRightVelocity
  apply Finset.sum_subset (primeClock_subset hst)
  intro p hp hn
  have hprime := (Nat.mem_primesLE.mp hp).2
  have hs : ¬ Real.log (p : ℝ) ≤ s := fun h => hn ((primeClock_mem hprime s).mpr h)
  simp only [routePLatePrimeRightVelocityAtom, Set.indicator_apply, Set.mem_Ico,
    hs, false_and, if_false]

private theorem profileAtom_hasDeriv_right (p : ℕ) (t : ℝ) :
    HasDerivWithinAt (profileAtom p) (routePLatePrimeRightVelocityAtom p t) (Ioi t) t := by
  by_cases hremoved : t < 2 * Real.log (p : ℝ)
  · by_cases hborn : Real.log (p : ℝ) ≤ t
    · have hshift : HasDerivWithinAt
          (fun s : ℝ => criticalAbelLogProfile (s - Real.log p) / p)
          (criticalAbelLogVelocity (t - Real.log p) / p) (Ioi t) t := by
        have h := (criticalAbelLogProfile_hasDeriv_right (sub_nonneg.mpr hborn)).comp t
          ((hasDerivAt_id t).sub_const (Real.log p)).hasDerivWithinAt
          (show MapsTo (fun s : ℝ => s - Real.log p) (Ioi t) (Ioi (t - Real.log p)) from
            fun s hs => by
              change t < s at hs
              change t - Real.log p < s - Real.log p
              linarith)
        simpa only [Function.comp_def, id_eq, mul_one] using h.div_const (p : ℝ)
      rw [routePLatePrimeRightVelocityAtom, Set.indicator_of_mem
        (show t ∈ Ico (Real.log p) (2 * Real.log p) from ⟨hborn, hremoved⟩)]
      apply hshift.congr_of_eventuallyEq
      · filter_upwards [(eventually_lt_nhds hremoved).filter_mono nhdsWithin_le_nhds] with s hs
        exact if_pos hs
      · exact if_pos hremoved
    · have hbefore : t < Real.log (p : ℝ) := lt_of_not_ge hborn
      rw [routePLatePrimeRightVelocityAtom, Set.indicator_of_notMem
        (show t ∉ Ico (Real.log p) (2 * Real.log p) from fun h => hborn h.1)]
      apply (hasDerivWithinAt_const t (Ioi t) (0 : ℝ)).congr_of_eventuallyEq
      · filter_upwards [(eventually_lt_nhds hbefore).filter_mono nhdsWithin_le_nhds] with s hs
        simp [profileAtom, criticalAbelLogProfile_zero_of_nonpos (sub_nonpos.mpr hs.le)]
      · simp [profileAtom, criticalAbelLogProfile_zero_of_nonpos (sub_nonpos.mpr hbefore.le)]
  · rw [routePLatePrimeRightVelocityAtom, Set.indicator_of_notMem
      (show t ∉ Ico (Real.log p) (2 * Real.log p) from fun h => hremoved h.2)]
    apply (hasDerivWithinAt_const t (Ioi t) (0 : ℝ)).congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin] with s hs
      have hnot : ¬ s < 2 * Real.log (p : ℝ) := by
        have hle := le_of_not_gt hremoved
        exact not_lt.mpr (hle.trans hs.le)
      exact if_neg hnot
    · exact if_neg hremoved

/-- The literal right derivative holds at every clock, including births and
removals. This is stronger than an a.e. derivative identity. -/
theorem routePLatePrimeIncrement_hasDeriv_right (t : ℝ) :
    HasDerivWithinAt routePLatePrimeIncrement (routePLatePrimeRightVelocity t) (Ioi t) t := by
  have hs := HasDerivWithinAt.fun_sum
    (u := Nat.primesLE ⌊Real.exp (t + 1)⌋₊)
    (fun p _ => profileAtom_hasDeriv_right p t)
  rw [← routePLatePrimeRightVelocity_eq_finite (show t ≤ t + 1 by linarith)] at hs
  apply hs.congr_of_eventuallyEq
  · filter_upwards [(eventually_lt_nhds (show t < t + 1 by linarith)).filter_mono
      nhdsWithin_le_nhds] with s hs'
    exact increment_eq_finite hs'.le
  · exact increment_eq_finite (show t ≤ t + 1 by linarith)

/-- Opposite endpoint conventions differ only at the countable arithmetic
entry/removal clocks. Every integral therefore retains the admitted velocity. -/
theorem routePLatePrimeRightVelocity_ae_eq :
    routePLatePrimeRightVelocity =ᵐ[volume] routePLatePrimeVelocity := by
  filter_upwards [(Set.countable_range (fun n : ℕ => Real.log (n : ℝ))).ae_notMem volume,
    (Set.countable_range (fun n : ℕ => 2 * Real.log (n : ℝ))).ae_notMem volume] with t hentry hexit
  unfold routePLatePrimeRightVelocity routePLatePrimeVelocity
  apply Finset.sum_congr rfl
  intro p _
  have hne : t ≠ Real.log (p : ℝ) := fun h => hentry ⟨p, h.symm⟩
  have hne' : t ≠ 2 * Real.log (p : ℝ) := fun h => hexit ⟨p, h.symm⟩
  have hi : t ∈ Ico (Real.log p) (2 * Real.log p) ↔
      t ∈ Ioc (Real.log p) (2 * Real.log p) := by
    constructor
    · rintro ⟨hlo, hhi⟩
      exact ⟨lt_of_le_of_ne hlo hne.symm, hhi.le⟩
    · rintro ⟨hlo, hhi⟩
      exact ⟨hlo.le, lt_of_le_of_ne hhi hne'⟩
  simp only [routePLatePrimeRightVelocityAtom, routePLatePrimeVelocityAtom,
    Set.indicator_apply, hi]

theorem integrableOn_routePLatePrimeRightVelocity_Ioc (t : ℝ) :
    IntegrableOn routePLatePrimeRightVelocity (Ioc (0 : ℝ) t) :=
  (integrableOn_routePLatePrimeVelocity_Ioc t).congr
    (ae_restrict_of_ae routePLatePrimeRightVelocity_ae_eq.symm)

end RHTower
