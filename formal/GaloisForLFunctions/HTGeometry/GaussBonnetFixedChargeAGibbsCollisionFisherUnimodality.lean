import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsCollisionFisherStepSigns
import Mathlib.Data.Nat.Find

/-!
# A complete finite-time shape classification for collision Fisher geometry

The fast-to-slow mass ratio decreases geometrically. Every mixed history
therefore crosses the turning threshold exactly once: strict increase may
precede the threshold, one plateau is possible, and strict decrease follows.
The global Fisher maximum is attained at a finite time. Missing sectors give
the identically zero history.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open Filter

private theorem source_mass_steps (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    (egbFixedChargeAGibbsCollisionSlowSourceMass n (m + 1) β E : ℝ) =
        (4 / 9 : ℝ) * (egbFixedChargeAGibbsCollisionSlowSourceMass n m β E : ℝ) ∧
    (egbFixedChargeAGibbsCollisionFastSourceMass n (m + 1) β E : ℝ) =
        (1 / 36 : ℝ) * (egbFixedChargeAGibbsCollisionFastSourceMass n m β E : ℝ) := by
  constructor
  · change (4 / 9 : ℝ) ^ ((m + 1) + 1) * egbFixedChargeAGibbsSlowModeEnergy n β E =
      (4 / 9 : ℝ) * ((4 / 9 : ℝ) ^ (m + 1) * egbFixedChargeAGibbsSlowModeEnergy n β E)
    rw [pow_succ (4 / 9 : ℝ) (m + 1)]
    ring
  · change (1 / 36 : ℝ) ^ ((m + 1) + 1) * egbFixedChargeAGibbsFastModeEnergy n β E =
      (1 / 36 : ℝ) * ((1 / 36 : ℝ) ^ (m + 1) * egbFixedChargeAGibbsFastModeEnergy n β E)
    rw [pow_succ (1 / 36 : ℝ) (m + 1)]
    ring

private theorem exists_turning_threshold (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) (hA : 0 < egbFixedChargeAGibbsSlowModeEnergy n β E) :
    ∃ m : ℕ, (egbFixedChargeAGibbsCollisionFastSourceMass n m β E : ℝ) ≤
      4 * (egbFixedChargeAGibbsCollisionSlowSourceMass n m β E : ℝ) := by
  let x0 : ℝ := (4 / 9 : ℝ) * egbFixedChargeAGibbsSlowModeEnergy n β E
  let y0 : ℝ := (1 / 36 : ℝ) * egbFixedChargeAGibbsFastModeEnergy n β E
  have hx0 : 0 < x0 := by dsimp [x0]; positivity
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 16) (by norm_num : (1 / 16 : ℝ) < 1)
  have ht : Tendsto (fun m : ℕ => y0 * (1 / 16 : ℝ) ^ m) atTop (nhds 0) := by
    simpa only [mul_zero] using hp.const_mul y0
  have he := Filter.Tendsto.eventually_lt_const (show (0 : ℝ) < 4 * x0 by positivity) ht
  obtain ⟨m, hm⟩ := he.exists
  have hfast : (egbFixedChargeAGibbsCollisionFastSourceMass n m β E : ℝ) =
      (4 / 9 : ℝ) ^ m * (y0 * (1 / 16 : ℝ) ^ m) := by
    change (1 / 36 : ℝ) ^ (m + 1) * egbFixedChargeAGibbsFastModeEnergy n β E =
      (4 / 9 : ℝ) ^ m * (((1 / 36 : ℝ) * egbFixedChargeAGibbsFastModeEnergy n β E) * (1 / 16 : ℝ) ^ m)
    rw [pow_succ (1 / 36 : ℝ) m,
      show (1 / 36 : ℝ) = (4 / 9 : ℝ) * (1 / 16 : ℝ) by norm_num, mul_pow]
    ring
  have hslow : (egbFixedChargeAGibbsCollisionSlowSourceMass n m β E : ℝ) =
      (4 / 9 : ℝ) ^ m * x0 := by
    change (4 / 9 : ℝ) ^ (m + 1) * egbFixedChargeAGibbsSlowModeEnergy n β E =
      (4 / 9 : ℝ) ^ m * ((4 / 9 : ℝ) * egbFixedChargeAGibbsSlowModeEnergy n β E)
    rw [pow_succ (4 / 9 : ℝ) m]
    ring
  refine ⟨m, le_of_lt ?_⟩
  rw [hfast, hslow]
  calc
    _ < (4 / 9 : ℝ) ^ m * (4 * x0) := mul_lt_mul_of_pos_left hm (by positivity)
    _ = _ := by ring

private theorem threshold_next_strict (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) (hA : 0 < egbFixedChargeAGibbsSlowModeEnergy n β E)
    (hm : (egbFixedChargeAGibbsCollisionFastSourceMass n m β E : ℝ) ≤
      4 * (egbFixedChargeAGibbsCollisionSlowSourceMass n m β E : ℝ)) :
    (egbFixedChargeAGibbsCollisionFastSourceMass n (m + 1) β E : ℝ) <
      4 * (egbFixedChargeAGibbsCollisionSlowSourceMass n (m + 1) β E : ℝ) := by
  have hx : 0 < (egbFixedChargeAGibbsCollisionSlowSourceMass n m β E : ℝ) := by
    change 0 < (4 / 9 : ℝ) ^ (m + 1) * egbFixedChargeAGibbsSlowModeEnergy n β E
    positivity
  rw [(source_mass_steps n m β E).1, (source_mass_steps n m β E).2]
  nlinarith

private theorem threshold_after (n p k : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) (hA : 0 < egbFixedChargeAGibbsSlowModeEnergy n β E)
    (hp : (egbFixedChargeAGibbsCollisionFastSourceMass n p β E : ℝ) ≤
      4 * (egbFixedChargeAGibbsCollisionSlowSourceMass n p β E : ℝ)) :
    (egbFixedChargeAGibbsCollisionFastSourceMass n (p + k + 1) β E : ℝ) <
      4 * (egbFixedChargeAGibbsCollisionSlowSourceMass n (p + k + 1) β E : ℝ) := by
  induction k with
  | zero => simpa using threshold_next_strict n p β E hA hp
  | succ k ih =>
      have h := threshold_next_strict n (p + k + 1) β E hA ih.le
      simpa only [Nat.add_assoc] using h

/-- Every history is flat zero or has one turning threshold, with strict growth before and strict decay afterward. -/
theorem egbFixedChargeAGibbsCollisionFisherValue_unimodal (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    if egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∨ egbFixedChargeAGibbsFastModeEnergy n β E = 0 then
      ∀ m : ℕ, egbFixedChargeAGibbsCollisionFisherValue n m β E = 0
    else ∃ p : ℕ,
      (∀ m : ℕ, m < p → egbFixedChargeAGibbsCollisionFisherValue n m β E <
        egbFixedChargeAGibbsCollisionFisherValue n (m + 1) β E) ∧
      egbFixedChargeAGibbsCollisionFisherValue n (p + 1) β E ≤
        egbFixedChargeAGibbsCollisionFisherValue n p β E ∧
      (∀ m : ℕ, p < m → egbFixedChargeAGibbsCollisionFisherValue n (m + 1) β E <
        egbFixedChargeAGibbsCollisionFisherValue n m β E) := by
  classical
  by_cases hz : egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∨ egbFixedChargeAGibbsFastModeEnergy n β E = 0
  · rw [if_pos hz]
    intro m
    exact (egbFixedChargeAGibbsCollisionFisherValue_zero_iff n m β E).mpr hz
  · rw [if_neg hz]
    have ha : egbFixedChargeAGibbsSlowModeEnergy n β E ≠ 0 := fun h => hz (Or.inl h)
    have hb : egbFixedChargeAGibbsFastModeEnergy n β E ≠ 0 := fun h => hz (Or.inr h)
    have hA := lt_of_le_of_ne (egbFixedChargeAGibbsSlowModeEnergy_nonneg n β E) (Ne.symm ha)
    have hB := lt_of_le_of_ne (egbFixedChargeAGibbsFastModeEnergy_nonneg n β E) (Ne.symm hb)
    have hex := exists_turning_threshold n β E hA
    let p : ℕ := Nat.find hex
    have hp : (egbFixedChargeAGibbsCollisionFastSourceMass n p β E : ℝ) ≤
        4 * (egbFixedChargeAGibbsCollisionSlowSourceMass n p β E : ℝ) := Nat.find_spec hex
    refine ⟨p, ?_, ?_, ?_⟩
    · intro m hm
      have hn := Nat.find_min hex hm
      exact (egbFixedChargeAGibbsCollisionFisherValue_increase_iff n m β E).mpr
        ⟨hA, hB, lt_of_not_ge hn⟩
    · apply le_of_not_gt
      intro h
      have ht := (egbFixedChargeAGibbsCollisionFisherValue_increase_iff n p β E).mp h
      linarith [ht.2.2]
    · intro m hm
      let k : ℕ := m - p - 1
      have he : m = p + k + 1 := by dsimp [k]; omega
      apply (egbFixedChargeAGibbsCollisionFisherValue_decrease_iff n m β E).mpr
      refine ⟨hA, hB, ?_⟩
      rw [he]
      exact threshold_after n p k β E hA hp

private theorem turning_maximum (f : ℕ → ℝ) (p : ℕ)
    (hbefore : ∀ m : ℕ, m < p → f m < f (m + 1))
    (hboundary : f (p + 1) ≤ f p)
    (hafter : ∀ m : ℕ, p < m → f (m + 1) < f m) : ∀ m : ℕ, f m ≤ f p := by
  have hprefix : ∀ k m : ℕ, m + k = p → f m ≤ f p := by
    intro k
    induction k with
    | zero =>
        intro m hm
        have he : m = p := by omega
        rw [he]
    | succ k ih =>
        intro m hm
        exact (hbefore m (by omega)).le.trans (ih (m + 1) (by omega))
  have hsuffix : ∀ k : ℕ, f (p + k) ≤ f p := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hstep : f ((p + k) + 1) ≤ f (p + k) := by
          by_cases hk : k = 0
          · simpa [hk] using hboundary
          · exact (hafter (p + k) (by omega)).le
        have he : p + (k + 1) = (p + k) + 1 := by omega
        rw [he]
        exact hstep.trans ih
  intro m
  by_cases hm : m ≤ p
  · exact hprefix (p - m) m (by omega)
  · have he : m = p + (m - p) := by omega
    rw [he]
    exact hsuffix (m - p)

/-- The collision Fisher value always attains its global maximum at a finite time. -/
theorem egbFixedChargeAGibbsCollisionFisherValue_peak_attained (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    ∃ p : ℕ, ∀ m : ℕ, egbFixedChargeAGibbsCollisionFisherValue n m β E ≤
      egbFixedChargeAGibbsCollisionFisherValue n p β E := by
  have h := egbFixedChargeAGibbsCollisionFisherValue_unimodal n β E
  by_cases hz : egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∨ egbFixedChargeAGibbsFastModeEnergy n β E = 0
  · rw [if_pos hz] at h
    refine ⟨0, ?_⟩
    intro m
    rw [h m, h 0]
  · rw [if_neg hz] at h
    obtain ⟨p, hbefore, hboundary, hafter⟩ := h
    exact ⟨p, turning_maximum _ p hbefore hboundary hafter⟩

end
end GaloisForLFunctions.HTGeometry
