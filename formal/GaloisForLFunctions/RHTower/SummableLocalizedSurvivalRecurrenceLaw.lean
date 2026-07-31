import GaloisForLFunctions.RHTower.SummablePurePointSurvivalEscapeReturnLaw

/-!
# Countably infinite localized survival recurrence

This file composes countable pure-point survival recurrence with an external
spectral-tail certificate.  A finite visible head determines the projective
phase exponent; the complete infinite complement enters only through its
certified mass.

The result is the precise infinite-volume interface for localization
theorems.  It does not assume that a named Hamiltonian or random ensemble
supplies the tail certificate.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- A certified localized-survival budget replaces the exact countable tail
by any proved upper bound. -/
def summableLocalizedSurvivalRecurrenceBudget
    (p : ℕ → ℝ) (M Q : ℕ) (tailBound : ℝ) : ℝ :=
  (2 * Real.pi / (Q + 1 : ℝ)) ^ 2 *
      ∑ k ∈ Finset.range (M - 1), p (k + 1) +
    4 * tailBound

theorem summablePurePointSurvivalRecurrenceBudget_le_localized
    (p : ℕ → ℝ) (M Q : ℕ) (tailBound : ℝ)
    (htail :
      summablePurePointSurvivalTail p M ≤ tailBound) :
    summablePurePointSurvivalRecurrenceBudget p M Q ≤
      summableLocalizedSurvivalRecurrenceBudget p M Q tailBound := by
  unfold summablePurePointSurvivalRecurrenceBudget
    summableLocalizedSurvivalRecurrenceBudget
  exact add_le_add le_rfl
    (mul_le_mul_of_nonneg_left htail (by norm_num : (0 : ℝ) ≤ 4))

/--
Every certified tail bound gives a quantitative countable survival return.
Only the `M - 1` projective gaps in the visible head enter the deadline.
-/
theorem exists_summableLocalizedSurvival_recurrence
    (p omega : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (hsum : Summable p) (htotal : ∑' k, p k = 1)
    (M Q : ℕ) (hM : 1 ≤ M) (tailBound : ℝ)
    (htail :
      summablePurePointSurvivalTail p M ≤ tailBound) :
    ∃ n : ℕ, 0 < n ∧ n ≤ (Q + 1) ^ (M - 1) ∧
      summablePurePointSurvivalDeviation p omega n ≤
        summableLocalizedSurvivalRecurrenceBudget
          p M Q tailBound := by
  obtain ⟨n, hn0, hnQ, hreturn⟩ :=
    exists_summablePurePointSurvival_recurrence_quantitative
      p omega hp hsum htotal M Q hM
  exact
    ⟨n, hn0, hnQ,
      hreturn.trans
        (summablePurePointSurvivalRecurrenceBudget_le_localized
          p M Q tailBound htail)⟩

/--
If the visible head contains at most `V` modes, the countably infinite
packet returns by the localization-volume deadline `(Q + 1)^(V - 1)`.
-/
theorem exists_summableLocalizedSurvival_volume_recurrence
    (p omega : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (hsum : Summable p) (htotal : ∑' k, p k = 1)
    (M Q V : ℕ) (hM : 1 ≤ M) (hMV : M ≤ V)
    (tailBound : ℝ)
    (htail :
      summablePurePointSurvivalTail p M ≤ tailBound) :
    ∃ n : ℕ, 0 < n ∧ n ≤ (Q + 1) ^ (V - 1) ∧
      summablePurePointSurvivalDeviation p omega n ≤
        summableLocalizedSurvivalRecurrenceBudget
          p M Q tailBound := by
  obtain ⟨n, hn0, hnM, hreturn⟩ :=
    exists_summableLocalizedSurvival_recurrence
      p omega hp hsum htotal M Q hM tailBound htail
  have hexponent : M - 1 ≤ V - 1 :=
    Nat.sub_le_sub_right hMV 1
  have hclock :
      (Q + 1) ^ (M - 1) ≤ (Q + 1) ^ (V - 1) :=
    Nat.pow_le_pow_right (Nat.succ_pos Q) hexponent
  exact ⟨n, hn0, hnM.trans hclock, hreturn⟩

/--
**Countably infinite localization-volume escape--return law.**

At every certified localization tail and visible-volume bound, either the
local survival record never exits its certified neighborhood, or an exit is
followed strictly later by a return before a clock depending on visible
volume rather than countable ambient support.
-/
theorem summableLocalizedSurvival_neverExits_or_postExit_return
    (p omega : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (hsum : Summable p) (htotal : ∑' k, p k = 1)
    (M Q V : ℕ) (hM : 1 ≤ M) (hMV : M ≤ V)
    (tailBound : ℝ)
    (htail :
      summablePurePointSurvivalTail p M ≤ tailBound)
    (guardTime : ℝ) (hguard : 0 < guardTime) :
    (∀ t : ℝ, 0 ≤ t →
      summablePurePointSurvivalDeviation p omega t ≤
        summableLocalizedSurvivalRecurrenceBudget
          p M Q tailBound) ∨
    ∃ exitTime : ℝ, ∃ n : ℕ,
      0 ≤ exitTime ∧
      0 < n ∧ n ≤ (Q + 1) ^ (V - 1) ∧
      summableLocalizedSurvivalRecurrenceBudget p M Q tailBound <
        summablePurePointSurvivalDeviation p omega exitTime ∧
      exitTime < (n : ℝ) * (exitTime + guardTime) ∧
      summablePurePointSurvivalDeviation p omega
          ((n : ℝ) * (exitTime + guardTime)) ≤
        summableLocalizedSurvivalRecurrenceBudget
          p M Q tailBound := by
  classical
  by_cases hnever :
      ∀ t : ℝ, 0 ≤ t →
        summablePurePointSurvivalDeviation p omega t ≤
          summableLocalizedSurvivalRecurrenceBudget
            p M Q tailBound
  · exact Or.inl hnever
  · right
    push Not at hnever
    obtain ⟨exitTime, hexitTime, hexit⟩ := hnever
    have hbudget :=
      summablePurePointSurvivalRecurrenceBudget_le_localized
        p M Q tailBound htail
    have hexitExact :
        summablePurePointSurvivalRecurrenceBudget p M Q <
          summablePurePointSurvivalDeviation p omega exitTime :=
      hbudget.trans_lt hexit
    obtain
      ⟨n, hn0, hnM, hpost, _hphysicalDeadline, _hexit, hreturn⟩ :=
      exists_summablePurePointSurvival_postExit_recurrence
        p omega hp hsum htotal M Q hM
        exitTime guardTime hexitTime hguard hexitExact
    have hexponent : M - 1 ≤ V - 1 :=
      Nat.sub_le_sub_right hMV 1
    have hclock :
        (Q + 1) ^ (M - 1) ≤ (Q + 1) ^ (V - 1) :=
      Nat.pow_le_pow_right (Nat.succ_pos Q) hexponent
    exact
      ⟨exitTime, n, hexitTime, hn0, hnM.trans hclock,
        hexit, hpost, hreturn.trans hbudget⟩

end RHTower
