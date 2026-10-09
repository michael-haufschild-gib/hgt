import GaloisForLFunctions.RHTower.WeilLogShiftDiffuseImpulse
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Almost-everywhere failure within arbitrary observation tolerances

A nonempty positive interval of one-coordinate errors fits any positive
tolerance at that coordinate. Almost every such error gives unbounded
moment tails and signed nonsummability at every real shift, with all other
observations exact. Positive finite interval volume makes the claim
nonvacuous. The statement concerns restricted Lebesgue measure on amplitudes.
-/

open Filter MeasureTheory Set Topology Real
open scoped BoundedContinuousFunction

namespace RHTower

open WeilExcess

/-- A positive tolerance at one sufficiently late coordinate supports
almost-everywhere divergence, even when all other tolerances vanish. -/
theorem exists_weilLogShiftPrecision_ae_impulse :
    ∃ K : ℕ, ∀ (center : ℕ →ᵇ ℝ) (ε : ℕ → ℝ), (∀ j, 0 ≤ ε j) →
      ∀ M k : ℕ, K ≤ k → M ≤ k → 0 < ε k →
        0 < volume (Ioo 0 (ε k)) ∧ volume (Ioo 0 (ε k)) < ⊤ ∧
        ∀ᵐ t ∂(volume.restrict (Ioo 0 (ε k))),
          center k < weilLogShiftRecoveryImpulseHistory center k t k ∧
          (∀ j : ℕ, j ≠ k → weilLogShiftRecoveryImpulseHistory center k t j = center j) ∧
          (∀ j : ℕ, |weilLogShiftRecoveryImpulseHistory center k t j - center j| ≤ ε j) ∧
          (∀ j : ℕ, j < M → weilLogShiftRecoveryImpulseHistory center k t j = center j) ∧
          WeilLogShiftUniformNowhereBounded (weilLogShiftRecoveryImpulseHistory center k t) ∧
          ∀ y : ℝ, ¬ Summable
            (weilLogShiftRecoveryMoment y (weilLogShiftRecoveryImpulseHistory center k t)) := by
  obtain ⟨K, hK⟩ := exists_weilLogShiftRecoveryImpulse_ae_divergence
  refine ⟨K, fun center ε hε M k hkK hkM hkε => ?_⟩
  have hvol : 0 < volume (Ioo 0 (ε k)) ∧ volume (Ioo 0 (ε k)) < ⊤ := by
    rw [Real.volume_Ioo, sub_zero]
    exact ⟨ENNReal.ofReal_pos.mpr hkε, ENNReal.ofReal_lt_top⟩
  refine ⟨hvol.1, hvol.2, ?_⟩
  have hmem : ∀ᵐ t ∂(volume.restrict (Ioo 0 (ε k))), 0 < t ∧ t < ε k :=
    ae_restrict_mem measurableSet_Ioo
  have hgood := hK center k hkK (volume.restrict (Ioo 0 (ε k)))
  filter_upwards [hmem, hgood] with t ht hlarge
  refine ⟨?_, ?_, ?_, ?_, hlarge.1, hlarge.2⟩
  · rw [weilLogShiftRecoveryImpulseHistory_apply, if_pos rfl]
    linarith [ht.1]
  · intro j hj
    rw [weilLogShiftRecoveryImpulseHistory_apply, if_neg hj, add_zero]
  · intro j
    by_cases hj : j = k
    · subst j
      rw [weilLogShiftRecoveryImpulseHistory_apply, if_pos rfl,
        add_sub_cancel_left, abs_of_pos ht.1]
      exact ht.2.le
    · rw [weilLogShiftRecoveryImpulseHistory_apply, if_neg hj, add_zero, sub_self, abs_zero]
      exact hε j
  · intro j hj
    rw [weilLogShiftRecoveryImpulseHistory_apply, if_neg (by omega : j ≠ k), add_zero]

/-- Every positive precision profile and finite exact prefix allows a
single strictly upward error whose permitted amplitudes almost all give
global unboundedness and signed nonsummability; every other observation is exact. -/
theorem exists_weilLogShiftArbitraryPrecision_ae_single_error
    (center : ℕ →ᵇ ℝ) (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j) (M : ℕ) :
    ∃ k : ℕ, M ≤ k ∧ 0 < volume (Ioo 0 (ε k)) ∧ volume (Ioo 0 (ε k)) < ⊤ ∧
      ∀ᵐ t ∂(volume.restrict (Ioo 0 (ε k))),
        center k < weilLogShiftRecoveryImpulseHistory center k t k ∧
        (∀ j : ℕ, j ≠ k → weilLogShiftRecoveryImpulseHistory center k t j = center j) ∧
        (∀ j : ℕ, |weilLogShiftRecoveryImpulseHistory center k t j - center j| ≤ ε j) ∧
        (∀ j : ℕ, j < M → weilLogShiftRecoveryImpulseHistory center k t j = center j) ∧
        WeilLogShiftUniformNowhereBounded (weilLogShiftRecoveryImpulseHistory center k t) ∧
        ∀ y : ℝ, ¬ Summable
          (weilLogShiftRecoveryMoment y (weilLogShiftRecoveryImpulseHistory center k t)) := by
  obtain ⟨K, hK⟩ := exists_weilLogShiftPrecision_ae_impulse
  refine ⟨max K M, le_max_right _ _, ?_⟩
  exact hK center ε (fun j => (hε j).le) M (max K M)
    (le_max_left _ _) (le_max_right _ _) (hε _)

end RHTower
