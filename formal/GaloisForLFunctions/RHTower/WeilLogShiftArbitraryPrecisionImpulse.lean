import GaloisForLFunctions.RHTower.WeilLogShiftImpulseLineObstruction

/-!
# Arbitrary precision envelopes permit one-coordinate divergent histories

Two distinct amplitudes on a late impulse line cannot both be exceptional.
Choosing two positive amplitudes within one allowed error gives a history
with unbounded moment tails at every shift while preserving every other observation.
No exponential-rate restriction on the error envelope is required.
-/

open Filter Topology Real
open scoped BoundedContinuousFunction

noncomputable section

namespace RHTower

open WeilExcess

/-- Of any two distinct amplitudes on a sufficiently late impulse line,
at least one has unbounded moment terms in every tail at every real shift. -/
theorem exists_weilLogShiftRecoveryImpulse_two_amplitude_alternative :
    ∃ K : ℕ, ∀ center : ℕ →ᵇ ℝ, ∀ k : ℕ, K ≤ k → ∀ t u : ℝ, t ≠ u →
      WeilLogShiftUniformNowhereBounded (weilLogShiftRecoveryImpulseHistory center k t) ∨
        WeilLogShiftUniformNowhereBounded (weilLogShiftRecoveryImpulseHistory center k u) := by
  obtain ⟨K, hK⟩ := exists_weilLogShiftRecoveryImpulse_exceptional_subsingleton
  refine ⟨K, fun center k hk t u htu => ?_⟩
  by_cases ht : WeilLogShiftUniformNowhereBounded (weilLogShiftRecoveryImpulseHistory center k t)
  · exact Or.inl ht
  · right
    by_contra hu
    exact htu (hK center k hk ht hu)

/-- An arbitrarily small strictly positive error at one sufficiently late
coordinate can produce unbounded moment tails at every shift. -/
theorem exists_weilLogShiftRecoveryImpulse_positive_amplitude :
    ∃ K : ℕ, ∀ center : ℕ →ᵇ ℝ, ∀ k : ℕ, K ≤ k → ∀ δ : ℝ, 0 < δ →
      ∃ t : ℝ, 0 < t ∧ t ≤ δ ∧
        WeilLogShiftUniformNowhereBounded (weilLogShiftRecoveryImpulseHistory center k t) := by
  obtain ⟨K, hK⟩ := exists_weilLogShiftRecoveryImpulse_two_amplitude_alternative
  refine ⟨K, fun center k hk δ hδ => ?_⟩
  rcases hK center k hk δ (δ / 2) (by linarith only [hδ]) with hfull | hhalf
  · exact ⟨δ, hδ, le_rfl, hfull⟩
  · exact ⟨δ / 2, by positivity, by linarith only [hδ], hhalf⟩

/-- A nonnegative precision envelope needs only one positive allowance at
a late coordinate to admit one upward error with unbounded moment tails at every shift. -/
theorem exists_weilLogShiftRecoveryImpulse_within_envelope :
    ∃ K : ℕ, ∀ center : ℕ →ᵇ ℝ, ∀ ε : ℕ → ℝ, (∀ j : ℕ, 0 ≤ ε j) →
      ∀ k : ℕ, K ≤ k → 0 < ε k → ∃ h : ℕ →ᵇ ℝ,
        center k < h k ∧
        (∀ j : ℕ, j ≠ k → h j = center j) ∧
        (∀ j : ℕ, |h j - center j| ≤ ε j) ∧
        WeilLogShiftUniformNowhereBounded h := by
  obtain ⟨K, hK⟩ := exists_weilLogShiftRecoveryImpulse_positive_amplitude
  refine ⟨K, fun center ε hε k hk hεk => ?_⟩
  obtain ⟨t, ht, htε, hlarge⟩ := hK center k hk (ε k) hεk
  refine ⟨weilLogShiftRecoveryImpulseHistory center k t, ?_, ?_, ?_, hlarge⟩
  · rw [weilLogShiftRecoveryImpulseHistory_apply, if_pos rfl]
    linarith only [ht]
  · intro j hj
    rw [weilLogShiftRecoveryImpulseHistory_apply, if_neg hj, add_zero]
  · intro j
    rw [weilLogShiftRecoveryImpulseHistory_apply]
    by_cases hj : j = k
    · subst j
      rw [if_pos rfl, add_sub_cancel_left, abs_of_pos ht]
      exact htε
    · simpa only [if_neg hj, add_zero, sub_self, abs_zero] using hε j

/-- Every positive coordinatewise precision envelope admits a single strictly
upward error beyond any prescribed prefix, preserving all other observations,
with unbounded moment tails and failure of signed summability at every shift. -/
theorem exists_weilLogShiftArbitraryPrecision_single_error
    (center : ℕ →ᵇ ℝ) (ε : ℕ → ℝ) (hε : ∀ j : ℕ, 0 < ε j) (M : ℕ) :
    ∃ k : ℕ, ∃ h : ℕ →ᵇ ℝ,
      M ≤ k ∧ center k < h k ∧
      (∀ j : ℕ, j ≠ k → h j = center j) ∧
      (∀ j : ℕ, |h j - center j| ≤ ε j) ∧
      (∀ j : ℕ, j < M → h j = center j) ∧
      WeilLogShiftUniformNowhereBounded h ∧
      ∀ y : ℝ, ¬ Summable (weilLogShiftRecoveryMoment y h) := by
  obtain ⟨K, hK⟩ := exists_weilLogShiftRecoveryImpulse_within_envelope
  let k := max K M
  obtain ⟨h, hrise, hrest, herror, hlarge⟩ :=
    hK center ε (fun j => (hε j).le) k (le_max_left _ _) (hε k)
  refine ⟨k, h, le_max_right _ _, hrise, hrest, herror, ?_, hlarge,
    weilLogShiftUniform_nowhere_summable_of_nowhere_bounded hlarge⟩
  intro j hj
  apply hrest j
  dsimp only [k]
  omega

end RHTower
