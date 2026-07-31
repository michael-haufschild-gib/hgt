import GaloisForLFunctions.RHTower.SummableWeightedInfinitePhaseQuantile

/-!
# Actual first return for countable weighted phase packets

The first positive coherence time is defined in `WithTop ℕ`, so it is
well-defined even before recurrence existence is supplied. This file proves
that the measurable finite-clock hit union is exactly the event that the
actual first return occurs by that deadline.
-/

noncomputable section

namespace RHTower

/-- Positive-clock coherence predicate for one countable torus packet. -/
def CountableTorusWeightedCoherenceAt
    (p : ℕ → ℝ) (x : ℕ → UnitAddCircle) (η : ℝ) (n : ℕ) : Prop :=
  0 < n ∧
    1 - η ≤
      ‖summableWeightedPhaseAmplitude p (fun k =>
        fourier 1 (((n : ℕ) : ℤ) • x k))‖

/-- First positive coherence time, with value `∞` when no positive hit
exists. -/
noncomputable def countableTorusWeightedFirstCoherenceTime
  (p : ℕ → ℝ) (x : ℕ → UnitAddCircle) (η : ℝ) : WithTop ℕ := by
  classical
  exact if h : ∃ n, CountableTorusWeightedCoherenceAt p x η n then
    (Nat.find h : WithTop ℕ)
  else ⊤

/-- Any witnessed hit bounds the actual first coherence time from above. -/
theorem countableTorusWeightedFirstCoherenceTime_le_of
    (p : ℕ → ℝ) (x : ℕ → UnitAddCircle) (η : ℝ) {n : ℕ}
    (hn : CountableTorusWeightedCoherenceAt p x η n) :
    countableTorusWeightedFirstCoherenceTime p x η ≤ n := by
  classical
  let h : ∃ n, CountableTorusWeightedCoherenceAt p x η n := ⟨n, hn⟩
  rw [countableTorusWeightedFirstCoherenceTime, dif_pos h]
  exact_mod_cast Nat.find_min' h hn

/-- The finite-clock hit union is exactly existence of a positive coherent
clock no larger than `N`. -/
theorem mem_countableTorusWeightedCoherenceHitUnion_iff
    (p : ℕ → ℝ) (x : ℕ → UnitAddCircle) (N : ℕ) (η : ℝ) :
    x ∈ countableTorusWeightedCoherenceHitUnion p N η ↔
      ∃ n : ℕ, n ≤ N ∧
        CountableTorusWeightedCoherenceAt p x η n := by
  constructor
  · intro hx
    rw [countableTorusWeightedCoherenceHitUnion, Set.mem_iUnion] at hx
    obtain ⟨i, hi⟩ := hx
    rw [Set.mem_setOf_eq] at hi
    refine ⟨i.1 + 1, by omega, ?_⟩
    exact ⟨by omega, by simpa only using hi⟩
  · rintro ⟨n, hnN, hn0, hn⟩
    have hN : 0 < N := hn0.trans_le hnN
    let i : Fin N := ⟨n - 1, by omega⟩
    rw [countableTorusWeightedCoherenceHitUnion, Set.mem_iUnion]
    refine ⟨i, ?_⟩
    rw [Set.mem_setOf_eq]
    have hin : i.1 + 1 = n := by
      dsimp only [i]
      omega
    simpa only [hin] using hn

/-- Avoidance of every clock through `N` is exactly the strict lower bound
`N < τ` for the actual first coherence time. -/
theorem not_mem_hitUnion_iff_deadline_lt_firstCoherenceTime
    (p : ℕ → ℝ) (x : ℕ → UnitAddCircle) (N : ℕ) (η : ℝ) :
    x ∉ countableTorusWeightedCoherenceHitUnion p N η ↔
      (N : WithTop ℕ) <
        countableTorusWeightedFirstCoherenceTime p x η := by
  classical
  rw [mem_countableTorusWeightedCoherenceHitUnion_iff]
  by_cases h : ∃ n, CountableTorusWeightedCoherenceAt p x η n
  · rw [countableTorusWeightedFirstCoherenceTime, dif_pos h]
    constructor
    · intro hnone
      exact_mod_cast Nat.lt_of_not_ge fun hfind => hnone
        ⟨Nat.find h, hfind, Nat.find_spec h⟩
    · intro hlt
      push Not
      intro n hnN hn
      have hmin : Nat.find h ≤ n := Nat.find_min' h hn
      have hltNat : N < Nat.find h := by exact_mod_cast hlt
      omega
  · rw [countableTorusWeightedFirstCoherenceTime, dif_neg h]
    constructor
    · intro _hnone
      exact WithTop.coe_lt_top N
    · intro _hlt
      push Not
      intro n hnN hn
      exact h ⟨n, hn⟩

end RHTower
