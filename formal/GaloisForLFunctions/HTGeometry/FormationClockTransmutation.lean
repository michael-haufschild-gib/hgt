import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Formation clock transmutation

A source density becomes a current only after an observer clock supplies its edge measure.
Nondegenerate clock changes form a multiplicative groupoid.  Their finite response is exactly a
boundary-storage term plus clock-acceleration work.  Uniform boundedness of a relative clock rate
is classified by its action on neutral unit dipoles; every unbounded rate creates arbitrarily large
response from neutral charges of fixed `l1` mass two.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Edge exposed by a discrete observer clock. -/
def formationClockEdge (clock : ℕ → ℝ) (k : ℕ) : ℝ :=
  clock (k + 1) - clock k

/-- Source density measured in one observer clock. -/
def formationClockCharge (source clock : ℕ → ℝ) (k : ℕ) : ℝ :=
  source k * formationClockEdge clock k

/-- Relative rate between two nondegenerate observer clocks. -/
def relativeFormationClockRate (sourceClock targetClock : ℕ → ℝ) (k : ℕ) : ℝ :=
  formationClockEdge targetClock k / formationClockEdge sourceClock k

/-- Finite response of one source density in one observer clock. -/
def formationClockResponse (source clock : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (N + 1), formationClockCharge source clock k

/-- Finite response after multiplying a reference-clock charge by a relative clock rate. -/
def formationClockTransmutedResponse (charge rate : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (N + 1), charge k * rate k

/-- Inclusive prefix of a formed charge. -/
def formationChargePrefix (charge : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (N + 1), charge k

/-- A relative clock rate is uniformly bounded on all scale edges. -/
def FormationClockRateUniformlyBounded (rate : ℕ → ℝ) : Prop :=
  ∃ B : ℝ, ∀ k, |rate k| ≤ B

/-- Neutral unit dipole between scale zero and one later scale. -/
def formationNeutralUnitDipole (m k : ℕ) : ℝ :=
  (if k = m then 1 else 0) - (if k = 0 then 1 else 0)

/-- Target-clock charge is reference charge multiplied by relative clock rate. -/
theorem formationClockCharge_target_eq_transmuted
    (source sourceClock targetClock : ℕ → ℝ) {k : ℕ}
    (hedge : formationClockEdge sourceClock k ≠ 0) :
    formationClockCharge source targetClock k =
      formationClockCharge source sourceClock k *
        relativeFormationClockRate sourceClock targetClock k := by
  rw [formationClockCharge, formationClockCharge, relativeFormationClockRate]
  field_simp [hedge]

/-- Relative rates compose multiplicatively across three observer clocks. -/
theorem relativeFormationClockRate_cocycle
    (clock₀ clock₁ clock₂ : ℕ → ℝ) {k : ℕ}
    (h₀ : formationClockEdge clock₀ k ≠ 0)
    (h₁ : formationClockEdge clock₁ k ≠ 0) :
    relativeFormationClockRate clock₀ clock₂ k =
      relativeFormationClockRate clock₀ clock₁ k *
        relativeFormationClockRate clock₁ clock₂ k := by
  rw [relativeFormationClockRate, relativeFormationClockRate,
    relativeFormationClockRate]
  field_simp [h₀, h₁]

/-- Target response is the relative-rate transmutation of reference charge. -/
theorem formationClockResponse_eq_transmuted
    (source sourceClock targetClock : ℕ → ℝ) {N : ℕ}
    (hedge : ∀ k, k ≤ N → formationClockEdge sourceClock k ≠ 0) :
    formationClockResponse source targetClock N =
      formationClockTransmutedResponse
        (formationClockCharge source sourceClock)
        (relativeFormationClockRate sourceClock targetClock) N := by
  unfold formationClockResponse formationClockTransmutedResponse
  apply Finset.sum_congr rfl
  intro k hk
  exact formationClockCharge_target_eq_transmuted _ _ _
    (hedge k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))

theorem formationChargePrefix_succ (charge : ℕ → ℝ) (N : ℕ) :
    formationChargePrefix charge (N + 1) =
      formationChargePrefix charge N + charge (N + 1) := by
  unfold formationChargePrefix
  rw [Finset.sum_range_succ]

/-- Clock transmutation is exactly boundary storage plus acceleration work. -/
theorem formationClockTransmutedResponse_eq_boundary_add_acceleration
    (charge rate : ℕ → ℝ) (N : ℕ) :
    formationClockTransmutedResponse charge rate N =
      formationChargePrefix charge N * rate N +
        ∑ k ∈ Finset.range N,
          formationChargePrefix charge k * (rate k - rate (k + 1)) := by
  induction N with
  | zero =>
      simp [formationClockTransmutedResponse, formationChargePrefix]
  | succ N ih =>
      rw [formationClockTransmutedResponse, Finset.sum_range_succ]
      change formationClockTransmutedResponse charge rate N +
          charge (N + 1) * rate (N + 1) = _
      rw [ih, formationChargePrefix_succ, Finset.sum_range_succ]
      ring

/-- Unit dipoles are exactly neutral in their finite support window. -/
theorem formationNeutralUnitDipole_sum (n : ℕ) :
    (∑ k ∈ Finset.range (n + 2), formationNeutralUnitDipole (n + 1) k) = 0 := by
  simp [formationNeutralUnitDipole]

/-- Every neutral unit dipole has fixed `l1` mass two. -/
theorem formationNeutralUnitDipole_l1Mass (n : ℕ) :
    (∑ k ∈ Finset.range (n + 2),
      |formationNeutralUnitDipole (n + 1) k|) = 2 := by
  have hpoint : ∀ k : ℕ,
      |formationNeutralUnitDipole (n + 1) k| =
        (if k = n + 1 then 1 else 0) + (if k = 0 then 1 else 0) := by
    intro k
    by_cases hk : k = n + 1
    · subst k
      simp [formationNeutralUnitDipole]
    · by_cases hk0 : k = 0 <;> simp [formationNeutralUnitDipole, hk, hk0]
  simp_rw [hpoint, Finset.sum_add_distrib]
  simp
  norm_num

/-- A neutral dipole measures exactly one relative-rate displacement. -/
theorem formationNeutralUnitDipole_response
    (rate : ℕ → ℝ) (n : ℕ) :
    formationClockTransmutedResponse
        (formationNeutralUnitDipole (n + 1)) rate (n + 1) =
      rate (n + 1) - rate 0 := by
  unfold formationClockTransmutedResponse
  simp_rw [formationNeutralUnitDipole, sub_mul]
  rw [Finset.sum_sub_distrib]
  simp

/-- A clock rate is bounded exactly when it is bounded on all neutral unit dipoles. -/
theorem formationClockRateUniformlyBounded_iff_dipoleResponses
    (rate : ℕ → ℝ) :
    FormationClockRateUniformlyBounded rate ↔
      ∃ B : ℝ, ∀ n,
        |formationClockTransmutedResponse
          (formationNeutralUnitDipole (n + 1)) rate (n + 1)| ≤ B := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨2 * B, fun n => ?_⟩
    rw [formationNeutralUnitDipole_response]
    exact (abs_sub _ _).trans (by linarith [hB (n + 1), hB 0])
  · rintro ⟨B, hB⟩
    refine ⟨max |rate 0| (B + |rate 0|), ?_⟩
    intro k
    cases k with
    | zero => exact le_max_left _ _
    | succ n =>
        have hd := hB n
        rw [formationNeutralUnitDipole_response] at hd
        calc
          |rate (n + 1)| = |(rate (n + 1) - rate 0) + rate 0| := by ring_nf
          _ ≤ |rate (n + 1) - rate 0| + |rate 0| := abs_add_le _ _
          _ ≤ B + |rate 0| := by linarith
          _ ≤ max |rate 0| (B + |rate 0|) := le_max_right _ _

/-- Unbounded clock change creates arbitrary response from neutral charges of fixed `l1` mass. -/
theorem exists_neutralUnitDipole_escape_of_rate_not_bounded
    (rate : ℕ → ℝ) (hunbounded : ¬ FormationClockRateUniformlyBounded rate)
    (A : ℝ) :
    ∃ n : ℕ,
      (∑ k ∈ Finset.range (n + 2), formationNeutralUnitDipole (n + 1) k) = 0 ∧
      (∑ k ∈ Finset.range (n + 2),
        |formationNeutralUnitDipole (n + 1) k|) = 2 ∧
      A < |formationClockTransmutedResponse
        (formationNeutralUnitDipole (n + 1)) rate (n + 1)| := by
  have hnot : ¬ ∃ B : ℝ, ∀ n,
      |formationClockTransmutedResponse
        (formationNeutralUnitDipole (n + 1)) rate (n + 1)| ≤ B := by
    intro h
    exact hunbounded
      ((formationClockRateUniformlyBounded_iff_dipoleResponses rate).2 h)
  push Not at hnot
  obtain ⟨n, hn⟩ := hnot A
  exact ⟨n, formationNeutralUnitDipole_sum n,
    formationNeutralUnitDipole_l1Mass n, hn⟩

end

end GaloisForLFunctions.HTGeometry
