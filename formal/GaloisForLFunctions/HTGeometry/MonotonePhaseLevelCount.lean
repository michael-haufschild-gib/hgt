import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Level counting for a strictly monotone phase

A boundary phase that is continuous and strictly increasing across an interval meets every level in
its range exactly once, so the number of solutions of a congruence `φ ≡ y` is governed entirely by
the total phase gain.  A gain of `p · N` forces `N + 1` solutions of the class `y`, and the class
shifted by the half period is met exactly once between consecutive solutions, so the two level sets
strictly alternate.

This is the counting half of an argument-principle crossing estimate: the analytic input is the
gain, and everything after it is monotone real analysis.

`EdgeEventParity.exists_crossing_enum_parity` enumerates *all* crossings of the single class
`sin θ = 0` and reads their parity; the statements here instead bound the number of crossings of a
prescribed class from below by the gain, and interlace two antipodal classes.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

/-- A continuous phase meets every level between its endpoint values. -/
theorem exists_mem_Icc_eq {φ : ℝ → ℝ} {α β y : ℝ} (hαβ : α ≤ β)
    (hcont : ContinuousOn φ (Icc α β)) (hy : y ∈ Icc (φ α) (φ β)) :
    ∃ x ∈ Icc α β, φ x = y :=
  intermediate_value_Icc hαβ hcont hy

/-- A strictly increasing phase orders its level points by their levels. -/
theorem lt_of_phase_lt {φ : ℝ → ℝ} {α β : ℝ} (hmono : StrictMonoOn φ (Icc α β))
    {u v : ℝ} (hu : u ∈ Icc α β) (hv : v ∈ Icc α β) (h : φ u < φ v) : u < v :=
  (hmono.lt_iff_lt hu hv).mp h

/-- **The level points of one congruence class.**  A phase gain of `p * N` produces `N + 1`
strictly increasing solutions of `φ x = y + p * k`. -/
theorem exists_strictMono_levelPoints {φ : ℝ → ℝ} {α β y p : ℝ} {N : ℕ}
    (hp : 0 < p) (hαβ : α ≤ β)
    (hcont : ContinuousOn φ (Icc α β)) (hmono : StrictMonoOn φ (Icc α β))
    (hlow : φ α ≤ y) (hhigh : y + p * N ≤ φ β) :
    ∃ x : ℕ → ℝ, (∀ k ≤ N, x k ∈ Icc α β) ∧ (∀ k ≤ N, φ (x k) = y + p * k) ∧
      ∀ j k, j ≤ N → k ≤ N → j < k → x j < x k := by
  classical
  have hmem : ∀ k : ℕ, k ≤ N → (y + p * k) ∈ Icc (φ α) (φ β) := by
    intro k hk
    have hkN : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    constructor
    · nlinarith
    · nlinarith
  have hex : ∀ k : ℕ, ∃ t : ℝ, k ≤ N → t ∈ Icc α β ∧ φ t = y + p * k := by
    intro k
    by_cases hk : k ≤ N
    · obtain ⟨t, ht, hteq⟩ := exists_mem_Icc_eq hαβ hcont (hmem k hk)
      exact ⟨t, fun _ => ⟨ht, hteq⟩⟩
    · exact ⟨α, fun hcon => absurd hcon hk⟩
  choose x hx using hex
  refine ⟨x, fun k hk => (hx k hk).1, fun k hk => (hx k hk).2, ?_⟩
  intro j k hj hk hjk
  refine lt_of_phase_lt hmono (hx j hj).1 (hx k hk).1 ?_
  rw [(hx j hj).2, (hx k hk).2]
  have : (j : ℝ) < (k : ℝ) := by exact_mod_cast hjk
  nlinarith

/-- **Strictly interlacing level sets.**  The class `y` and the class shifted by the half period
alternate: exactly one half-shifted point lies between consecutive points of the base class. -/
theorem exists_interlacing_levelPoints {φ : ℝ → ℝ} {α β y p : ℝ} {N : ℕ}
    (hp : 0 < p) (hαβ : α ≤ β)
    (hcont : ContinuousOn φ (Icc α β)) (hmono : StrictMonoOn φ (Icc α β))
    (hlow : φ α ≤ y) (hhigh : y + p * N ≤ φ β) :
    ∃ x x' : ℕ → ℝ,
      (∀ k ≤ N, x k ∈ Icc α β ∧ φ (x k) = y + p * k) ∧
      (∀ k, k < N → x' k ∈ Icc α β ∧ φ (x' k) = y + p / 2 + p * k) ∧
      (∀ k, k < N → x k < x' k ∧ x' k < x (k + 1)) := by
  obtain ⟨x, hx1, hx2, _⟩ :=
    exists_strictMono_levelPoints hp hαβ hcont hmono hlow hhigh
  -- the half-shifted class gains `p * (N - 1)` starting from `y + p/2`
  have hlow' : φ α ≤ y + p / 2 := by linarith
  have hhigh' : ∀ k : ℕ, k < N → (y + p / 2 + p * k) ∈ Icc (φ α) (φ β) := by
    intro k hk
    have hk1 : (k : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hk
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    constructor
    · nlinarith
    · nlinarith
  have hex : ∀ k : ℕ, ∃ t : ℝ, k < N → t ∈ Icc α β ∧ φ t = y + p / 2 + p * k := by
    intro k
    by_cases hk : k < N
    · obtain ⟨t, ht, hteq⟩ := exists_mem_Icc_eq hαβ hcont (hhigh' k hk)
      exact ⟨t, fun _ => ⟨ht, hteq⟩⟩
    · exact ⟨α, fun hcon => absurd hcon hk⟩
  choose x' hx' using hex
  refine ⟨x, x', fun k hk => ⟨hx1 k hk, hx2 k hk⟩, fun k hk => hx' k hk, ?_⟩
  intro k hk
  have hkN : k ≤ N := le_of_lt hk
  have hk1N : k + 1 ≤ N := hk
  constructor
  · refine lt_of_phase_lt hmono (hx1 k hkN) (hx' k hk).1 ?_
    rw [hx2 k hkN, (hx' k hk).2]
    linarith
  · refine lt_of_phase_lt hmono (hx' k hk).1 (hx1 (k + 1) hk1N) ?_
    rw [hx2 (k + 1) hk1N, (hx' k hk).2]
    push_cast
    linarith

/-- The level points of one class are pairwise distinct, so the class really has `N + 1` solutions
in the interval. -/
theorem injOn_levelPoints {φ : ℝ → ℝ} {α β y p : ℝ} {N : ℕ}
    (hp : 0 < p) (hαβ : α ≤ β)
    (hcont : ContinuousOn φ (Icc α β)) (hmono : StrictMonoOn φ (Icc α β))
    (hlow : φ α ≤ y) (hhigh : y + p * N ≤ φ β) :
    ∃ x : ℕ → ℝ, InjOn x (Iic N) ∧ (∀ k ≤ N, x k ∈ Icc α β) ∧
      ∀ k ≤ N, φ (x k) = y + p * k := by
  obtain ⟨x, hx1, hx2, hx3⟩ :=
    exists_strictMono_levelPoints hp hαβ hcont hmono hlow hhigh
  refine ⟨x, ?_, hx1, hx2⟩
  intro j hj k hk hjk
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact absurd hjk (ne_of_lt (hx3 j k hj hk h))
  · exact absurd hjk.symm (ne_of_lt (hx3 k j hk hj h))

end GaloisForLFunctions.HTGeometry
