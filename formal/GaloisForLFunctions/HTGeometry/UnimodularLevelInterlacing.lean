import GaloisForLFunctions.HTGeometry.MonotonePhaseLevelCount
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Interlacing unimodular levels of a monotone boundary phase

A unimodular function written as `exp(i Φ)` with `Φ` continuous and strictly increasing meets the
value `1` exactly where `Φ` is a multiple of `2π` and the value `-1` exactly where `Φ` is an odd
multiple of `π`.  A phase gain of `2πN` therefore forces `N + 1` solutions of the first equation and
`N` of the second, and the two solution sets strictly alternate.

Only the gain is analytic input; everything else is the monotone level count.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Complex Real Set

/-- The full-turn levels of a phase are the points where the unimodular function equals one. -/
theorem exp_phase_eq_one {Φ : ℝ → ℝ} {x : ℝ} {k : ℕ} (h : Φ x = 2 * π * k) :
    Complex.exp ((Φ x : ℂ) * I) = 1 := by
  rw [h]
  have : ((2 * π * (k : ℕ) : ℝ) : ℂ) * I = (k : ℤ) * (2 * π * I) := by
    push_cast
    ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

/-- The half-turn levels of a phase are the points where the unimodular function equals minus
one. -/
theorem exp_phase_eq_neg_one {Φ : ℝ → ℝ} {x : ℝ} {k : ℕ}
    (h : Φ x = 2 * π / 2 + 2 * π * k) :
    Complex.exp ((Φ x : ℂ) * I) = -1 := by
  rw [h]
  have hsplit : ((2 * π / 2 + 2 * π * (k : ℕ) : ℝ) : ℂ) * I
      = (π : ℂ) * I + (k : ℤ) * (2 * π * I) := by
    push_cast
    ring
  rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, Complex.exp_pi_mul_I]
  ring

/-- **Interlacing unimodular levels.**  A continuous strictly increasing phase with gain at least
`2πN` makes `exp(iΦ)` take the value `1` at `N + 1` points and the value `-1` at `N` points, and the
two families strictly alternate. -/
theorem exists_interlacing_unimodular_levels
    {Φ : ℝ → ℝ} {α β : ℝ} {N : ℕ} (hαβ : α ≤ β)
    (hcont : ContinuousOn Φ (Icc α β)) (hmono : StrictMonoOn Φ (Icc α β))
    (hlow : Φ α ≤ 0) (hhigh : 2 * π * N ≤ Φ β) :
    ∃ x x' : ℕ → ℝ,
      (∀ k ≤ N, x k ∈ Icc α β ∧ Complex.exp ((Φ (x k) : ℂ) * I) = 1) ∧
      (∀ k, k < N → x' k ∈ Icc α β ∧ Complex.exp ((Φ (x' k) : ℂ) * I) = -1) ∧
      (∀ k, k < N → x k < x' k ∧ x' k < x (k + 1)) := by
  have hp : (0 : ℝ) < 2 * π := by positivity
  have hhigh' : (0 : ℝ) + 2 * π * N ≤ Φ β := by linarith
  obtain ⟨x, x', hx, hx', hint⟩ :=
    exists_interlacing_levelPoints hp hαβ hcont hmono hlow hhigh'
  refine ⟨x, x', fun k hk => ⟨(hx k hk).1, ?_⟩, fun k hk => ⟨(hx' k hk).1, ?_⟩, hint⟩
  · exact exp_phase_eq_one (by simpa using (hx k hk).2)
  · exact exp_phase_eq_neg_one (by simpa using (hx' k hk).2)

/-! ## An arbitrary base level -/

/-- Shifting a phase by a full turn does not change the unimodular value. -/
theorem exp_phase_add_turn (y : ℝ) (k : ℕ) :
    Complex.exp (((y + 2 * π * k : ℝ) : ℂ) * I) = Complex.exp ((y : ℂ) * I) := by
  have hsplit : ((y + 2 * π * (k : ℕ) : ℝ) : ℂ) * I
      = (y : ℂ) * I + (k : ℤ) * (2 * π * I) := by
    push_cast
    ring
  rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Shifting a phase by a half turn negates the unimodular value. -/
theorem exp_phase_add_half_turn (y : ℝ) (k : ℕ) :
    Complex.exp (((y + 2 * π / 2 + 2 * π * k : ℝ) : ℂ) * I)
      = -Complex.exp ((y : ℂ) * I) := by
  have hsplit : ((y + 2 * π / 2 + 2 * π * (k : ℕ) : ℝ) : ℂ) * I
      = ((y : ℂ) * I + (π : ℂ) * I) + (k : ℤ) * (2 * π * I) := by
    push_cast
    ring
  rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, Complex.exp_add,
    Complex.exp_pi_mul_I]
  ring

/-- **Interlacing antipodal levels.**  A continuous strictly increasing phase gaining at least
`2πN` across `[α, β]` returns to its left-endpoint unimodular value `N + 1` times and reaches the
antipodal value `N` times, and the two families strictly alternate.  This is the crossing count of
a boundary phase with no reference to which value the phase starts at. -/
theorem exists_interlacing_levels_of_phase_gain
    {Φ : ℝ → ℝ} {α β : ℝ} {N : ℕ} (hαβ : α ≤ β)
    (hcont : ContinuousOn Φ (Icc α β)) (hmono : StrictMonoOn Φ (Icc α β))
    (hgain : Φ α + 2 * π * N ≤ Φ β) :
    ∃ x x' : ℕ → ℝ,
      (∀ k ≤ N, x k ∈ Icc α β ∧
        Complex.exp ((Φ (x k) : ℂ) * I) = Complex.exp ((Φ α : ℂ) * I)) ∧
      (∀ k, k < N → x' k ∈ Icc α β ∧
        Complex.exp ((Φ (x' k) : ℂ) * I) = -Complex.exp ((Φ α : ℂ) * I)) ∧
      (∀ k, k < N → x k < x' k ∧ x' k < x (k + 1)) := by
  have hp : (0 : ℝ) < 2 * π := by positivity
  obtain ⟨x, x', hx, hx', hint⟩ :=
    exists_interlacing_levelPoints hp hαβ hcont hmono le_rfl hgain
  refine ⟨x, x', fun k hk => ⟨(hx k hk).1, ?_⟩, fun k hk => ⟨(hx' k hk).1, ?_⟩, hint⟩
  · rw [(hx k hk).2]
    exact exp_phase_add_turn (Φ α) k
  · rw [(hx' k hk).2]
    exact exp_phase_add_half_turn (Φ α) k

end GaloisForLFunctions.HTGeometry
