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

/-! ## An arbitrary prescribed unimodular level

The levels a phase actually has to meet are prescribed by the problem, not by where the phase
happens to start.  One extra full turn of gain buys every unimodular target.
-/

/-- A phase representative of a unimodular number, normalised to the window above a given real. -/
def phaseRepresentative (w : ℂ) (t : ℝ) : ℝ :=
  Complex.arg w + 2 * π * ⌈(t - Complex.arg w) / (2 * π)⌉

theorem le_phaseRepresentative (w : ℂ) (t : ℝ) : t ≤ phaseRepresentative w t := by
  have hpi : (0 : ℝ) < 2 * π := by positivity
  have hceil := Int.le_ceil ((t - Complex.arg w) / (2 * π))
  rw [phaseRepresentative]
  have := (div_le_iff₀ hpi).mp hceil
  linarith

theorem phaseRepresentative_lt (w : ℂ) (t : ℝ) : phaseRepresentative w t < t + 2 * π := by
  have hpi : (0 : ℝ) < 2 * π := by positivity
  have hceil := Int.ceil_lt_add_one ((t - Complex.arg w) / (2 * π))
  have h2 := mul_lt_mul_of_pos_left hceil hpi
  have hsimp : 2 * π * ((t - Complex.arg w) / (2 * π) + 1) = (t - Complex.arg w) + 2 * π := by
    field_simp
  rw [hsimp] at h2
  rw [phaseRepresentative]
  linarith

theorem exp_phaseRepresentative {w : ℂ} (hw : ‖w‖ = 1) (t : ℝ) :
    Complex.exp ((phaseRepresentative w t : ℂ) * I) = w := by
  have hbase : Complex.exp ((Complex.arg w : ℂ) * I) = w := by
    have h := Complex.norm_mul_exp_arg_mul_I w
    rwa [hw, Complex.ofReal_one, one_mul] at h
  have hsplit : ((phaseRepresentative w t : ℝ) : ℂ) * I
      = (Complex.arg w : ℂ) * I
        + (⌈(t - Complex.arg w) / (2 * π)⌉ : ℤ) * (2 * π * I) := by
    rw [phaseRepresentative]
    push_cast
    ring
  rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, hbase]

/-- **Interlacing at a prescribed unimodular level.**  A phase gaining `2π(N+1)` meets any
prescribed unimodular value `N + 1` times and its antipode `N` times, strictly alternating. -/
theorem exists_interlacing_levels_of_gain_two_turns
    {Φ : ℝ → ℝ} {α β : ℝ} {N : ℕ} (hαβ : α ≤ β)
    (hcont : ContinuousOn Φ (Icc α β)) (hmono : StrictMonoOn Φ (Icc α β))
    (hgain : Φ α + 2 * π * ((N : ℝ) + 1) ≤ Φ β) {w : ℂ} (hw : ‖w‖ = 1) :
    ∃ x x' : ℕ → ℝ,
      (∀ k ≤ N, x k ∈ Icc α β ∧ Complex.exp ((Φ (x k) : ℂ) * I) = w) ∧
      (∀ k, k < N → x' k ∈ Icc α β ∧ Complex.exp ((Φ (x' k) : ℂ) * I) = -w) ∧
      (∀ k, k < N → x k < x' k ∧ x' k < x (k + 1)) := by
  have hp : (0 : ℝ) < 2 * π := by positivity
  set y := phaseRepresentative w (Φ α) with hy
  have hlow : Φ α ≤ y := le_phaseRepresentative w (Φ α)
  have hhigh : y + 2 * π * N ≤ Φ β := by
    have hlt := phaseRepresentative_lt w (Φ α)
    rw [← hy] at hlt
    nlinarith
  obtain ⟨x, x', hx, hx', hint⟩ :=
    exists_interlacing_levelPoints hp hαβ hcont hmono hlow hhigh
  refine ⟨x, x', fun k hk => ⟨(hx k hk).1, ?_⟩, fun k hk => ⟨(hx' k hk).1, ?_⟩, hint⟩
  · rw [(hx k hk).2]
    have := exp_phase_add_turn y k
    rw [this, hy, exp_phaseRepresentative hw]
  · rw [(hx' k hk).2]
    have := exp_phase_add_half_turn y k
    rw [this, hy, exp_phaseRepresentative hw]

end GaloisForLFunctions.HTGeometry
