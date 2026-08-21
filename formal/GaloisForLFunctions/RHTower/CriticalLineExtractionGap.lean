import GaloisForLFunctions.HTGeometry.LogPhaseNoLimit

/-!
# What two proportionality relations can and cannot force

Suppose two quantities `C` and `S` satisfy the pair of relations

`C = (a/b) S`  and  `C = ((1-a)/b) S`

with `b ≠ 0`.  Subtracting gives `(2a-1) S = 0`, so either `a = 1/2` or `S = 0`, and in the second
case `C = 0` as well.  The value `a = 1/2` therefore follows only after `S ≠ 0` has been
established; the pair of relations alone never forces it.

For the specific pair `C = lim cos (b log N)`, `S = lim sin (b log N)` this extra input is not
merely missing, it is unavailable: for `b ≠ 0` neither limit exists.
-/

open Real Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- **The dichotomy behind a two-relation extraction.** -/
theorem eq_half_or_eq_zero_of_ratio_pair {a b C S : ℝ} (hb : b ≠ 0)
    (h₁ : C = a / b * S) (h₂ : C = (1 - a) / b * S) : a = 1 / 2 ∨ (C = 0 ∧ S = 0) := by
  have hkey : (2 * a - 1) * S = 0 := by
    have h : a / b * S = (1 - a) / b * S := by rw [← h₁, h₂]
    field_simp at h
    linarith
  rcases mul_eq_zero.mp hkey with h | h
  · left
    linarith
  · exact Or.inr ⟨by rw [h₁, h, mul_zero], h⟩

/-- **The extraction is not valid without a nonvanishing hypothesis.**  There are values with
`a ≠ 1/2` satisfying both relations. -/
theorem not_forall_eq_half_of_ratio_pair :
    ¬ ∀ a b C S : ℝ, b ≠ 0 → C = a / b * S → C = (1 - a) / b * S → a = 1 / 2 := by
  intro h
  have := h 0 1 0 0 one_ne_zero (by norm_num) (by norm_num)
  norm_num at this

/-- **The two limits the extraction would need do not exist.** -/
theorem not_exists_tendsto_cos_and_sin_log {b : ℝ} (hb : b ≠ 0) :
    (¬ ∃ C : ℝ, Tendsto (fun N : ℝ => Real.cos (b * Real.log N)) atTop (𝓝 C)) ∧
      ¬ ∃ S : ℝ, Tendsto (fun N : ℝ => Real.sin (b * Real.log N)) atTop (𝓝 S) := by
  constructor
  · rintro ⟨C, hC⟩
    exact not_tendsto_cos_log_atTop hb hC
  · rintro ⟨S, hS⟩
    exact not_tendsto_sin_log_atTop hb hS

/-- **The divisor of the extraction is not a real number.**  For `a > 0` the quantity `N^a` has no
finite limit at `+∞`, so `1 / lim N^a` denotes nothing. -/
theorem not_exists_tendsto_rpow_atTop_of_pos {a : ℝ} (ha : 0 < a) :
    ¬ ∃ L : ℝ, Tendsto (fun N : ℝ => N ^ a) atTop (𝓝 L) :=
  GaloisForLFunctions.HTGeometry.not_exists_tendsto_rpow_atTop ha

end RHTower
