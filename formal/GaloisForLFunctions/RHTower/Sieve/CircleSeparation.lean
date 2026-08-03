import GaloisForLFunctions.RHTower.Sieve.ChordalSeparation

/-!
# Chordal separation on the circle

`ChordalSeparation.lean` bounds the chord `‖e(α) - 1‖` from below by `4α` only on the half range
`0 ≤ α ≤ 1/2`.  A large sieve hypothesis, however, separates frequencies in `ℝ/ℤ`, so the bound is
needed at every real `α`, with the *distance to the nearest integer* on the left:

`4 |α - round α| ≤ ‖e(α) - 1‖`   for all `α : ℝ`.

Both extensions are periodicity arguments rather than new estimates.  Jordan's inequality is first
made two-sided (`|sin x| ≥ (2/π)|x|` on `|x| ≤ π/2`, by reflecting the negative half), and the
exponential is then reduced modulo one, which is legitimate exactly because `e(n) = 1` for integral
`n`.  Since `|α - round α| ≤ 1/2` always, the reduced argument always lands in the range where the
two-sided Jordan bound applies.

This is the form of the chord bound that a genuine `ℝ/ℤ` separation hypothesis feeds.
-/

namespace RHTower.Sieve

open Real

/-- **Two-sided Jordan inequality.** -/
theorem mul_abs_le_abs_sin {x : ℝ} (hx : |x| ≤ Real.pi / 2) :
    2 / Real.pi * |x| ≤ |Real.sin x| := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rcases le_or_gt 0 x with hpos | hneg
  · have habs : |x| = x := abs_of_nonneg hpos
    rw [habs] at hx ⊢
    have h := Real.mul_le_sin hpos hx
    exact le_trans h (le_abs_self _)
  · have hy : (0 : ℝ) ≤ -x := by linarith
    have habs : |x| = -x := abs_of_neg hneg
    rw [habs] at hx ⊢
    have h := Real.mul_le_sin hy hx
    have hsin : |Real.sin x| = |Real.sin (-x)| := by
      rw [Real.sin_neg, abs_neg]
    rw [hsin]
    exact le_trans h (le_abs_self _)

/-- **Two-sided chord bound.**  On the half range around zero the chord dominates four times the
arc, in absolute value. -/
theorem four_mul_abs_le_norm_exp_two_pi {β : ℝ} (hβ : |β| ≤ 1 / 2) :
    4 * |β| ≤ ‖Complex.exp (((2 * Real.pi * β : ℝ) : ℂ) * Complex.I) - 1‖ := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [norm_exp_I_sub_one]
  have hval : (2 * Real.pi * β) / 2 = Real.pi * β := by ring
  rw [hval]
  have hx : |Real.pi * β| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos hpi]
    nlinarith [hβ, abs_nonneg β, hpi]
  have h := mul_abs_le_abs_sin hx
  have habs : |Real.pi * β| = Real.pi * |β| := by
    rw [abs_mul, abs_of_pos hpi]
  rw [habs] at h
  have hsimp : 2 / Real.pi * (Real.pi * |β|) = 2 * |β| := by
    field_simp
  rw [hsimp] at h
  linarith

/-- Reducing the argument of `e(·)` modulo one does not change it. -/
theorem exp_two_pi_sub_round (α : ℝ) :
    Complex.exp (((2 * Real.pi * α : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((2 * Real.pi * (α - (round α : ℝ)) : ℝ) : ℂ) * Complex.I) := by
  have hsplit : ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I
      = ((2 * Real.pi * (α - (round α : ℝ)) : ℝ) : ℂ) * Complex.I
        + ((round α : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **Chord bound on the circle.**  The chord dominates four times the distance from the argument to
the nearest integer, at every real argument. -/
theorem four_mul_round_dist_le (α : ℝ) :
    4 * |α - (round α : ℝ)| ≤ ‖Complex.exp (((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) - 1‖ := by
  rw [exp_two_pi_sub_round α]
  exact four_mul_abs_le_norm_exp_two_pi (abs_sub_round α)

end RHTower.Sieve
