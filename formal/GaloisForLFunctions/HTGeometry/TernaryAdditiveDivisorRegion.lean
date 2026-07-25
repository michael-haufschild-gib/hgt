/-
The admissible region of the ternary additive divisor input for the sixth moment.

The transfer from divisor correlations to moments is usually recorded with a single exponent: the
size `X^{θ}` of the error in the shifted sum.  It has a second parameter.  The additive divisor
statement is made for a *smoothed* sum whose test function has derivatives bounded by `P^{i+j}`, and
the error is `P^{C} X^{θ+ε}`; the exponent `C` measures how sharply the cut-off may be taken.  The
sixth moment needs a joint condition on `(θ, C)`:

    1/2 ≤ θ < 2/3    and    1 ≤ C < 3(1 - θ).

The region is a triangle with vertices `(1/2, 1)`, `(1/2, 3/2)`, `(2/3, 1)`.  Its `θ`-projection
`[1/2, 2/3)` is exactly the range in which the one-parameter transfer already returns the Lindelöf
value, so the second parameter is a genuine additional constraint, invisible to `transferBound`.
-/
import GaloisForLFunctions.HTGeometry.AveragedDivisorInput

namespace HTGeometry

/-- The admissible region for the ternary additive divisor input: size exponent `θ` and smoothness
exponent `C`. -/
def ngAdmissible (θ C : ℚ) : Prop := 1/2 ≤ θ ∧ θ < 2/3 ∧ 1 ≤ C ∧ C < 3 * (1 - θ)

/-- The Conrey–Gonek size with the Duke–Friedlander–Iwaniec smoothness exponent lies in the
region. -/
theorem ngAdmissible_conreyGonek : ngAdmissible (1/2) (5/4) := by
  refine ⟨le_refl _, by norm_num, by norm_num, by norm_num⟩

/-- The smoothness exponent is capped at `3/2` throughout the region. -/
theorem ngAdmissible_C_lt (θ C : ℚ) (h : ngAdmissible θ C) : C < 3/2 := by
  obtain ⟨h1, _, _, h4⟩ := h
  linarith

/-- The size exponent is capped at `2/3` throughout the region — the same threshold the
one-parameter transfer produces. -/
theorem ngAdmissible_theta_lt (θ C : ℚ) (h : ngAdmissible θ C) : θ < 2/3 := h.2.1

/-- **The two constraints are not independent.**  Demanding the weakest admissible size `θ` forces
the strongest admissible smoothness `C`, and conversely: the region degenerates to the single point
`C = 1` as `θ → 2/3`. -/
theorem ngAdmissible_tradeoff (θ C : ℚ) (h : ngAdmissible θ C) : θ < 1 - C / 3 := by
  obtain ⟨_, _, _, h4⟩ := h
  linarith

/-- **Agreement with the one-parameter transfer.**  The `θ`-projection of the admissible region is
exactly the range where `transferBound 3 1 θ = 1`; so the literature's threshold and the transfer's
threshold coincide, and `C` is the only extra demand. -/
theorem ngAdmissible_projection_agrees {θ : ℝ} (h : θ < 2/3) :
    transferBound 3 1 θ = 1 := by
  rw [pointwise_input_eq_one_iff]
  linarith

/-- The region is a triangle: at the Conrey–Gonek size the smoothness may be as large as `3/2`, and
at the extreme size `2/3` only `C = 1` survives — but that corner is excluded, since the constraint
on `C` is strict. -/
theorem ngAdmissible_corner_excluded (C : ℚ) : ¬ ngAdmissible (2/3) C := by
  intro h
  exact absurd h.2.1 (by norm_num)

end HTGeometry
