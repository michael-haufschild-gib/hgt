import GaloisForLFunctions.RHTower.SelbergMaassDilationStress

/-!
# No pointwise sign from a nonzero Möbius stress multiplier

The translation, dilation, and special-conformal vector fields have, on a horizontal
boundary, coefficients
`a + b * x + c * (x^(2 : ℕ) - 1)` and `b + 2 * c * x`.  Their derivative part of the
normal stress flux is
`2 * horizontal * u * v + vertical * (v^(2 : ℕ) - u^(2 : ℕ))`.

This quadratic form is indefinite whenever either coefficient is nonzero.  Therefore
no nonzero linear combination of the three Möbius currents can provide the missing
Maass boundary inequality by a pointwise stress sign alone.  The statement is purely
algebraic: it does not assert that arbitrary jets occur for a Maass form.
-/

namespace GaloisForLFunctions.RHTower.SelbergMaassMobiusMultiplierNoGo

/-- Derivative-only normal flux of a two-dimensional stress tensor. -/
def topDerivativeFlux (horizontal vertical u v : ℝ) : ℝ :=
  2 * horizontal * u * v + vertical * (v ^ (2 : ℕ) - u ^ (2 : ℕ))

/-- Quarter-turning a derivative jet reverses its stress flux. -/
theorem topDerivativeFlux_quarterTurn (horizontal vertical u v : ℝ) :
    topDerivativeFlux horizontal vertical v (-u) =
      -topDerivativeFlux horizontal vertical u v := by
  unfold topDerivativeFlux
  ring

/-- A derivative-flux quadratic form which is nonnegative on all jets is zero. -/
theorem topDerivativeFlux_coefficients_eq_zero_of_nonneg
    {horizontal vertical : ℝ}
    (h : ∀ u v : ℝ, 0 ≤ topDerivativeFlux horizontal vertical u v) :
    horizontal = 0 ∧ vertical = 0 := by
  have hv_le : 0 ≤ -vertical := by
    simpa [topDerivativeFlux] using h 1 0
  have hv_ge : 0 ≤ vertical := by
    simpa [topDerivativeFlux] using h 0 1
  have hh_ge : 0 ≤ 2 * horizontal := by
    simpa [topDerivativeFlux] using h 1 1
  have hh_le : 0 ≤ -(2 * horizontal) := by
    simpa [topDerivativeFlux] using h 1 (-1)
  constructor <;> linarith

/-- Every nonzero derivative-flux quadratic form takes a negative value. -/
theorem exists_topDerivativeFlux_neg_of_coeff_ne_zero
    {horizontal vertical : ℝ} (h : horizontal ≠ 0 ∨ vertical ≠ 0) :
    ∃ u v : ℝ, topDerivativeFlux horizontal vertical u v < 0 := by
  by_contra hn
  push Not at hn
  obtain ⟨hh, hv⟩ := topDerivativeFlux_coefficients_eq_zero_of_nonneg
    (fun u v => hn u v)
  rcases h with h | h
  · exact h hh
  · exact h hv

/-- Every nonzero derivative-flux quadratic form is genuinely indefinite. -/
theorem exists_topDerivativeFlux_pos_neg_of_coeff_ne_zero
    {horizontal vertical : ℝ} (h : horizontal ≠ 0 ∨ vertical ≠ 0) :
    (∃ u v : ℝ, 0 < topDerivativeFlux horizontal vertical u v) ∧
      (∃ u v : ℝ, topDerivativeFlux horizontal vertical u v < 0) := by
  obtain ⟨u, v, huv⟩ := exists_topDerivativeFlux_neg_of_coeff_ne_zero h
  refine ⟨⟨v, -u, ?_⟩, ⟨u, v, huv⟩⟩
  rw [topDerivativeFlux_quarterTurn]
  exact neg_pos.mpr huv

/-- Horizontal coefficient of a translation--dilation--special-conformal multiplier at height one. -/
def mobiusTopHorizontal (translation dilation specialConformal x : ℝ) : ℝ :=
  translation + dilation * x + specialConformal * (x ^ (2 : ℕ) - 1)

/-- Vertical coefficient of a translation--dilation--special-conformal multiplier at height one. -/
def mobiusTopVertical (dilation specialConformal x : ℝ) : ℝ :=
  dilation + 2 * specialConformal * x

/-- A Möbius multiplier whose top derivative flux is nonnegative for every boundary jet is zero. -/
theorem mobius_coefficients_eq_zero_of_top_flux_nonneg
    {translation dilation specialConformal : ℝ}
    (h : ∀ x u v : ℝ,
      0 ≤ topDerivativeFlux
        (mobiusTopHorizontal translation dilation specialConformal x)
        (mobiusTopVertical dilation specialConformal x) u v) :
    translation = 0 ∧ dilation = 0 ∧ specialConformal = 0 := by
  obtain ⟨h0, hd⟩ := topDerivativeFlux_coefficients_eq_zero_of_nonneg
    (fun u v => h 0 u v)
  have htranslation : translation = specialConformal := by
    norm_num [mobiusTopHorizontal] at h0
    linarith
  have hdilation : dilation = 0 := by
    simpa only [mobiusTopVertical, mul_zero, add_zero] using hd
  obtain ⟨_, hhalf⟩ := topDerivativeFlux_coefficients_eq_zero_of_nonneg
    (fun u v => h (1 / 2) u v)
  have hspecial : specialConformal = 0 := by
    rw [mobiusTopVertical, hdilation] at hhalf
    linarith
  exact ⟨htranslation.trans hspecial, hdilation, hspecial⟩

end GaloisForLFunctions.RHTower.SelbergMaassMobiusMultiplierNoGo
