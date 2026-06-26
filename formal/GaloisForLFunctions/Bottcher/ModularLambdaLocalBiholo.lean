/-
# `λ` is a local biholomorphism on `ℍ` — `λ' ≠ 0`, reduced to one theta Wronskian identity

For the three-value Montel lane, `λ : ℍ → ℂ∖{0,1}` must be a covering map; a covering is in particular
a local homeomorphism, i.e. (holomorphically) `λ' ≠ 0` everywhere on `ℍ`. This file establishes that,
reduced to a single classical theta identity.

* `hasDerivAt_modularLambda` — **unconditional** closed form of `λ'` from the nullwert derivatives
  (`ThetaNullwert`): with `g = θ₂/θ₃`, `λ = g⁴` so `λ' = 4g³·(θ₂'θ₃ − θ₂θ₃')/θ₃²`.
* `ThetaWronskian23` — the named input `θ₂'θ₃ − θ₂θ₃' = (πi/4)·θ₂θ₃θ₄⁴` (a weight-3 *half-integral*
  modular identity; Mathlib has no half-integral-weight theory and the `dim = 0/1` q-expansion trick
  that proved the Jacobi quartic identity does not transfer, so it is carried as a hypothesis here, in
  the same style as `TranscendentalOverAdjoin` in `Rigidity.lean`).
* `deriv_modularLambda_eq` / `deriv_modularLambda_eq_lambda` — under that identity, `λ' = πi·θ₂⁴θ₄⁴/θ₃⁴
  = πi·θ₃⁴·λ·(1−λ)` (the textbook formula; the `λ(1−λ)` factor uses the now-proven quartic identity).
* `modularLambda_deriv_ne_zero` — under that identity, `λ' ≠ 0` on `ℍ` (every factor is nonzero:
  `θ₂,θ₃,θ₄ ≠ 0` and `λ,1−λ ≠ 0`). This is the local-biholomorphism datum for `IsCoveringMap λ`.

Consumes `ModularLambdaUnconditional` (the proven quartic identity) + `ThetaNullwert` (nullwert
`τ`-derivatives).
-/
import GaloisForLFunctions.Bottcher.ModularLambdaUnconditional
import GaloisForLFunctions.Bottcher.ThetaNullwert

open Complex
open scoped Real

namespace Bottcher

/-- **The classical theta Wronskian identity** `θ₂'θ₃ − θ₂θ₃' = (πi/4)·θ₂θ₃θ₄⁴`. This is a weight-3
*half-integral* modular relation; Mathlib has no half-integral-weight machinery, so it is taken as a
named analytic input (exactly as `TranscendentalOverAdjoin` is in the E–vS algebra core). It is the one
remaining gate to "`λ` is a local biholomorphism" (`λ' ≠ 0`). -/
def ThetaWronskian23 : Prop :=
  ∀ {τ : ℂ}, 0 < τ.im →
    deriv thetaTwo τ * thetaThree τ - thetaTwo τ * deriv thetaThree τ
      = (π : ℂ) * I / 4 * (thetaTwo τ * thetaThree τ * thetaFour τ ^ 4)

/-- **`λ'` in closed form (unconditional).** With `g = θ₂/θ₃` and `λ = g⁴`, the quotient and power
rules give `λ'(τ) = 4·(θ₂/θ₃)³·(θ₂'θ₃ − θ₂θ₃')/θ₃²`. -/
theorem hasDerivAt_modularLambda {τ : ℂ} (hτ : 0 < τ.im) :
    HasDerivAt modularLambda
      (4 * (thetaTwo τ / thetaThree τ) ^ 3 *
        ((deriv thetaTwo τ * thetaThree τ - thetaTwo τ * deriv thetaThree τ) / thetaThree τ ^ 2)) τ := by
  have h3 : thetaThree τ ≠ 0 := thetaThree_ne_zero_of_im_pos hτ
  have hg : HasDerivAt (fun s => thetaTwo s / thetaThree s)
      ((deriv thetaTwo τ * thetaThree τ - thetaTwo τ * deriv thetaThree τ) / thetaThree τ ^ 2) τ := by
    have hh := (hasDerivAt_thetaTwo hτ).div (hasDerivAt_thetaThree hτ) h3
    rwa [(hasDerivAt_thetaTwo hτ).deriv, (hasDerivAt_thetaThree hτ).deriv]
  have hp := hg.pow 4
  convert hp using 1

/-- **`λ' = πi·θ₂⁴θ₄⁴/θ₃⁴`** under the theta Wronskian identity — substituting `θ₂'θ₃ − θ₂θ₃' =
(πi/4)θ₂θ₃θ₄⁴` into `hasDerivAt_modularLambda` and simplifying. -/
theorem deriv_modularLambda_eq (hW : ThetaWronskian23) {τ : ℂ} (hτ : 0 < τ.im) :
    deriv modularLambda τ
      = (π : ℂ) * I * thetaTwo τ ^ 4 * thetaFour τ ^ 4 / thetaThree τ ^ 4 := by
  have h3 : thetaThree τ ≠ 0 := thetaThree_ne_zero_of_im_pos hτ
  rw [(hasDerivAt_modularLambda hτ).deriv, hW hτ]
  field_simp

/-- **`λ' = πi·θ₃⁴·λ·(1−λ)`** — the textbook closed form. Uses the now-proven quartic identity
`θ₃⁴ = θ₂⁴ + θ₄⁴` to write `1 − λ = θ₄⁴/θ₃⁴`. -/
theorem deriv_modularLambda_eq_lambda (hW : ThetaWronskian23) {τ : ℂ} (hτ : 0 < τ.im) :
    deriv modularLambda τ
      = (π : ℂ) * I * thetaThree τ ^ 4 * modularLambda τ * (1 - modularLambda τ) := by
  have h3 : thetaThree τ ≠ 0 := thetaThree_ne_zero_of_im_pos hτ
  have h1l : 1 - modularLambda τ = thetaFour τ ^ 4 / thetaThree τ ^ 4 := by
    have hF := Bottcher2Cusp.quarticDefect_eq_zero hτ
    rw [quarticDefect] at hF
    rw [modularLambda, div_pow]
    field_simp
    linear_combination hF
  rw [deriv_modularLambda_eq hW hτ, h1l, modularLambda, div_pow]
  field_simp

/-- **`λ' ≠ 0` on `ℍ` (local biholomorphism), under the theta Wronskian identity.** `λ' = πi·θ₂⁴θ₄⁴/θ₃⁴`
and every factor is nonzero (`θ₂,θ₃,θ₄ ≠ 0` on `ℍ`). This is the local-homeomorphism datum that
`IsCoveringMap λ` (onto `ℂ∖{0,1}`) needs in the three-value Montel lane. -/
theorem modularLambda_deriv_ne_zero (hW : ThetaWronskian23) {τ : ℂ} (hτ : 0 < τ.im) :
    deriv modularLambda τ ≠ 0 := by
  rw [deriv_modularLambda_eq hW hτ]
  have h2 : thetaTwo τ ≠ 0 := thetaTwo_ne_zero_of_im_pos hτ
  have h3 : thetaThree τ ≠ 0 := thetaThree_ne_zero_of_im_pos hτ
  have h4 : thetaFour τ ≠ 0 := thetaFour_ne_zero_of_im_pos hτ
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  apply div_ne_zero
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero hπ Complex.I_ne_zero) (pow_ne_zero 4 h2))
      (pow_ne_zero 4 h4)
  · exact pow_ne_zero 4 h3

end Bottcher
