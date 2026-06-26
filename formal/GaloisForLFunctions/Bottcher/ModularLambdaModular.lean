/-
# Γ(2)-modularity of the modular lambda function

`λ = (θ₂/θ₃)⁴` is the Hauptmodul for `Γ(2)`; this file records the two value-relations that generate
its automorphy, the second of which converts "λ omits 0" into "λ omits 1":

* `modularLambda_add_two : λ(τ+2) = λ(τ)` — the `T²` (Γ(2) translation) invariance. **Unconditional**:
  applying `modularLambda_T` at `τ+1` and `thetaTwo_add_one`/`thetaFour_add_one` gives a prefactor
  `exp(πi/4)⁴ = exp(πi) = −1` that exactly cancels the sign in `modularLambda_T`.
* `modularLambda_S_eq_one_sub : λ(−1/τ) = 1 − λ(τ)` — the `S` involution of the anharmonic action.
  **Conditional on the Jacobi quartic identity** `F(τ)=0`: from `modularLambda_S : λ(−1/τ)=(θ₄/θ₃)⁴`
  and `θ₃⁴ = θ₂⁴+θ₄⁴`, `(θ₄/θ₃)⁴ = 1 − (θ₂/θ₃)⁴ = 1 − λ`.

Together with `modularLambda_T` (`λ(τ+1) = −(θ₂/θ₄)⁴`) these are the generator-relations exhibiting `λ`
as the `Γ(2)` Hauptmodul; the remaining covering datum (`IsCoveringMap λ` onto `ℂ∖{0,1}`, feeding
`normal_of_omitting_lift` via mathlib's `IsCoveringMap.existsUnique_continuousMap_lifts`) is the last
absent input on the three-value-Montel side.

Consumes `QuarticCusp`. Mathlib only otherwise.
-/
import GaloisForLFunctions.Bottcher.QuarticCusp

open Complex
open scoped Real

namespace Bottcher

/-- `exp(πi/4)⁴ = exp(πi) = −1`. -/
private theorem exp_pi_I_quarter_pow_four : (Complex.exp ((Real.pi : ℂ) * I / 4)) ^ 4 = -1 := by
  rw [← Complex.exp_nat_mul,
    show ((4 : ℕ) : ℂ) * ((Real.pi : ℂ) * I / 4) = (Real.pi : ℂ) * I by push_cast; ring]
  exact Complex.exp_pi_mul_I

/-- **`λ(τ+2) = λ(τ)`** — the `T²` (Γ(2)) translation invariance of the modular lambda function.
Unconditional. -/
theorem modularLambda_add_two (τ : ℂ) : modularLambda (τ + 2) = modularLambda τ := by
  have key : modularLambda (τ + 1 + 1) = -(thetaTwo (τ + 1) / thetaFour (τ + 1)) ^ 4 :=
    modularLambda_T (τ + 1)
  rw [thetaTwo_add_one, thetaFour_add_one] at key
  rw [show τ + 2 = τ + 1 + 1 by ring, key]
  unfold modularLambda
  rw [mul_div_assoc, div_pow, mul_pow, exp_pi_I_quarter_pow_four]
  ring

/-- **`λ(−1/τ) = 1 − λ(τ)`** — the `S` involution of the anharmonic group, conditional on the Jacobi
quartic identity `F(τ) = 0`. This is precisely the relation that turns the (unconditional) "λ omits 0"
into "λ omits 1". -/
theorem modularLambda_S_eq_one_sub {τ : ℂ} (hτ : 0 < τ.im) (hF : quarticDefect τ = 0) :
    modularLambda (-1 / τ) = 1 - modularLambda τ := by
  have h3 : thetaThree τ ≠ 0 := thetaThree_ne_zero_of_im_pos hτ
  have h3' : thetaThree τ ^ 4 ≠ 0 := pow_ne_zero 4 h3
  rw [modularLambda_S hτ]
  unfold modularLambda
  rw [quarticDefect] at hF
  rw [div_pow, div_pow]
  field_simp
  linear_combination -hF

/-- The Γ(2) generators act on `λ`-values by the anharmonic involution `λ ↦ 1−λ` (`S`) and the
translation `λ ↦ λ` of period 2 (`T²`); together they realise `λ` as the `Γ(2)` Hauptmodul. Bundled
form, conditional on the quartic identity. -/
theorem modularLambda_anharmonic_S {τ : ℂ} (hτ : 0 < τ.im) (hF : quarticDefect τ = 0) :
    modularLambda (-1 / τ) = 1 - modularLambda τ ∧ modularLambda (τ + 2) = modularLambda τ :=
  ⟨modularLambda_S_eq_one_sub hτ hF, modularLambda_add_two τ⟩

end Bottcher


namespace Bottcher

/-- **`λ(τ+1)·(λ(τ)−1) = λ(τ)`** — the `T`-action `λ ↦ λ/(λ−1)` of the anharmonic group, in cleared
(division-free) form, conditional on the Jacobi quartic identity. From `modularLambda_T`
(`λ(τ+1) = −(θ₂/θ₄)⁴`) and `θ₃⁴ = θ₂⁴+θ₄⁴`. -/
theorem modularLambda_T_mul {τ : ℂ} (hτ : 0 < τ.im) (hF : quarticDefect τ = 0) :
    modularLambda (τ + 1) * (modularLambda τ - 1) = modularLambda τ := by
  have h3 : thetaThree τ ≠ 0 := thetaThree_ne_zero_of_im_pos hτ
  have h4 : thetaFour τ ≠ 0 := thetaFour_ne_zero_of_im_pos hτ
  rw [modularLambda_T, modularLambda]
  rw [quarticDefect] at hF
  field_simp
  linear_combination (thetaTwo τ ^ 4) * hF

/-- **`λ(τ+1) = λ(τ)/(λ(τ)−1)`** — the divided form of `modularLambda_T_mul` (`λ ≠ 1` under the
quartic identity makes the denominator nonzero). -/
theorem modularLambda_T_eq {τ : ℂ} (hτ : 0 < τ.im) (hF : quarticDefect τ = 0) :
    modularLambda (τ + 1) = modularLambda τ / (modularLambda τ - 1) := by
  have hne1 : modularLambda τ - 1 ≠ 0 := sub_ne_zero.mpr (modularLambda_ne_one_of_quartic hτ hF)
  rw [eq_div_iff hne1, modularLambda_T_mul hτ hF]

/-- **`λ(I) = 1/2`** — the value at the `S`-fixed point `τ = I` (`−1/I = I`), from the involution
`λ(−1/τ) = 1 − λ(τ)`: `λ(I) = 1 − λ(I)`. Conditional on the quartic identity at `I`. -/
theorem modularLambda_at_I (hF : quarticDefect I = 0) : modularLambda I = 1 / 2 := by
  have hI : (0 : ℝ) < I.im := by simp
  have key : modularLambda (-1 / I) = 1 - modularLambda I := modularLambda_S_eq_one_sub hI hF
  rw [show (-1 / I : ℂ) = I by rw [div_eq_mul_inv, Complex.inv_I]; ring] at key
  linear_combination key / 2

end Bottcher


namespace Bottcher

/-- `im(−1/z) > 0` when `im z > 0`. -/
private theorem im_neg_inv_pos {z : ℂ} (hz : 0 < z.im) : 0 < (-1 / z).im := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have hn : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz0
  rw [neg_div, Complex.neg_im, Complex.div_im]
  simp only [Complex.one_im, Complex.one_re, zero_mul, zero_div, one_mul, zero_sub, neg_neg]
  exact div_pos hz hn

/-- **Invariance of `λ` under the second `Γ(2)` generator** `[[1,0],[2,1]] : τ ↦ τ/(2τ+1)`.
Conditional on the Jacobi quartic identity (global), via the factorisation `τ/(2τ+1) = S⁻¹T⁻²S·τ`
and the anharmonic relations `λ(−1/·) = 1 − λ` and `λ(·+2) = λ`:
`λ(τ/(2τ+1)) = 1 − λ((−1/τ)−2) = 1 − λ(−1/τ) = 1 − (1 − λ(τ)) = λ(τ)`. With `λ(τ+2)=λ(τ)` (already
unconditional) these are the two generators of `Γ(2)`, so `λ` descends to `ℍ/Γ(2)` — the Hauptmodul
property modulo the quartic identity. -/
theorem modularLambda_Gamma2_gen
    (hquartic : ∀ σ : ℂ, 0 < σ.im → quarticDefect σ = 0) {τ : ℂ} (hτ : 0 < τ.im) :
    modularLambda (τ / (2 * τ + 1)) = modularLambda τ := by
  have hτ0 : τ ≠ 0 := by rintro rfl; simp at hτ
  have h2 : 2 * τ + 1 ≠ 0 := by
    intro h; apply absurd hτ; rw [show τ = -1/2 by linear_combination h / 2]; norm_num
  set σ : ℂ := -1 / τ with hσ
  have hσim : 0 < σ.im := im_neg_inv_pos hτ
  set w : ℂ := σ - 2 with hw
  have hwim : 0 < w.im := by rw [hw, Complex.sub_im]; simpa using hσim
  have hwne : w ≠ 0 := fun h => by rw [h] at hwim; simp at hwim
  have heq : τ / (2 * τ + 1) = -1 / w := by
    rw [div_eq_div_iff h2 hwne, hw, hσ]; field_simp; ring
  have e1 : modularLambda (τ / (2 * τ + 1)) = 1 - modularLambda w := by
    rw [heq, modularLambda_S_eq_one_sub hwim (hquartic w hwim)]
  have e2 : modularLambda w = modularLambda σ := by
    have hp := modularLambda_add_two (σ - 2)
    rw [show σ - 2 + 2 = σ by ring] at hp
    rw [hw]; exact hp.symm
  have e3 : modularLambda σ = 1 - modularLambda τ := by
    rw [hσ]; exact modularLambda_S_eq_one_sub hτ (hquartic τ hτ)
  rw [e1, e2, e3]; ring

end Bottcher


namespace Bottcher

/-- **`F(τ+2) = F(τ)`** — the `T²` (Γ(2)) invariance of the quartic defect. UNCONDITIONAL (two
applications of `quarticDefect_add_one`, the two signs cancelling). -/
theorem quarticDefect_add_two (τ : ℂ) : quarticDefect (τ + 2) = quarticDefect τ := by
  have h1 := quarticDefect_add_one (τ + 1)
  rw [show τ + 1 + 1 = τ + 2 by ring] at h1
  rw [h1, quarticDefect_add_one]; ring

/-- **`F(τ/(2τ+1)) = (2τ+1)²·F(τ)`** — the weight-2 transformation of the quartic defect under the
second `Γ(2)` generator `[[1,0],[2,1]]`. UNCONDITIONAL, from `quarticDefect_S` (`F(−1/τ)=−τ²F(τ)`)
and `quarticDefect_add_two`, via `τ/(2τ+1) = S⁻¹T⁻²S·τ`:
`F(τ/(2τ+1)) = −w²·F(w) = −w²·F(σ) = −w²·(−τ²)·F(τ) = (w·τ)²·F(τ) = (2τ+1)²·F(τ)` with `σ=−1/τ`,
`w=σ−2`. Together with `quarticDefect_add_two` these are the two weight-2 generator transformations
exhibiting `F` as a weight-2 modular form for `Γ(2)` (the SlashInvariantForm framework prerequisites). -/
theorem quarticDefect_lowerTri {τ : ℂ} (hτ : 0 < τ.im) :
    quarticDefect (τ / (2 * τ + 1)) = (2 * τ + 1) ^ 2 * quarticDefect τ := by
  have hτ0 : τ ≠ 0 := by rintro rfl; simp at hτ
  have h2 : 2 * τ + 1 ≠ 0 := by
    intro h; apply absurd hτ; rw [show τ = -1/2 by linear_combination h / 2]; norm_num
  set σ : ℂ := -1 / τ with hσ
  have hσim : 0 < σ.im := im_neg_inv_pos hτ
  set w : ℂ := σ - 2 with hw
  have hwim : 0 < w.im := by rw [hw, Complex.sub_im]; simpa using hσim
  have hwne : w ≠ 0 := fun h => by rw [h] at hwim; simp at hwim
  have heq : τ / (2 * τ + 1) = -1 / w := by
    rw [div_eq_div_iff h2 hwne, hw, hσ]; field_simp; ring
  have e2 : quarticDefect w = quarticDefect σ := by
    have hp := quarticDefect_add_two (σ - 2)
    rw [show σ - 2 + 2 = σ by ring] at hp
    rw [hw]; exact hp.symm
  have e3 : quarticDefect σ = -τ ^ 2 * quarticDefect τ := by rw [hσ]; exact quarticDefect_S hτ
  rw [heq, quarticDefect_S hwim, e2, e3, hw, hσ]
  field_simp
  ring

end Bottcher


namespace Bottcher

/-- `F = θ₃⁴ − θ₂⁴ − θ₄⁴` is holomorphic on `ℍ` (each nullwert is). Needed for the `ModularForm`
structure on the quartic defect. -/
theorem differentiableAt_quarticDefect {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ quarticDefect τ := by
  have h : quarticDefect = fun z => thetaThree z ^ 4 - thetaTwo z ^ 4 - thetaFour z ^ 4 := by
    funext z; rw [quarticDefect]
  rw [h]
  exact (((differentiableAt_thetaThree hτ).pow 4).sub
    ((differentiableAt_thetaTwo hτ).pow 4)).sub ((differentiableAt_thetaFour hτ).pow 4)

end Bottcher
