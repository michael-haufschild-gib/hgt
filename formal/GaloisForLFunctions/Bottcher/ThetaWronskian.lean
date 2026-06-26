/-
# The theta Wronskian identity `θ₂'θ₃ − θ₂θ₃' = (πi/4)θ₂θ₃θ₄⁴` — weight-6 route

`ThetaWronskian23` (the gate to `λ' ≠ 0`, `ModularLambdaLocalBiholo`) is equivalent to the vanishing of
the **weight-6 Rankin–Cohen defect**

  `D₆(τ) := (θ₂⁴)'(τ)·θ₃⁴(τ) − θ₂⁴(τ)·(θ₃⁴)'(τ) − πi·θ₂⁴θ₃⁴θ₄⁴(τ)`.

Dividing the bracket out: `(θ₂⁴)'θ₃⁴ − θ₂⁴(θ₃⁴)' = 4θ₂³θ₃³·(θ₂'θ₃ − θ₂θ₃')`, so `D₆ = 0` collapses (after
dividing by `4θ₂³θ₃³ ≠ 0`) to exactly `θ₂'θ₃ − θ₂θ₃' = (πi/4)θ₂θ₃θ₄⁴`.

The point of the weight-6 form is that `D₆` is **`SL(2,ℤ)`-sign-covariant** (`D₆(τ+1) = −D₆(τ)`; the
Rankin–Cohen bracket `[θ₂⁴,θ₃⁴]₁ = [θ₂⁴,θ₄⁴]₁` collapses by `θ₃⁴ = θ₂⁴+θ₄⁴`, picking up the same `−1`
the product `θ₂⁴θ₃⁴θ₄⁴` does), so the very `F² ∈ S₄(SL(2,ℤ)) = 0` trick that proved the Jacobi quartic
identity applies: `D₆² ∈ ModularForm 𝒮ℒ 12`, `D₆ = O(q²)` at `i∞`, Sturm ⟹ `D₆² = 0 ⟹ D₆ = 0`.

This file builds the algebraic skeleton: the defect, the `4th`-power derivatives, and the reduction
`D₆ ≡ 0 ⟹ ThetaWronskian23`. The remaining (modular) input is the vanishing `D₆ ≡ 0`.

Consumes `ModularLambdaLocalBiholo` (`ThetaWronskian23`) + `ThetaNullwert` (nullwert derivatives).
-/
import GaloisForLFunctions.Bottcher.ModularLambdaLocalBiholo

open Complex
open scoped Real

namespace Bottcher

/-- The **weight-6 Rankin–Cohen defect** `D₆ = (θ₂⁴)'θ₃⁴ − θ₂⁴(θ₃⁴)' − πi·θ₂⁴θ₃⁴θ₄⁴`. Its vanishing is
equivalent to `ThetaWronskian23`. -/
noncomputable def thetaWronskianDefect (τ : ℂ) : ℂ :=
  deriv (fun t => thetaTwo t ^ 4) τ * thetaThree τ ^ 4
    - thetaTwo τ ^ 4 * deriv (fun t => thetaThree t ^ 4) τ
    - (π : ℂ) * I * (thetaTwo τ ^ 4 * thetaThree τ ^ 4 * thetaFour τ ^ 4)

/-- `(θ₂⁴)'(τ) = 4·θ₂(τ)³·θ₂'(τ)`. -/
theorem hasDerivAt_thetaTwo_pow4 {τ : ℂ} (hτ : 0 < τ.im) :
    HasDerivAt (fun t => thetaTwo t ^ 4) (4 * thetaTwo τ ^ 3 * deriv thetaTwo τ) τ := by
  have hp := (hasDerivAt_thetaTwo hτ).pow 4
  rw [(hasDerivAt_thetaTwo hτ).deriv]
  convert hp using 1

theorem deriv_thetaTwo_pow4 {τ : ℂ} (hτ : 0 < τ.im) :
    deriv (fun t => thetaTwo t ^ 4) τ = 4 * thetaTwo τ ^ 3 * deriv thetaTwo τ :=
  (hasDerivAt_thetaTwo_pow4 hτ).deriv

/-- `(θ₃⁴)'(τ) = 4·θ₃(τ)³·θ₃'(τ)`. -/
theorem hasDerivAt_thetaThree_pow4 {τ : ℂ} (hτ : 0 < τ.im) :
    HasDerivAt (fun t => thetaThree t ^ 4) (4 * thetaThree τ ^ 3 * deriv thetaThree τ) τ := by
  have hp := (hasDerivAt_thetaThree hτ).pow 4
  rw [(hasDerivAt_thetaThree hτ).deriv]
  convert hp using 1

theorem deriv_thetaThree_pow4 {τ : ℂ} (hτ : 0 < τ.im) :
    deriv (fun t => thetaThree t ^ 4) τ = 4 * thetaThree τ ^ 3 * deriv thetaThree τ :=
  (hasDerivAt_thetaThree_pow4 hτ).deriv

/-- **Algebraic reduction.** If the weight-6 defect vanishes on `ℍ`, then the theta Wronskian
identity holds: `θ₂'θ₃ − θ₂θ₃' = (πi/4)θ₂θ₃θ₄⁴`. (Divide `D₆ = 4θ₂³θ₃³(θ₂'θ₃−θ₂θ₃') − πiθ₂⁴θ₃⁴θ₄⁴`
by `4θ₂³θ₃³ ≠ 0`.) -/
theorem thetaWronskian23_of_defect
    (hD : ∀ τ : ℂ, 0 < τ.im → thetaWronskianDefect τ = 0) : ThetaWronskian23 := by
  intro τ hτ
  have h2 : thetaTwo τ ≠ 0 := thetaTwo_ne_zero_of_im_pos hτ
  have h3 : thetaThree τ ≠ 0 := thetaThree_ne_zero_of_im_pos hτ
  have hd := hD τ hτ
  rw [thetaWronskianDefect, deriv_thetaTwo_pow4 hτ, deriv_thetaThree_pow4 hτ] at hd
  -- hd : 4θ₂³(θ₂')θ₃⁴ − θ₂⁴·4θ₃³(θ₃') − πiθ₂⁴θ₃⁴θ₄⁴ = 0
  have hne : (4 : ℂ) * thetaTwo τ ^ 3 * thetaThree τ ^ 3 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 3 h2)) (pow_ne_zero 3 h3)
  apply mul_left_cancel₀ hne
  linear_combination hd

/-- `(θ₄⁴)'(τ) = 4·θ₄(τ)³·θ₄'(τ)`. -/
theorem hasDerivAt_thetaFour_pow4 {τ : ℂ} (hτ : 0 < τ.im) :
    HasDerivAt (fun t => thetaFour t ^ 4) (4 * thetaFour τ ^ 3 * deriv thetaFour τ) τ := by
  have hp := (hasDerivAt_thetaFour hτ).pow 4
  rw [(hasDerivAt_thetaFour hτ).deriv]
  convert hp using 1

theorem deriv_thetaFour_pow4 {τ : ℂ} (hτ : 0 < τ.im) :
    deriv (fun t => thetaFour t ^ 4) τ = 4 * thetaFour τ ^ 3 * deriv thetaFour τ :=
  (hasDerivAt_thetaFour_pow4 hτ).deriv

/-! ### `T`-anti-invariance `D₆(τ+1) = −D₆(τ)`. -/

/-- `θ₂⁴(τ+1) = −θ₂⁴(τ)` (`θ₂(τ+1)=e^{πi/4}θ₂`, `e^{πi}=−1`). -/
theorem thetaTwo_pow4_add_one (τ : ℂ) : thetaTwo (τ + 1) ^ 4 = - thetaTwo τ ^ 4 := by
  rw [thetaTwo_add_one, mul_pow, ← Complex.exp_nat_mul,
      show ((4 : ℕ) : ℂ) * ((Real.pi : ℂ) * I / 4) = (Real.pi : ℂ) * I by push_cast; ring,
      Complex.exp_pi_mul_I]
  ring

/-- `θ₃⁴(τ+1) = θ₄⁴(τ)`. -/
theorem thetaThree_pow4_add_one (τ : ℂ) : thetaThree (τ + 1) ^ 4 = thetaFour τ ^ 4 := by
  rw [thetaThree_add_one]

/-- `θ₄⁴(τ+1) = θ₃⁴(τ)`. -/
theorem thetaFour_pow4_add_one (τ : ℂ) : thetaFour (τ + 1) ^ 4 = thetaThree τ ^ 4 := by
  rw [thetaFour_add_one]

private theorem im_add_one_pos {τ : ℂ} (hτ : 0 < τ.im) : 0 < (τ + 1).im := by
  rw [Complex.add_im, Complex.one_im]; simpa using hτ

/-- Shift transfer of derivative: if `g(t+1) = h(t)` on `ℂ`, then `g'(τ+1) = h'(τ)`. -/
private theorem deriv_shift_eq {g h : ℂ → ℂ} {τ : ℂ}
    (hg : DifferentiableAt ℂ g (τ + 1)) (hh : DifferentiableAt ℂ h τ)
    (hid : ∀ t, g (t + 1) = h t) : deriv g (τ + 1) = deriv h τ := by
  have hcomp : HasDerivAt (fun t => g (t + 1)) (deriv g (τ + 1)) τ := by
    have h1 := hg.hasDerivAt.comp τ ((hasDerivAt_id τ).add_const 1)
    simpa using h1
  rw [funext hid] at hcomp
  exact hcomp.unique hh.hasDerivAt

/-- `(θ₂⁴)'(τ+1) = −(θ₂⁴)'(τ)`. -/
theorem deriv_thetaTwo_pow4_add_one {τ : ℂ} (hτ : 0 < τ.im) :
    deriv (fun t => thetaTwo t ^ 4) (τ + 1) = - deriv (fun t => thetaTwo t ^ 4) τ := by
  rw [deriv_shift_eq (hasDerivAt_thetaTwo_pow4 (im_add_one_pos hτ)).differentiableAt
        ((hasDerivAt_thetaTwo_pow4 hτ).neg).differentiableAt (fun t => thetaTwo_pow4_add_one t),
      (hasDerivAt_thetaTwo_pow4 hτ).neg.deriv, deriv_thetaTwo_pow4 hτ]

/-- `(θ₃⁴)'(τ+1) = (θ₄⁴)'(τ)`. -/
theorem deriv_thetaThree_pow4_add_one {τ : ℂ} (hτ : 0 < τ.im) :
    deriv (fun t => thetaThree t ^ 4) (τ + 1) = deriv (fun t => thetaFour t ^ 4) τ :=
  deriv_shift_eq (hasDerivAt_thetaThree_pow4 (im_add_one_pos hτ)).differentiableAt
    (hasDerivAt_thetaFour_pow4 hτ).differentiableAt (fun t => thetaThree_pow4_add_one t)

/-- Jacobi quartic identity in power form: `θ₃⁴ = θ₂⁴ + θ₄⁴`. -/
theorem pow4_jacobi {τ : ℂ} (hτ : 0 < τ.im) :
    thetaThree τ ^ 4 = thetaTwo τ ^ 4 + thetaFour τ ^ 4 := by
  have hF := Bottcher2Cusp.quarticDefect_eq_zero hτ
  rw [quarticDefect] at hF
  linear_combination hF

/-- Derivative of the Jacobi identity: `4θ₃³θ₃' = 4θ₂³θ₂' + 4θ₄³θ₄'` (from `F ≡ 0 ⟹ F' = 0`). -/
theorem deriv_pow4_jacobi {τ : ℂ} (hτ : 0 < τ.im) :
    4 * thetaThree τ ^ 3 * deriv thetaThree τ
      = 4 * thetaTwo τ ^ 3 * deriv thetaTwo τ + 4 * thetaFour τ ^ 3 * deriv thetaFour τ := by
  have hU : {σ : ℂ | 0 < σ.im} ∈ nhds τ :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hτ
  have hev : quarticDefect =ᶠ[nhds τ] (fun _ : ℂ => (0 : ℂ)) := by
    filter_upwards [hU] with σ hσ using Bottcher2Cusp.quarticDefect_eq_zero hσ
  have hz : HasDerivAt quarticDefect 0 τ :=
    (hasDerivAt_const τ (0 : ℂ)).congr_of_eventuallyEq hev
  have he := (hasDerivAt_quarticDefect hτ).unique hz
  linear_combination he

/-- **`D₆(τ+1) = −D₆(τ)`** (the `T`-anti-invariance). Under `τ ↦ τ+1`: `θ₂⁴ ↦ −θ₂⁴`, `θ₃⁴ ↦ θ₄⁴`,
`θ₄⁴ ↦ θ₃⁴`, and the same on derivatives; the Rankin–Cohen bracket collapses against the Jacobi
identity (`pow4_jacobi`, `deriv_pow4_jacobi`) to flip the overall sign. -/
theorem thetaWronskianDefect_add_one {τ : ℂ} (hτ : 0 < τ.im) :
    thetaWronskianDefect (τ + 1) = - thetaWronskianDefect τ := by
  simp only [thetaWronskianDefect]
  rw [deriv_thetaTwo_pow4_add_one hτ, deriv_thetaThree_pow4_add_one hτ,
      thetaTwo_pow4_add_one, thetaThree_pow4_add_one, thetaFour_pow4_add_one,
      deriv_thetaTwo_pow4 hτ, deriv_thetaThree_pow4 hτ, deriv_thetaFour_pow4 hτ]
  have hJ := pow4_jacobi hτ
  have hdJ := deriv_pow4_jacobi hτ
  linear_combination (4 * thetaTwo τ ^ 3 * deriv thetaTwo τ) * hJ - thetaTwo τ ^ 4 * hdJ

/-! ### `S`-anti-invariance `D₆(−1/τ) = −τ⁶·D₆(τ)`. -/

/-- `(z^{1/2})⁴ = z²` for `z ≠ 0` (the half-power automorphy factor cleans up at the 4th power). -/
private theorem cpow_half_pow4 {z : ℂ} (hz : z ≠ 0) : (z ^ (1/2 : ℂ)) ^ 4 = z ^ 2 := by
  have h2 : (z ^ (1/2 : ℂ)) ^ 2 = z := by
    rw [sq, ← Complex.cpow_add _ _ hz, show (1/2 + 1/2 : ℂ) = 1 by norm_num, Complex.cpow_one]
  calc (z ^ (1/2 : ℂ)) ^ 4 = ((z ^ (1/2 : ℂ)) ^ 2) ^ 2 := by ring
    _ = z ^ 2 := by rw [h2]

/-- `θ₃⁴(−1/τ) = −τ²·θ₃⁴(τ)`. -/
theorem thetaThree_pow4_S {τ : ℂ} (hτ : τ ≠ 0) :
    thetaThree (-1/τ) ^ 4 = - τ ^ 2 * thetaThree τ ^ 4 := by
  rw [thetaThree_S τ hτ, mul_pow, cpow_half_pow4 (mul_ne_zero (by simp) hτ)]
  rw [show ((-I * τ) ^ 2 : ℂ) = - τ ^ 2 by rw [mul_pow, neg_sq, Complex.I_sq]; ring]

/-- `θ₂⁴(−1/τ) = −τ²·θ₄⁴(τ)`. -/
theorem thetaTwo_pow4_S {τ : ℂ} (hτ : τ ≠ 0) :
    thetaTwo (-1/τ) ^ 4 = - τ ^ 2 * thetaFour τ ^ 4 := by
  rw [thetaTwo_S τ hτ, mul_pow, div_pow, one_pow, cpow_half_pow4 (div_ne_zero Complex.I_ne_zero hτ)]
  rw [show (1 : ℂ) / (I / τ) ^ 2 = - τ ^ 2 by
    rw [div_pow, Complex.I_sq, one_div, neg_div, inv_neg, one_div, inv_inv]]

/-- `θ₄⁴(−1/τ) = −τ²·θ₂⁴(τ)`. -/
theorem thetaFour_pow4_S {τ : ℂ} (hτ : τ ≠ 0) :
    thetaFour (-1/τ) ^ 4 = - τ ^ 2 * thetaTwo τ ^ 4 := by
  rw [thetaFour_S τ hτ, mul_pow, div_pow, one_pow, cpow_half_pow4 (div_ne_zero Complex.I_ne_zero hτ)]
  rw [show (1 : ℂ) / (I / τ) ^ 2 = - τ ^ 2 by
    rw [div_pow, Complex.I_sq, one_div, neg_div, inv_neg, one_div, inv_inv]]

end Bottcher
