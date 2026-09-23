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
open scoped Real Topology

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
  rw [show (fun t => thetaTwo t ^ 4) = thetaTwo ^ 4 by
    funext t
    rfl]
  apply hp.congr_deriv
  rw [(hasDerivAt_thetaTwo hτ).deriv]
  push_cast
  ring

theorem deriv_thetaTwo_pow4 {τ : ℂ} (hτ : 0 < τ.im) :
    deriv (fun t => thetaTwo t ^ 4) τ = 4 * thetaTwo τ ^ 3 * deriv thetaTwo τ :=
  (hasDerivAt_thetaTwo_pow4 hτ).deriv

/-- `(θ₃⁴)'(τ) = 4·θ₃(τ)³·θ₃'(τ)`. -/
theorem hasDerivAt_thetaThree_pow4 {τ : ℂ} (hτ : 0 < τ.im) :
    HasDerivAt (fun t => thetaThree t ^ 4) (4 * thetaThree τ ^ 3 * deriv thetaThree τ) τ := by
  have hp := (hasDerivAt_thetaThree hτ).pow 4
  rw [show (fun t => thetaThree t ^ 4) = thetaThree ^ 4 by
    funext t
    rfl]
  apply hp.congr_deriv
  rw [(hasDerivAt_thetaThree hτ).deriv]
  push_cast
  ring

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
  rw [show (fun t => thetaFour t ^ 4) = thetaFour ^ 4 by
    funext t
    rfl]
  apply hp.congr_deriv
  rw [(hasDerivAt_thetaFour hτ).deriv]
  push_cast
  ring

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
    rw [show (fun t => g (t + 1)) = g ∘ (fun t => id t + 1) by rfl]
    exact h1.congr_deriv (by ring)
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

private theorem im_neg_inv_pos {τ : ℂ} (hτ : 0 < τ.im) : 0 < (-1 / τ).im := by
  have hz0 : τ ≠ 0 := by rintro rfl; simp at hτ
  have hn : 0 < Complex.normSq τ := Complex.normSq_pos.mpr hz0
  rw [neg_div, Complex.neg_im, Complex.div_im]
  simp only [Complex.one_im, Complex.one_re, zero_mul, zero_div, one_mul, zero_sub, neg_neg]
  exact div_pos hτ hn

/-- `S`-substitution transfer of derivative: if `g(−1/t) = h(t)` near `τ`, then `g'(−1/τ)·(1/τ²) = h'(τ)`
(chain rule for `t ↦ −1/t`, whose derivative is `1/τ²`). -/
private theorem deriv_S_shift {g h : ℂ → ℂ} {τ : ℂ} (hτ : τ ≠ 0)
    (hg : DifferentiableAt ℂ g (-1 / τ)) (hh : DifferentiableAt ℂ h τ)
    (hid : (fun t => g (-1 / t)) =ᶠ[nhds τ] h) :
    deriv g (-1 / τ) * (1 / τ ^ 2) = deriv h τ := by
  have hinv : HasDerivAt (fun t : ℂ => -1 / t) (1 / τ ^ 2) τ := by
    rw [show (fun t : ℂ => -1 / t) = -(fun t : ℂ => t⁻¹) by
      funext t
      simp [neg_div, one_div]]
    apply (hasDerivAt_inv hτ).neg.congr_deriv
    field_simp
  have hcomp : HasDerivAt (fun t => g (-1 / t)) (deriv g (-1 / τ) * (1 / τ ^ 2)) τ :=
    hg.hasDerivAt.comp τ hinv
  exact (hcomp.congr_of_eventuallyEq hid.symm).unique hh.hasDerivAt

/-- `(θ₂⁴)'(−1/τ) = −2τ³θ₄⁴ − τ⁴(θ₄⁴)'`. -/
theorem deriv_thetaTwo_pow4_S {τ : ℂ} (hτ : 0 < τ.im) :
    deriv (fun t => thetaTwo t ^ 4) (-1 / τ)
      = -2 * τ ^ 3 * thetaFour τ ^ 4 - τ ^ 4 * deriv (fun t => thetaFour t ^ 4) τ := by
  have hτ0 : τ ≠ 0 := fun h => by simp [h] at hτ
  have hHder : HasDerivAt (fun t => -t ^ 2 * thetaFour t ^ 4)
      (-(2 * τ) * thetaFour τ ^ 4 + -τ ^ 2 * (4 * thetaFour τ ^ 3 * deriv thetaFour τ)) τ := by
    have h1 : HasDerivAt (fun t : ℂ => -t ^ 2) (-(2 * τ)) τ := by
      rw [show (fun t : ℂ => -t ^ 2) = -(fun t : ℂ => t ^ 2) by
        funext t
        rfl]
      apply (hasDerivAt_pow 2 τ).neg.congr_deriv
      push_cast
      ring
    exact h1.mul (hasDerivAt_thetaFour_pow4 hτ)
  have hid : ∀ᶠ t in nhds τ, thetaTwo (-1 / t) ^ 4 = (fun t => -t ^ 2 * thetaFour t ^ 4) t := by
    filter_upwards [isOpen_ne.mem_nhds hτ0] with t ht using thetaTwo_pow4_S ht
  have hshift := deriv_S_shift hτ0 (hasDerivAt_thetaTwo_pow4 (im_neg_inv_pos hτ)).differentiableAt
    hHder.differentiableAt hid
  rw [hHder.deriv, mul_one_div, div_eq_iff (pow_ne_zero 2 hτ0)] at hshift
  rw [deriv_thetaFour_pow4 hτ]
  linear_combination hshift

/-- `(θ₃⁴)'(−1/τ) = −2τ³θ₃⁴ − τ⁴(θ₃⁴)'`. -/
theorem deriv_thetaThree_pow4_S {τ : ℂ} (hτ : 0 < τ.im) :
    deriv (fun t => thetaThree t ^ 4) (-1 / τ)
      = -2 * τ ^ 3 * thetaThree τ ^ 4 - τ ^ 4 * deriv (fun t => thetaThree t ^ 4) τ := by
  have hτ0 : τ ≠ 0 := fun h => by simp [h] at hτ
  have hHder : HasDerivAt (fun t => -t ^ 2 * thetaThree t ^ 4)
      (-(2 * τ) * thetaThree τ ^ 4 + -τ ^ 2 * (4 * thetaThree τ ^ 3 * deriv thetaThree τ)) τ := by
    have h1 : HasDerivAt (fun t : ℂ => -t ^ 2) (-(2 * τ)) τ := by
      rw [show (fun t : ℂ => -t ^ 2) = -(fun t : ℂ => t ^ 2) by
        funext t
        rfl]
      apply (hasDerivAt_pow 2 τ).neg.congr_deriv
      push_cast
      ring
    exact h1.mul (hasDerivAt_thetaThree_pow4 hτ)
  have hid : ∀ᶠ t in nhds τ, thetaThree (-1 / t) ^ 4 = (fun t => -t ^ 2 * thetaThree t ^ 4) t := by
    filter_upwards [isOpen_ne.mem_nhds hτ0] with t ht using thetaThree_pow4_S ht
  have hshift := deriv_S_shift hτ0 (hasDerivAt_thetaThree_pow4 (im_neg_inv_pos hτ)).differentiableAt
    hHder.differentiableAt hid
  rw [hHder.deriv, mul_one_div, div_eq_iff (pow_ne_zero 2 hτ0)] at hshift
  rw [deriv_thetaThree_pow4 hτ]
  linear_combination hshift

/-- Derivative-Jacobi in `4th`-power-derivative form: `(θ₃⁴)' = (θ₂⁴)' + (θ₄⁴)'`. -/
theorem deriv_pow4_jacobi' {τ : ℂ} (hτ : 0 < τ.im) :
    deriv (fun t => thetaThree t ^ 4) τ
      = deriv (fun t => thetaTwo t ^ 4) τ + deriv (fun t => thetaFour t ^ 4) τ := by
  rw [deriv_thetaThree_pow4 hτ, deriv_thetaTwo_pow4 hτ, deriv_thetaFour_pow4 hτ]
  exact deriv_pow4_jacobi hτ

/-- **`D₆(−1/τ) = −τ⁶·D₆(τ)`** (the `S`-anti-invariance). With `D₆∣[6]T = −D₆`
(`thetaWronskianDefect_add_one`), this gives `D₆∣[6]γ = ±D₆` for all `γ ∈ SL(2,ℤ)`, so `D₆²` descends
to `ModularForm 𝒮ℒ 12`. -/
theorem thetaWronskianDefect_S {τ : ℂ} (hτ : 0 < τ.im) :
    thetaWronskianDefect (-1 / τ) = - τ ^ 6 * thetaWronskianDefect τ := by
  have hτ0 : τ ≠ 0 := fun h => by simp [h] at hτ
  simp only [thetaWronskianDefect]
  rw [deriv_thetaTwo_pow4_S hτ, deriv_thetaThree_pow4_S hτ,
      thetaThree_pow4_S hτ0, thetaTwo_pow4_S hτ0, thetaFour_pow4_S hτ0]
  linear_combination (τ ^ 6 * deriv (fun t => thetaThree t ^ 4) τ) * pow4_jacobi hτ
    - (τ ^ 6 * thetaThree τ ^ 4) * deriv_pow4_jacobi' hτ

/-! ### Holomorphy of `D₆` on `ℍ`. -/

/-- **`D₆` is holomorphic on `ℍ`.** The derivative terms `(θᵢ⁴)'` are holomorphic because `θᵢ⁴` is
holomorphic on the open set `ℍ` (the derivative of a function holomorphic on an open set is itself
holomorphic — no second-derivative computation needed). -/
theorem differentiableOn_thetaWronskianDefect :
    DifferentiableOn ℂ thetaWronskianDefect {z : ℂ | 0 < z.im} := by
  set U : Set ℂ := {z : ℂ | 0 < z.im} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have h2 : DifferentiableOn ℂ (fun t => thetaTwo t ^ 4) U :=
    fun z hz => (hasDerivAt_thetaTwo_pow4 hz).differentiableAt.differentiableWithinAt
  have h3 : DifferentiableOn ℂ (fun t => thetaThree t ^ 4) U :=
    fun z hz => (hasDerivAt_thetaThree_pow4 hz).differentiableAt.differentiableWithinAt
  have h4 : DifferentiableOn ℂ (fun t => thetaFour t ^ 4) U :=
    fun z hz => (hasDerivAt_thetaFour_pow4 hz).differentiableAt.differentiableWithinAt
  have hd2 : DifferentiableOn ℂ (deriv (fun t => thetaTwo t ^ 4)) U :=
    (h2.analyticOnNhd hUo).deriv.differentiableOn
  have hd3 : DifferentiableOn ℂ (deriv (fun t => thetaThree t ^ 4)) U :=
    (h3.analyticOnNhd hUo).deriv.differentiableOn
  unfold thetaWronskianDefect
  exact ((hd2.mul h3).sub (h2.mul hd3)).sub
    ((differentiableOn_const ((π : ℂ) * I)).mul ((h2.mul h3).mul h4))

/-! ### Sign-covariance of the weight-6 denominator `(θ₂θ₃θ₄)⁴`. -/

/-- `(θ₂θ₃θ₄)⁴(τ+1) = −(θ₂θ₃θ₄)⁴(τ)`. -/
theorem thetaProductPow4_add_one (τ : ℂ) :
    (thetaTwo (τ + 1) * thetaThree (τ + 1) * thetaFour (τ + 1)) ^ 4
      = -(thetaTwo τ * thetaThree τ * thetaFour τ) ^ 4 := by
  rw [thetaProduct_add_one, mul_pow, ← Complex.exp_nat_mul,
      show ((4 : ℕ) : ℂ) * ((Real.pi : ℂ) * I / 4) = (Real.pi : ℂ) * I by push_cast; ring,
      Complex.exp_pi_mul_I]
  ring

/-- `(θ₂θ₃θ₄)⁴(−1/τ) = −τ⁶·(θ₂θ₃θ₄)⁴(τ)` — the automorphy factor `M⁴ = −τ⁶`, matching `D₆`. -/
theorem thetaProductPow4_S {τ : ℂ} (hτ : τ ≠ 0) :
    (thetaTwo (-1 / τ) * thetaThree (-1 / τ) * thetaFour (-1 / τ)) ^ 4
      = -τ ^ 6 * (thetaTwo τ * thetaThree τ * thetaFour τ) ^ 4 := by
  have ha : (1 / (I / τ) ^ (1/2 : ℂ)) ^ 4 = -τ ^ 2 := by
    rw [div_pow, one_pow, cpow_half_pow4 (div_ne_zero Complex.I_ne_zero hτ), div_pow, Complex.I_sq,
        one_div, neg_div, inv_neg, one_div, inv_inv]
  have hb : ((-I * τ) ^ (1/2 : ℂ)) ^ 4 = -τ ^ 2 := by
    rw [cpow_half_pow4 (mul_ne_zero (by simp) hτ), mul_pow, neg_sq, Complex.I_sq]; ring
  rw [thetaProduct_S τ hτ, mul_pow,
      show (1 / (I / τ) ^ (1/2 : ℂ) * (-I * τ) ^ (1/2 : ℂ) * (1 / (I / τ) ^ (1/2 : ℂ))) ^ 4
        = (1 / (I / τ) ^ (1/2 : ℂ)) ^ 4 * ((-I * τ) ^ (1/2 : ℂ)) ^ 4
          * (1 / (I / τ) ^ (1/2 : ℂ)) ^ 4 by ring,
      ha, hb]
  ring

/-! ### The `SL(2,ℤ)`-invariant ratio `P = D₆ / (θ₂θ₃θ₄)⁴`. -/

/-- **`P := D₆ / (θ₂θ₃θ₄)⁴`** — weight-0, `SL(2,ℤ)`-invariant (the `−1` and `−τ⁶` sign factors of `D₆`
and `(θ₂θ₃θ₄)⁴` cancel in the ratio). A holomorphic level-one modular *function*; `ThetaWronskian23`
reduces to `P ≡ 0`, which `ModularFormClass.levelOne_weight_zero_const` + the cusp limit will give. -/
noncomputable def thetaWronskianRatio (τ : ℂ) : ℂ :=
  thetaWronskianDefect τ / (thetaTwo τ * thetaThree τ * thetaFour τ) ^ 4

/-- `P(τ+1) = P(τ)`. -/
theorem thetaWronskianRatio_add_one {τ : ℂ} (hτ : 0 < τ.im) :
    thetaWronskianRatio (τ + 1) = thetaWronskianRatio τ := by
  unfold thetaWronskianRatio
  rw [thetaWronskianDefect_add_one hτ, thetaProductPow4_add_one, neg_div_neg_eq]

/-- `P(−1/τ) = P(τ)`. -/
theorem thetaWronskianRatio_S {τ : ℂ} (hτ : 0 < τ.im) :
    thetaWronskianRatio (-1 / τ) = thetaWronskianRatio τ := by
  have hτ0 : τ ≠ 0 := fun h => by simp [h] at hτ
  unfold thetaWronskianRatio
  rw [thetaWronskianDefect_S hτ, thetaProductPow4_S hτ0,
      mul_div_mul_left _ _ (neg_ne_zero.mpr (pow_ne_zero 6 hτ0))]

/-- `D₆ = P · (θ₂θ₃θ₄)⁴`: recover the defect from the ratio (used to transfer `P ≡ 0` to `D₆ ≡ 0`). -/
theorem thetaWronskianDefect_eq_ratio_mul {τ : ℂ} (hτ : 0 < τ.im) :
    thetaWronskianDefect τ = thetaWronskianRatio τ * (thetaTwo τ * thetaThree τ * thetaFour τ) ^ 4 := by
  unfold thetaWronskianRatio
  rw [div_mul_cancel₀ _ (pow_ne_zero 4 (thetaProduct_ne_zero_of_im_pos hτ))]

/-- **Final reduction: `P ≡ 0 ⟹ ThetaWronskian23`.** `P` is the holomorphic `SL(2,ℤ)`-invariant
weight-0 ratio; the only remaining input to `ThetaWronskian23` (hence to `λ' ≠ 0`) is `P ≡ 0`, which
follows from `P` being a level-one modular function (constant by `levelOne_weight_zero_const`) with
`P → 0` at `i∞`. -/
theorem thetaWronskian23_of_ratio_zero
    (hP : ∀ τ : ℂ, 0 < τ.im → thetaWronskianRatio τ = 0) : ThetaWronskian23 := by
  apply thetaWronskian23_of_defect
  intro τ hτ
  rw [thetaWronskianDefect_eq_ratio_mul hτ, hP τ hτ, zero_mul]

/-! ### Cusp limit `θ₃' → 0` at `i∞` (first step toward `P → 0`). -/

open Filter in
/-- `‖θ₃'`'s `n`-th term`‖ = π·n²·e^{−πn²·im τ}` (the `z = 0` nullwert). -/
theorem norm_jacobiTheta₂_snd_term_zero (n : ℤ) (τ : ℂ) :
    ‖jacobiTheta₂_snd_term n 0 τ‖ = π * (n : ℝ) ^ 2 * Real.exp (-π * (n : ℝ) ^ 2 * τ.im) := by
  rw [jacobiTheta₂_snd_term, norm_mul, norm_jacobiTheta₂_term, Complex.zero_im, mul_zero, sub_zero]
  congr 1
  rw [show (π : ℂ) * I * (n : ℂ) ^ 2 = ((π * (n : ℝ) ^ 2 : ℝ) : ℂ) * I by push_cast; ring,
      norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]

open Filter in
/-- **`θ₃' → 0` as `im τ → ∞`.** The derivative series `θ₃'(τ) = ∑ πin²·q^{n²}` is squeezed by
`C·e^{−π·imτ/2}` (`C = ∑ πn²e^{−πn²/2}`): for `im ≥ 1`, `πn²e^{−πn²·im} ≤ (πn²e^{−πn²/2})·e^{−π·im/2}`. -/
theorem tendsto_deriv_thetaThree_atImInfty :
    Tendsto (deriv thetaThree) (comap Complex.im atTop) (𝓝 0) := by
  have hCsum : Summable (fun n : ℤ => π * (n : ℝ) ^ 2 * Real.exp (-π * (n : ℝ) ^ 2 / 2)) := by
    have h := (summable_pow_mul_jacobiTheta₂_term_bound (0 : ℝ) (by norm_num : (0:ℝ) < 1/2) 2).mul_left π
    refine h.congr (fun n => ?_)
    rw [Int.cast_abs, sq_abs]; ring_nf
  set C : ℝ := ∑' n : ℤ, π * (n : ℝ) ^ 2 * Real.exp (-π * (n : ℝ) ^ 2 / 2) with hC
  have hgto : Tendsto (fun τ : ℂ => C * Real.exp (-π * τ.im / 2)) (comap Complex.im atTop) (𝓝 0) := by
    have : Tendsto (fun τ : ℂ => Real.exp (-π * τ.im / 2)) (comap Complex.im atTop) (𝓝 0) := by
      apply Real.tendsto_exp_atBot.comp
      exact Filter.Tendsto.neg_mul_atTop (by have := Real.pi_pos; linarith : (-π / 2 : ℝ) < 0)
        tendsto_const_nhds tendsto_comap |>.congr (fun τ => by ring)
    simpa using this.const_mul C
  refine squeeze_zero_norm' ?_ hgto
  filter_upwards [tendsto_comap.eventually (eventually_ge_atTop (1 : ℝ))] with τ hτ
  have hτ0 : 0 < τ.im := by linarith
  rw [(hasDerivAt_thetaThree hτ0).deriv]
  have hsummN : Summable (fun n : ℤ => ‖jacobiTheta₂_snd_term n 0 τ‖) := by
    simp_rw [norm_jacobiTheta₂_snd_term_zero]
    have h := (summable_pow_mul_jacobiTheta₂_term_bound (0 : ℝ) hτ0 2).mul_left π
    refine h.congr (fun n => ?_)
    rw [Int.cast_abs, sq_abs]; ring_nf
  refine (norm_tsum_le_tsum_norm hsummN).trans ?_
  rw [tsum_congr (fun n => norm_jacobiTheta₂_snd_term_zero n τ)]
  rw [show C * Real.exp (-π * τ.im / 2)
      = ∑' n : ℤ, π * (n : ℝ) ^ 2 * Real.exp (-π * (n : ℝ) ^ 2 / 2) * Real.exp (-π * τ.im / 2) by
    rw [hC, ← tsum_mul_right]]
  have hsummN' : Summable (fun n : ℤ => π * (n : ℝ) ^ 2 * Real.exp (-π * (n : ℝ) ^ 2 * τ.im)) := by
    simp_rw [norm_jacobiTheta₂_snd_term_zero] at hsummN; exact hsummN
  refine Summable.tsum_mono hsummN' (hCsum.mul_right _) (fun n => ?_)
  rcases eq_or_ne n 0 with hn | hn
  · simp [hn]
  · have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
      have hz : (1 : ℤ) ≤ n ^ 2 := by nlinarith [Int.one_le_abs hn, sq_abs n]
      exact_mod_cast hz
    calc π * (n : ℝ) ^ 2 * Real.exp (-π * (n : ℝ) ^ 2 * τ.im)
        ≤ π * (n : ℝ) ^ 2 * Real.exp (-π * (n : ℝ) ^ 2 / 2 + -π * τ.im / 2) := by
          gcongr π * (n : ℝ) ^ 2 * Real.exp ?_
          nlinarith [Real.pi_pos, hτ, hn2,
            mul_nonneg (sub_nonneg.2 hn2) (by linarith : (0 : ℝ) ≤ 2 * τ.im - 1)]
      _ = π * (n : ℝ) ^ 2 * Real.exp (-π * (n : ℝ) ^ 2 / 2) * Real.exp (-π * τ.im / 2) := by
          rw [Real.exp_add]; ring

/-! ### Cusp limit `Θ(τ/2,τ) → 2` (the `θ₂`-diagonal nullwert). -/

open Filter in
/-- **`jacobiTheta₂(τ/2, τ) → 2`** as `im τ → ∞`. The two terms `n = 0, −1` both equal `1` (their
exponents vanish on the diagonal `z = τ/2`); the rest decay (`n(n+1) ≥ 2`), squeezed by `C·e^{−π·imτ}`. -/
theorem tendsto_jacobiTheta₂_diag_atImInfty :
    Tendsto (fun τ : ℂ => jacobiTheta₂ (τ / 2) τ) (comap Complex.im atTop) (𝓝 2) := by
  have hC'' : Summable (fun n : ℤ => Real.exp (-π * ((n : ℝ) ^ 2 + n) / 2)) := by
    refine (summable_exp_neg_half (1/2 : ℝ) (by norm_num)).congr (fun n => ?_)
    rw [show (-π * ((n : ℝ) ^ 2 + (n : ℝ)) * (1/2 : ℝ)) = -π * ((n : ℝ) ^ 2 + n) / 2 by ring]
  set C'' : ℝ := ∑' n : ℤ, Real.exp (-π * ((n : ℝ) ^ 2 + n) / 2) with hC''def
  suffices hsub : Tendsto (fun τ : ℂ => jacobiTheta₂ (τ / 2) τ - 2) (comap Complex.im atTop) (𝓝 0) by
    simpa using hsub.add_const 2
  have hgto : Tendsto (fun τ : ℂ => C'' * Real.exp (-π * τ.im)) (comap Complex.im atTop) (𝓝 0) := by
    simpa using tendsto_exp_neg_pi_im.const_mul C''
  refine squeeze_zero_norm' ?_ hgto
  filter_upwards [tendsto_comap.eventually (eventually_ge_atTop (1 : ℝ))] with τ hτ
  have hτ0 : 0 < τ.im := by linarith
  have hsumm : Summable (fun n : ℤ => jacobiTheta₂_term n (τ / 2) τ) :=
    (summable_jacobiTheta₂_term_iff (τ / 2) τ).2 hτ0
  have hsum2 : (∑ i ∈ ({0, -1} : Finset ℤ), jacobiTheta₂_term i (τ / 2) τ) = 2 := by
    rw [Finset.sum_pair (by decide),
        show jacobiTheta₂_term 0 (τ / 2) τ = 1 by rw [jacobiTheta₂_term]; simp,
        show jacobiTheta₂_term (-1) (τ / 2) τ = 1 by
          rw [jacobiTheta₂_term,
            show (2 * ↑π * I * ((-1 : ℤ) : ℂ) * (τ / 2) + ↑π * I * ((-1 : ℤ) : ℂ) ^ 2 * τ : ℂ) = 0 by
              push_cast; ring, Complex.exp_zero]]
    norm_num
  have hΘsub : jacobiTheta₂ (τ / 2) τ - 2
      = ∑' (i : ↥((↑({0, -1} : Finset ℤ) : Set ℤ)ᶜ)), jacobiTheta₂_term i (τ / 2) τ := by
    have h := hsumm.sum_add_tsum_compl (s := ({0, -1} : Finset ℤ))
    rw [hsum2] at h
    rw [show jacobiTheta₂ (τ / 2) τ = ∑' n, jacobiTheta₂_term n (τ / 2) τ from rfl]
    linear_combination -h
  rw [hΘsub]
  have hzim : ((τ / 2 : ℂ)).im = τ.im / 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.div_ofReal_im]
  have hnorm : ∀ n : ℤ, ‖jacobiTheta₂_term n (τ / 2) τ‖
      = Real.exp (-π * ((n : ℝ) ^ 2 + n) * τ.im) := by
    intro n; rw [norm_jacobiTheta₂_term, hzim]; congr 1; ring
  have hsummNorm : Summable (fun n : ℤ => ‖jacobiTheta₂_term n (τ / 2) τ‖) := by
    simp_rw [hnorm]; exact summable_exp_neg_half τ.im hτ0
  have hBsum : Summable (fun n : ℤ => Real.exp (-π * ((n : ℝ) ^ 2 + n) / 2) * Real.exp (-π * τ.im)) :=
    hC''.mul_right _
  refine (norm_tsum_le_tsum_norm (hsummNorm.subtype _)).trans ?_
  refine (Summable.tsum_mono (hsummNorm.subtype _) (hBsum.subtype _) (fun i => ?_)).trans ?_
  · have hi : (i : ℤ) ≠ 0 ∧ (i : ℤ) ≠ -1 := by
      have h := i.2
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_compl_iff, Set.mem_insert_iff,
        Set.mem_singleton_iff, not_or] at h
      exact h
    have hge : (2 : ℝ) ≤ ((i : ℤ) : ℝ) ^ 2 + ((i : ℤ) : ℝ) := by
      have h2 : (2 : ℤ) ≤ (i : ℤ) ^ 2 + (i : ℤ) := by
        rcases lt_or_gt_of_ne hi.1 with h | h
        · have : (i : ℤ) ≤ -2 := by omega
          nlinarith
        · have : (1 : ℤ) ≤ (i : ℤ) := by omega
          nlinarith
      exact_mod_cast h2
    simp only [Function.comp_apply]
    rw [hnorm, ← Real.exp_add, Real.exp_le_exp]
    nlinarith [Real.pi_pos, hτ, hge,
      mul_nonneg (mul_nonneg Real.pi_pos.le (sub_nonneg.2 hge)) (by linarith : (0 : ℝ) ≤ τ.im - 1/2),
      mul_nonneg Real.pi_pos.le (by linarith : (0 : ℝ) ≤ τ.im - 1)]
  · rw [hC''def, ← tsum_mul_right]
    exact Summable.tsum_subtype_le _ _ (fun n => by positivity) hBsum

/-! ### Cusp limit `Θ_deriv(τ) := jacobiTheta₂_fderiv(τ/2,τ)(1/2,1) → 0`. -/

/-- The diagonal fderiv term: `term_fderiv n (τ/2) τ (1/2,1) = πin(n+1)·term`. -/
theorem jacobiTheta₂_term_fderiv_diag (n : ℤ) (τ : ℂ) :
    (jacobiTheta₂_term_fderiv n (τ / 2) τ) (1/2, 1)
      = (π : ℂ) * I * n * (n + 1) * jacobiTheta₂_term n (τ / 2) τ := by
  rw [jacobiTheta₂_term_fderiv, jacobiTheta₂_term]
  simp only [_root_.smul_apply, _root_.add_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
  ring

/-- The `θ₂`-diagonal derivative `Θ_deriv(τ) = jacobiTheta₂_fderiv(τ/2,τ)(1/2,1)`. By `hasDerivAt_thetaTwo`
this is the non-prefactor part of `θ₂'`. -/
noncomputable def jacobiTheta₂DiagDeriv (τ : ℂ) : ℂ := (jacobiTheta₂_fderiv (τ / 2) τ) (1/2, 1)

theorem jacobiTheta₂DiagDeriv_tsum {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta₂DiagDeriv τ = ∑' n : ℤ, (π : ℂ) * I * n * (n + 1) * jacobiTheta₂_term n (τ / 2) τ := by
  let evalCLM : (ℂ × ℂ →L[ℂ] ℂ) →L[ℂ] ℂ :=
    { toFun := fun f => f (1/2, 1), map_add' := fun f g => rfl, map_smul' := fun c f => rfl,
      cont := by fun_prop }
  have h := evalCLM.hasSum (hasSum_jacobiTheta₂_term_fderiv (τ / 2) hτ)
  have heq : (fun n : ℤ => evalCLM (jacobiTheta₂_term_fderiv n (τ / 2) τ))
      = fun n => (π : ℂ) * I * n * (n + 1) * jacobiTheta₂_term n (τ / 2) τ := by
    funext n; exact jacobiTheta₂_term_fderiv_diag n τ
  rw [show jacobiTheta₂DiagDeriv τ = evalCLM (jacobiTheta₂_fderiv (τ / 2) τ) from rfl,
      ← h.tsum_eq, heq]


/-- The summand `π(n²+n)·e^{−π(n²+n)·y}`, **named** so `tsum`/`isDefEq` treat it as an atom (the
expanded form triggers an exponential `isDefEq` blowup inside `Summable.tsum_mono`). -/
private noncomputable def polyExpTerm (y : ℝ) (n : ℤ) : ℝ :=
  π * ((n : ℝ) ^ 2 + n) * Real.exp (-π * ((n : ℝ) ^ 2 + n) * y)

private theorem nn_sq_add {n : ℤ} : (0 : ℝ) ≤ (n : ℝ) ^ 2 + n := by
  have h : (0 : ℤ) ≤ n ^ 2 + n := by nlinarith [sq_nonneg (2 * n + 1)]
  exact_mod_cast h

private theorem summable_polyExpTerm {y : ℝ} (hy : 0 < y) : Summable (polyExpTerm y) := by
  unfold polyExpTerm
  have hb : Summable (fun n : ℤ =>
      π * ((|(n : ℝ)| ^ 2 + |(n : ℝ)|) * Real.exp (-π * (y * (n : ℝ) ^ 2 - y * |(n : ℝ)|)))) := by
    have h := (((summable_pow_mul_jacobiTheta₂_term_bound (y / 2) hy 2).add
      (summable_pow_mul_jacobiTheta₂_term_bound (y / 2) hy 1)).mul_left π)
    refine h.congr (fun n => ?_)
    rw [Int.cast_abs, sq_abs]; ring_nf
  refine Summable.of_nonneg_of_le (fun n => by have := @nn_sq_add n; positivity) (fun n => ?_) hb
  have hexp : Real.exp (-π * ((n : ℝ) ^ 2 + n) * y)
      ≤ Real.exp (-π * (y * (n : ℝ) ^ 2 - y * |(n : ℝ)|)) := by
    rw [Real.exp_le_exp]
    nlinarith [Real.pi_pos, hy, neg_abs_le (n : ℝ),
      mul_nonneg (mul_nonneg Real.pi_pos.le hy.le)
        (by linarith [neg_abs_le (n : ℝ)] : (0 : ℝ) ≤ (n : ℝ) + |(n : ℝ)|)]
  have hpoly : (n : ℝ) ^ 2 + n ≤ |(n : ℝ)| ^ 2 + |(n : ℝ)| := by
    rw [sq_abs]; nlinarith [le_abs_self (n : ℝ)]
  calc π * ((n : ℝ) ^ 2 + n) * Real.exp (-π * ((n : ℝ) ^ 2 + n) * y)
      ≤ π * (|(n : ℝ)| ^ 2 + |(n : ℝ)|) * Real.exp (-π * (y * (n : ℝ) ^ 2 - y * |(n : ℝ)|)) := by gcongr
    _ = π * ((|(n : ℝ)| ^ 2 + |(n : ℝ)|) * Real.exp (-π * (y * (n : ℝ) ^ 2 - y * |(n : ℝ)|))) := by ring

private theorem tsum_polyExpTerm_bound {y : ℝ} (hy1 : 1 ≤ y) :
    (∑' n : ℤ, polyExpTerm y n) ≤ (∑' n : ℤ, polyExpTerm (1/2 : ℝ) n) * Real.exp (-π * y) := by
  rw [← tsum_mul_right]
  refine Summable.tsum_mono (summable_polyExpTerm (by linarith))
    ((summable_polyExpTerm (by norm_num : (0:ℝ) < 1/2)).mul_right _) (fun n => ?_)
  unfold polyExpTerm
  rcases eq_or_lt_of_le (@nn_sq_add n) with h0 | h0
  · rw [← h0]; simp
  · have hge : (2 : ℝ) ≤ (n : ℝ) ^ 2 + n := by
      have hint : (0 : ℤ) < n ^ 2 + n := by
        have : (0 : ℝ) < ((n ^ 2 + n : ℤ) : ℝ) := by push_cast; linarith [h0]
        exact_mod_cast this
      have heven : Even (n ^ 2 + n) := by
        have := Int.even_mul_succ_self n
        rwa [show n * (n + 1) = n ^ 2 + n by ring] at this
      have hz : (2 : ℤ) ≤ n ^ 2 + n := by
        obtain ⟨k, hk⟩ := heven; rw [hk] at hint ⊢; omega
      exact_mod_cast hz
    have hAB : Real.exp (-π * ((n : ℝ) ^ 2 + n) * y)
        ≤ Real.exp (-π * ((n : ℝ) ^ 2 + n) * (1/2 : ℝ) + -π * y) := by
      rw [Real.exp_le_exp]
      nlinarith [Real.pi_pos, hy1, hge,
        mul_nonneg (mul_nonneg Real.pi_pos.le (sub_nonneg.2 hge))
          (by linarith : (0 : ℝ) ≤ y - 1/2)]
    calc π * ((n : ℝ) ^ 2 + n) * Real.exp (-π * ((n : ℝ) ^ 2 + n) * y)
        ≤ π * ((n : ℝ) ^ 2 + n) * Real.exp (-π * ((n : ℝ) ^ 2 + n) * (1/2 : ℝ) + -π * y) :=
          mul_le_mul_of_nonneg_left hAB (by have := @nn_sq_add n; positivity)
      _ = π * ((n : ℝ) ^ 2 + n) * Real.exp (-π * ((n : ℝ) ^ 2 + n) * (1/2 : ℝ)) * Real.exp (-π * y) := by
          rw [Real.exp_add]; ring

open Filter in
/-- **`Θ_deriv → 0`** as `im τ → ∞` (the `n = 0, −1` terms vanish; the rest decay like `e^{−π·im}`). -/
theorem tendsto_jacobiTheta₂DiagDeriv_atImInfty :
    Tendsto jacobiTheta₂DiagDeriv (comap Complex.im atTop) (𝓝 0) := by
  have hbnd : Tendsto (fun τ : ℂ => (∑' n : ℤ, polyExpTerm (1/2 : ℝ) n) * Real.exp (-π * τ.im))
      (comap Complex.im atTop) (𝓝 0) := by
    simpa using tendsto_exp_neg_pi_im.const_mul (∑' n : ℤ, polyExpTerm (1/2 : ℝ) n)
  refine squeeze_zero_norm' ?_ hbnd
  filter_upwards [tendsto_comap.eventually (eventually_ge_atTop (1 : ℝ))] with τ hτ
  have hτ0 : 0 < τ.im := by linarith
  rw [jacobiTheta₂DiagDeriv_tsum hτ0]
  have hzim : ((τ / 2 : ℂ)).im = τ.im / 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.div_ofReal_im]
  have hnorm : ∀ n : ℤ, ‖(π : ℂ) * I * n * (n + 1) * jacobiTheta₂_term n (τ / 2) τ‖
      = polyExpTerm τ.im n := by
    intro n
    rw [polyExpTerm, norm_mul, norm_jacobiTheta₂_term, hzim,
        show (π : ℂ) * I * n * (n + 1) = (((π * ((n : ℝ) ^ 2 + n) : ℝ)) : ℂ) * I by push_cast; ring,
        norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by have := @nn_sq_add n; positivity)]
    congr 1; ring_nf
  have hsummNorm : Summable
      (fun n : ℤ => ‖(π : ℂ) * I * n * (n + 1) * jacobiTheta₂_term n (τ / 2) τ‖) := by
    simp_rw [hnorm]; exact summable_polyExpTerm hτ0
  refine (norm_tsum_le_tsum_norm hsummNorm).trans ?_
  rw [tsum_congr (fun n => hnorm n)]
  exact tsum_polyExpTerm_bound hτ


/-- **`θ₂'/θ₂ = πi/4 + Θ_deriv/Θ`** (`Θ = jacobiTheta₂(τ/2,τ)`), from `hasDerivAt_thetaTwo` and
`θ₂ = e^{πiτ/4}·Θ`. -/
theorem deriv_thetaTwo_div_eq {τ : ℂ} (hτ : 0 < τ.im) :
    deriv thetaTwo τ / thetaTwo τ
      = (π : ℂ) * I / 4 + jacobiTheta₂DiagDeriv τ / jacobiTheta₂ (τ / 2) τ := by
  have hΘ : jacobiTheta₂ (τ / 2) τ ≠ 0 := (thetaTwo_ne_zero_iff τ).mp (thetaTwo_ne_zero_of_im_pos hτ)
  have hexp : Complex.exp ((Real.pi : ℂ) * I * τ / 4) ≠ 0 := Complex.exp_ne_zero _
  rw [(hasDerivAt_thetaTwo hτ).deriv, thetaTwo, jacobiTheta₂DiagDeriv]
  field_simp

open Filter in
/-- **`θ₂'/θ₂ → πi/4`** as `im τ → ∞` (since `Θ_deriv → 0` and `Θ → 2 ≠ 0`). -/
theorem tendsto_deriv_thetaTwo_div_atImInfty :
    Tendsto (fun τ : ℂ => deriv thetaTwo τ / thetaTwo τ) (comap Complex.im atTop)
      (𝓝 ((π : ℂ) * I / 4)) := by
  have hΘdΘ : Tendsto (fun τ : ℂ => jacobiTheta₂DiagDeriv τ / jacobiTheta₂ (τ / 2) τ)
      (comap Complex.im atTop) (𝓝 (0 / 2)) :=
    tendsto_jacobiTheta₂DiagDeriv_atImInfty.div tendsto_jacobiTheta₂_diag_atImInfty (by norm_num)
  have hsum := tendsto_const_nhds (x := (π : ℂ) * I / 4)
    (f := comap Complex.im atTop) |>.add hΘdΘ
  refine (hsum.congr' ?_).mono_right (by norm_num)
  filter_upwards [tendsto_comap.eventually (eventually_gt_atTop (0 : ℝ))] with τ hτ
  exact (deriv_thetaTwo_div_eq hτ).symm

/-- **Closed form of `P`:** `P = (4·θ₂'/θ₂ − 4·θ₃'/θ₃)/θ₄⁴ − πi` (factor `θ₂⁴θ₃⁴` out of `D₆`). -/
theorem thetaWronskianRatio_eq {τ : ℂ} (hτ : 0 < τ.im) :
    thetaWronskianRatio τ
      = (4 * (deriv thetaTwo τ / thetaTwo τ) - 4 * (deriv thetaThree τ / thetaThree τ))
          / thetaFour τ ^ 4 - (π : ℂ) * I := by
  have h2 := thetaTwo_ne_zero_of_im_pos hτ
  have h3 := thetaThree_ne_zero_of_im_pos hτ
  have h4 := thetaFour_ne_zero_of_im_pos hτ
  rw [thetaWronskianRatio, thetaWronskianDefect, deriv_thetaTwo_pow4 hτ, deriv_thetaThree_pow4 hτ]
  field_simp

open Filter in
/-- **`P → 0` at `i∞`.** From `θ₂'/θ₂ → πi/4`, `θ₃'/θ₃ → 0`, `θ₄⁴ → 1`:
`P → (4·πi/4 − 0)/1 − πi = 0`. This is the cusp-vanishing input for `P ≡ 0`. -/
theorem tendsto_thetaWronskianRatio_atImInfty :
    Tendsto thetaWronskianRatio (comap Complex.im atTop) (𝓝 0) := by
  have hb : Tendsto (fun τ : ℂ => deriv thetaThree τ / thetaThree τ)
      (comap Complex.im atTop) (𝓝 (0 / 1)) :=
    tendsto_deriv_thetaThree_atImInfty.div tendsto_thetaThree_atImInfty (by norm_num)
  have hc : Tendsto (fun τ : ℂ => thetaFour τ ^ 4) (comap Complex.im atTop) (𝓝 ((1 : ℂ) ^ 4)) :=
    tendsto_thetaFour_atImInfty.pow 4
  have hlim : Tendsto (fun τ : ℂ =>
      (4 * (deriv thetaTwo τ / thetaTwo τ) - 4 * (deriv thetaThree τ / thetaThree τ))
        / thetaFour τ ^ 4 - (π : ℂ) * I)
      (comap Complex.im atTop)
      (𝓝 ((4 * ((π : ℂ) * I / 4) - 4 * (0 / 1)) / (1 : ℂ) ^ 4 - (π : ℂ) * I)) :=
    (((tendsto_deriv_thetaTwo_div_atImInfty.const_mul (4 : ℂ)).sub
      (hb.const_mul (4 : ℂ))).div hc (by norm_num)).sub tendsto_const_nhds
  rw [show ((4 * ((π : ℂ) * I / 4) - 4 * (0 / 1)) / (1 : ℂ) ^ 4 - (π : ℂ) * I) = 0 by ring] at hlim
  refine hlim.congr' ?_
  filter_upwards [tendsto_comap.eventually (eventually_gt_atTop (0 : ℝ))] with τ hτ
  exact (thetaWronskianRatio_eq hτ).symm

/-! ### `P` is a weight-0 cusp form for `SL(2,ℤ)`, so `P ≡ 0` — `ThetaWronskian23` unconditional.

`P = D₆/(θ₂θ₃θ₄)⁴` is holomorphic on `ℍ`, `SL(2,ℤ)`-invariant (weight 0; `_add_one`/`_S`), and `→ 0`
at `i∞` (`tendsto_thetaWronskianRatio_atImInfty`). Hence `P ∈ S₀(SL(2,ℤ))`, a weight-`0 < 12` cusp-form
space, which is zero-dimensional (`CuspForm.rank_eq_zero_of_weight_lt_twelve`). So `P ≡ 0`, giving
`ThetaWronskian23` (hence `λ' ≠ 0`) unconditionally — the same `F² ∈ S₄ = 0` route that proved the
Jacobi quartic identity, one weight up. -/

section ModularConstruction
open Matrix ModularGroup CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups ModularForm Manifold

/-- `P` viewed as a function `ℍ → ℂ`. -/
noncomputable def thetaWronskianRatioH : ℍ → ℂ := fun z => thetaWronskianRatio (z : ℂ)

/-- `P` is holomorphic at every `τ ∈ ℍ`: `D₆` is (`differentiableOn_thetaWronskianDefect`) and the
denominator `(θ₂θ₃θ₄)⁴` is holomorphic and nonzero. -/
theorem differentiableAt_thetaWronskianRatio {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ thetaWronskianRatio τ := by
  have hUo : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hnum : DifferentiableAt ℂ thetaWronskianDefect τ :=
    differentiableOn_thetaWronskianDefect.differentiableAt (hUo.mem_nhds hτ)
  have hden : DifferentiableAt ℂ (fun t => (thetaTwo t * thetaThree t * thetaFour t) ^ 4) τ :=
    ((((hasDerivAt_thetaTwo hτ).mul (hasDerivAt_thetaThree hτ)).mul
      (hasDerivAt_thetaFour hτ)).pow 4).differentiableAt
  exact hnum.div hden (pow_ne_zero 4 (thetaProduct_ne_zero_of_im_pos hτ))

/-- `P` is holomorphic on `ℍ` (manifold sense). -/
theorem thetaWronskianRatioH_mdiff : MDiff thetaWronskianRatioH := by
  rw [mdifferentiable_iff]
  intro z hz
  have hz' : 0 < z.im := by simpa using hz
  refine (differentiableAt_thetaWronskianRatio hz').differentiableWithinAt.congr
    (fun w hw => ?_) ?_
  · show thetaWronskianRatio ((ofComplex w : ℍ) : ℂ) = thetaWronskianRatio w
    rw [ofComplex_apply_of_im_pos (by simpa using hw)]
  · show thetaWronskianRatio ((ofComplex z : ℍ) : ℂ) = thetaWronskianRatio z
    rw [ofComplex_apply_of_im_pos hz']

/-- `P ∣[0] S = P` (weight-0, `S`-invariance `P(−1/τ)=P(τ)`; the `denom^(0 : ℕ) = 1` factor drops). -/
theorem thetaWronskianRatioH_slash_S :
    thetaWronskianRatioH ∣[(0 : ℤ)] ModularGroup.S = thetaWronskianRatioH := by
  funext z
  have hzim : 0 < (z : ℂ).im := by rw [UpperHalfPlane.coe_im]; exact z.im_pos
  rw [ModularForm.SL_slash_apply, thetaWronskianRatioH, thetaWronskianRatioH]
  have hact : ((ModularGroup.S • z : ℍ) : ℂ) = -1 / (z : ℂ) := by
    rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, neg_div, one_div, inv_neg]
  rw [hact, thetaWronskianRatio_S hzim, neg_zero, zpow_zero, mul_one]

/-- `P ∣[0] T = P` (weight-0, `T`-invariance `P(τ+1)=P(τ)`). -/
theorem thetaWronskianRatioH_slash_T :
    thetaWronskianRatioH ∣[(0 : ℤ)] ModularGroup.T = thetaWronskianRatioH := by
  funext z
  have hzim : 0 < (z : ℂ).im := by rw [UpperHalfPlane.coe_im]; exact z.im_pos
  rw [ModularForm.SL_slash_apply, thetaWronskianRatioH, thetaWronskianRatioH]
  have hact : ((ModularGroup.T • z : ℍ) : ℂ) = (z : ℂ) + 1 := by
    rw [← zpow_one ModularGroup.T, ModularGroup.coe_T_zpow_smul_eq]; push_cast; ring
  rw [hact, thetaWronskianRatio_add_one hzim, neg_zero, zpow_zero, mul_one]

/-- `P ∣[0] γ = P` for every `γ ∈ SL(2,ℤ)` — closure induction over `⟨S,T⟩` (all `=`, no sign, since
`P` is genuinely invariant of weight 0). -/
theorem thetaWronskianRatioH_slash_SL2Z (γ : SL(2, ℤ)) :
    thetaWronskianRatioH ∣[(0 : ℤ)] γ = thetaWronskianRatioH := by
  have hmem : γ ∈ Subgroup.closure ({ModularGroup.S, ModularGroup.T} : Set SL(2, ℤ)) := by
    simp [SpecialLinearGroup.SL2Z_generators]
  induction hmem using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    exacts [thetaWronskianRatioH_slash_S, thetaWronskianRatioH_slash_T]
  | one => exact SlashAction.slash_one 0 thetaWronskianRatioH
  | mul x y _ _ ihx ihy => rw [SlashAction.slash_mul, ihx, ihy]
  | inv x _ ih =>
    have h : thetaWronskianRatioH ∣[(0 : ℤ)] x⁻¹
        = (thetaWronskianRatioH ∣[(0 : ℤ)] x) ∣[(0 : ℤ)] x⁻¹ := by rw [ih]
    rw [h, ← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]

/-- `P → 0` at `i∞` in manifold form. -/
theorem thetaWronskianRatioH_zeroAtImInfty : IsZeroAtImInfty thetaWronskianRatioH :=
  tendsto_thetaWronskianRatio_atImInfty.comp tendsto_coe_atImInfty

/-- **`P` as a weight-0 cusp form for `SL(2,ℤ)`** — holomorphic, `SL(2,ℤ)`-invariant, vanishing at the
cusp. -/
noncomputable def thetaWronskianRatioCusp : CuspForm 𝒮ℒ 0 where
  toFun := thetaWronskianRatioH
  slash_action_eq' A hA := by
    obtain ⟨γ, rfl⟩ := hA
    exact thetaWronskianRatioH_slash_SL2Z γ
  holo' := thetaWronskianRatioH_mdiff
  zero_at_cusps' hc := by
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    rw [thetaWronskianRatioH_slash_SL2Z γ]
    exact thetaWronskianRatioH_zeroAtImInfty

/-- **`P ≡ 0` on `ℍ`.** `P` is a weight-`0` cusp form and `S₀(SL(2,ℤ)) = 0`
(`CuspForm.rank_eq_zero_of_weight_lt_twelve`, `0 < 12`). -/
theorem thetaWronskianRatio_eq_zero {τ : ℂ} (hτ : 0 < τ.im) : thetaWronskianRatio τ = 0 := by
  have h0 : thetaWronskianRatioCusp = 0 :=
    rank_zero_iff_forall_zero.mp
      (CuspForm.rank_eq_zero_of_weight_lt_twelve (by norm_num)) thetaWronskianRatioCusp
  have key : thetaWronskianRatioCusp ⟨τ, hτ⟩ = (0 : CuspForm 𝒮ℒ 0) ⟨τ, hτ⟩ :=
    DFunLike.congr_fun h0 _
  rw [CuspForm.zero_apply] at key
  exact key

/-- **`ThetaWronskian23` is a theorem.** `θ₂'θ₃ − θ₂θ₃' = (πi/4)·θ₂θ₃θ₄⁴` on `ℍ`, via `P ≡ 0`. This
discharges the named hypothesis of `ModularLambdaLocalBiholo`, making `λ' ≠ 0` unconditional. -/
theorem thetaWronskian23 : ThetaWronskian23 :=
  thetaWronskian23_of_ratio_zero (fun _ hτ => thetaWronskianRatio_eq_zero hτ)

end ModularConstruction

/-! ### `λ` is a local biholomorphism, unconditionally (`ThetaWronskian23` discharged). -/

/-- **`λ' ≠ 0` on `ℍ`, unconditionally** — the local-biholomorphism datum for `IsCoveringMap λ`. -/
theorem modularLambda_deriv_ne_zero' {τ : ℂ} (hτ : 0 < τ.im) : deriv modularLambda τ ≠ 0 :=
  modularLambda_deriv_ne_zero thetaWronskian23 hτ

/-- **`λ' = πi·θ₂⁴θ₄⁴/θ₃⁴`, unconditionally.** -/
theorem deriv_modularLambda_eq' {τ : ℂ} (hτ : 0 < τ.im) :
    deriv modularLambda τ = (π : ℂ) * I * thetaTwo τ ^ 4 * thetaFour τ ^ 4 / thetaThree τ ^ 4 :=
  deriv_modularLambda_eq thetaWronskian23 hτ

/-- **`λ' = πi·θ₃⁴·λ·(1−λ)`, unconditionally.** -/
theorem deriv_modularLambda_eq_lambda' {τ : ℂ} (hτ : 0 < τ.im) :
    deriv modularLambda τ
      = (π : ℂ) * I * thetaThree τ ^ 4 * modularLambda τ * (1 - modularLambda τ) :=
  deriv_modularLambda_eq_lambda thetaWronskian23 hτ
end Bottcher
