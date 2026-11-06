import GaloisForLFunctions.ArithmeticInnerFunctionTheory.TheCrowdOfTheInnerField

/-!
# Crowds are exponentially rare

The budget of a box controls the exponential of its crowd. For a centre `w`, a box of ratio `θ` and an entire mollifier `M`,

`exp((4θ/5) Σ_box m_ρ) · |E(w)M(w)/w|² ≤ ∫ |ζM|² P_w` (`exp_mul_sum_box_le`).

The exponential comes from the inner field itself: the crowd costs `2θ/5` per zero in the exponent of `I`, and `e^{2I}` is what a second moment
pays. Summing over centres (`card_mul_exp_le`), centres carrying a crowd of size `≥ k` and a mollified value at least `δ` satisfy

`#{centres} · δ² · exp(4θk/5) ≤ Σ_j ∫ |ζM|² P_{w_j}`.

So crowds are exponentially rare in `k`, and this is the Carleson embedding at the critical scale with arithmetic coefficients: all arithmetic is in the
mollifier `M` and in the second moment on the line.
-/

open Complex Finset

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

open _root_.RHTower

noncomputable section

/-- **The crowd of a box is paid exponentially by the second moment.** -/
theorem exp_mul_sum_box_le {M : ℂ → ℂ} (hM : Differentiable ℂ M) {C : ℝ}
    (hgrow : ∀ z : ℂ, 1 / 2 ≤ z.re → ‖M z‖ ≤ C * (‖z‖ + 2) ^ 2) {w : ℂ} (hw : 1 / 2 < w.re)
    (h0 : zetaEntire w ≠ 0) (hMw : M w ≠ 0)
    (hi : MeasureTheory.Integrable fun τ : ℝ => ‖riemannZeta (1 / 2 + τ * I)‖ ^ 2 * ‖M (1 / 2 + τ * I)‖ ^ 2 *
      halfPlanePoissonKernel w τ) {θ : ℝ} (hθ : 0 < θ)
    (Z : Finset ZetaRightZero) (hZ : ∀ ρ ∈ Z, InBox w θ ρ) :
    Real.exp ((4 * θ / 5) * ∑ ρ ∈ Z, zeroMult ρ) * (‖zetaEntire w‖ / ‖w‖ * ‖M w‖) ^ 2 ≤
      ∫ τ : ℝ, ‖riemannZeta (1 / 2 + τ * I)‖ ^ 2 * ‖M (1 / 2 + τ * I)‖ ^ 2 *
        halfPlanePoissonKernel w τ := by
  refine le_trans ?_ (exp_two_innerField_mul_le hM hgrow hw h0 hMw hi)
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (sq_nonneg _)
  have h := mult_sum_box_le hw h0 hθ Z hZ
  linarith

/-- **Large deviations of crowds.** Centres carrying a crowd of size `≥ k` with mollified value `≥ δ` are at most
`e^{−4θk/5}δ^{−2}` times the second moment. -/
theorem card_mul_exp_le {ι : Type*} (J : Finset ι) {M : ℂ → ℂ} (hM : Differentiable ℂ M) {C : ℝ}
    (hgrow : ∀ z : ℂ, 1 / 2 ≤ z.re → ‖M z‖ ≤ C * (‖z‖ + 2) ^ 2) {w : ι → ℂ} (hw : ∀ j ∈ J, 1 / 2 < (w j).re)
    (h0 : ∀ j ∈ J, zetaEntire (w j) ≠ 0) (hMw : ∀ j ∈ J, M (w j) ≠ 0)
    (hi : ∀ j ∈ J, MeasureTheory.Integrable fun τ : ℝ =>
      ‖riemannZeta (1 / 2 + τ * I)‖ ^ 2 * ‖M (1 / 2 + τ * I)‖ ^ 2 * halfPlanePoissonKernel (w j) τ)
    {θ k δ : ℝ} (hθ : 0 < θ) (hδ : 0 ≤ δ) {Z : ι → Finset ZetaRightZero}
    (hZ : ∀ j ∈ J, ∀ ρ ∈ Z j, InBox (w j) θ ρ) (hk : ∀ j ∈ J, k ≤ ∑ ρ ∈ Z j, zeroMult ρ)
    (hlow : ∀ j ∈ J, δ ≤ ‖zetaEntire (w j)‖ / ‖w j‖ * ‖M (w j)‖) :
    (J.card : ℝ) * (δ ^ 2 * Real.exp ((4 * θ / 5) * k)) ≤
      ∑ j ∈ J, ∫ τ : ℝ, ‖riemannZeta (1 / 2 + τ * I)‖ ^ 2 * ‖M (1 / 2 + τ * I)‖ ^ 2 *
        halfPlanePoissonKernel (w j) τ := by
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun j hj => le_trans ?_
    (exp_mul_sum_box_le hM hgrow (hw j hj) (h0 j hj) (hMw j hj) (hi j hj) hθ (Z j) (hZ j hj))
  have h1 : Real.exp ((4 * θ / 5) * k) ≤ Real.exp ((4 * θ / 5) * ∑ ρ ∈ Z j, zeroMult ρ) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hk j hj) (by positivity))
  have h2 : δ ^ 2 ≤ (‖zetaEntire (w j)‖ / ‖w j‖ * ‖M (w j)‖) ^ 2 :=
    pow_le_pow_left₀ hδ (hlow j hj) 2
  rw [mul_comm (Real.exp _)]
  exact mul_le_mul h2 h1 (Real.exp_pos _).le (sq_nonneg _)

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
