import GaloisForLFunctions.RHTower.DeningerMobiusPreimage

/-!
# The derivative of the pullback on the positive ray

Differentiating `H_h(x) = h(log x)` on the ray gives `H_h'(x) = h'(log x)/x`, so the *weighted*
derivative `x H_h'(x)` is just `h'(log x)` — the factor `1/x` from the chain rule cancels the
weight exactly.  Consequently `x H_h'(x)` inherits the same two-sided power decay as the pullback
itself, with no loss.

This is what makes the first weighted moment `∫_0^∞ u |H_h'(u)| du` finite, which is the analytic
half of the `L¹` estimate for the canonical Möbius preimage.

* `deningerLogPullDeriv` : the derivative `h'(log x)/x`.
* `deningerLogPull_hasDerivAt` : it is the derivative of the pullback.
* `deningerLogPullDeriv_weighted_norm_le` : **the weighted derivative decays two-sidedly.**
-/

namespace RHTower

open SchwartzMap

noncomputable section

/-- The derivative of the pullback on the positive ray. -/
def deningerLogPullDeriv (h : 𝓢(ℝ, ℂ)) (x : ℝ) : ℂ := deriv (h : ℝ → ℂ) (Real.log x) * (x : ℝ)⁻¹

/-- **The pullback is differentiable on the positive ray**, with the chain-rule derivative. -/
theorem deningerLogPull_hasDerivAt (h : 𝓢(ℝ, ℂ)) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (deningerLogPull h) (deningerLogPullDeriv h x) x := by
  have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx.ne'
  have hh : HasDerivAt (h : ℝ → ℂ) (deriv (h : ℝ → ℂ) (Real.log x)) (Real.log x) :=
    (h.differentiable (Real.log x)).hasDerivAt
  have hcomp : HasDerivAt (fun y : ℝ => (h : ℝ → ℂ) (Real.log y))
      ((x⁻¹ : ℝ) • deriv (h : ℝ → ℂ) (Real.log x)) x := hh.scomp x hlog
  have heq : (x⁻¹ : ℝ) • deriv (h : ℝ → ℂ) (Real.log x) = deningerLogPullDeriv h x := by
    rw [deningerLogPullDeriv, Complex.real_smul]
    push_cast
    ring
  rw [← heq]
  exact hcomp

/-- The `n`-th derivative bound of the source, read off the exponential weight. -/
theorem deningerExpSchwartz_deriv_norm_le {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz)
    (A : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      Real.exp (A * |t|) * ‖deriv (h : ℝ → ℂ) t‖ ≤ C := by
  obtain ⟨C, hC⟩ := hh A 1
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  have hle : ‖deriv (h : ℝ → ℂ) t‖ ≤ ‖iteratedFDeriv ℝ 1 (h : ℝ → ℂ) t‖ := by
    rw [norm_iteratedFDeriv_one]
    have hd : deriv (h : ℝ → ℂ) t = (fderiv ℝ (h : ℝ → ℂ) t) 1 := (fderiv_apply_one_eq_deriv).symm
    rw [hd]
    calc ‖(fderiv ℝ (h : ℝ → ℂ) t) 1‖ ≤ ‖fderiv ℝ (h : ℝ → ℂ) t‖ * ‖(1 : ℝ)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ (h : ℝ → ℂ) t‖ := by rw [norm_one, mul_one]
  have hstep : Real.exp (A * |t|) * ‖deriv (h : ℝ → ℂ) t‖
      ≤ Real.exp (A * |t|) * ‖iteratedFDeriv ℝ 1 (h : ℝ → ℂ) t‖ :=
    mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le
  exact le_trans hstep (le_trans (hC t) (le_max_left _ _))

/-- **The weighted derivative decays two-sidedly.**  Multiplying by `x` cancels the chain-rule
factor exactly, so `x H_h'(x)` obeys the same bound as the pullback. -/
theorem deningerLogPullDeriv_weighted_norm_le {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 0 < y →
      y * ‖deningerLogPullDeriv h y‖ ≤ C * y ^ (2 : ℕ) ∧
      y * ‖deningerLogPullDeriv h y‖ ≤ C / y ^ (2 : ℕ) := by
  obtain ⟨C, hCnn, hC⟩ := deningerExpSchwartz_deriv_norm_le hh 2
  refine ⟨C, hCnn, fun y hy => ?_⟩
  have hcancel : y * ‖deningerLogPullDeriv h y‖ = ‖deriv (h : ℝ → ℂ) (Real.log y)‖ := by
    rw [deningerLogPullDeriv, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv,
      abs_of_pos hy]
    field_simp
  have hbase : ‖deriv (h : ℝ → ℂ) (Real.log y)‖
      ≤ C * Real.exp (-(2 * |Real.log y|)) := by
    have hval := hC (Real.log y)
    have hepos : (0 : ℝ) < Real.exp (2 * |Real.log y|) := Real.exp_pos _
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ hepos]
    calc ‖deriv (h : ℝ → ℂ) (Real.log y)‖ * Real.exp (2 * |Real.log y|)
        = Real.exp (2 * |Real.log y|) * ‖deriv (h : ℝ → ℂ) (Real.log y)‖ := by ring
      _ ≤ C := hval
  have hlog : Real.exp (Real.log y) = y := Real.exp_log hy
  have hup : Real.exp (-(2 * |Real.log y|)) ≤ y ^ (2 : ℕ) := by
    have hle : -(2 * |Real.log y|) ≤ 2 * Real.log y := by
      have := neg_abs_le (Real.log y)
      linarith [abs_nonneg (Real.log y)]
    have hexp := Real.exp_le_exp.mpr hle
    rwa [show (2 : ℝ) * Real.log y = Real.log y + Real.log y by ring, Real.exp_add, hlog,
      ← pow_two] at hexp
  have hdown : Real.exp (-(2 * |Real.log y|)) ≤ 1 / y ^ (2 : ℕ) := by
    have hle : -(2 * |Real.log y|) ≤ -(2 * Real.log y) := by
      have := le_abs_self (Real.log y)
      linarith
    have hexp := Real.exp_le_exp.mpr hle
    have hval : Real.exp (-(2 * Real.log y)) = 1 / y ^ (2 : ℕ) := by
      rw [Real.exp_neg, show (2 : ℝ) * Real.log y = Real.log y + Real.log y by ring,
        Real.exp_add, hlog, ← pow_two, one_div]
    rwa [hval] at hexp
  rw [hcancel]
  refine ⟨le_trans hbase ?_, le_trans hbase ?_⟩
  · exact mul_le_mul_of_nonneg_left hup hCnn
  · have := mul_le_mul_of_nonneg_left hdown hCnn
    rwa [mul_one_div] at this

end

end RHTower
