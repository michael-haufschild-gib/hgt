import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The hyperbolic tangent lies below the identity

`tanh x ≤ x` for `x ≥ 0`, equivalently `x ≤ artanh x` on `[0,1)`, and the resulting quadratic
lower bound `d² ≤ d · artanh d` on `(-1,1)`.  The proof is the monotonicity of
`x ↦ x·cosh x − sinh x`, whose derivative is `x·sinh x`.
-/

namespace GaloisForLFunctions.HTGeometry

open Real Set

theorem hasDerivAt_mulCoshSubSinh (x : ℝ) :
    HasDerivAt (fun t : ℝ => t * Real.cosh t - Real.sinh t) (x * Real.sinh x) x := by
  have h1 : HasDerivAt (fun t : ℝ => t * Real.cosh t)
      (1 * Real.cosh x + x * Real.sinh x) x :=
    (hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)
  have h2 : HasDerivAt Real.sinh (Real.cosh x) x := Real.hasDerivAt_sinh x
  have h3 := h1.sub h2
  rw [show (1 * Real.cosh x + x * Real.sinh x) - Real.cosh x = x * Real.sinh x by ring] at h3
  exact h3

theorem monotoneOn_mulCoshSubSinh :
    MonotoneOn (fun t : ℝ => t * Real.cosh t - Real.sinh t) (Ici 0) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
  · exact (continuous_id.mul Real.continuous_cosh).sub Real.continuous_sinh |>.continuousOn
  · exact fun x _ => (hasDerivAt_mulCoshSubSinh x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [(hasDerivAt_mulCoshSubSinh x).deriv]
    rw [interior_Ici] at hx
    exact mul_nonneg (le_of_lt hx) (Real.sinh_nonneg_iff.mpr (le_of_lt hx))

/-- `sinh x ≤ x · cosh x` for nonnegative `x`. -/
theorem sinh_le_mul_cosh {x : ℝ} (hx : 0 ≤ x) : Real.sinh x ≤ x * Real.cosh x := by
  have h := monotoneOn_mulCoshSubSinh (by simp : (0:ℝ) ∈ Ici (0:ℝ)) (by simpa using hx) hx
  simp only [zero_mul, Real.sinh_zero, sub_zero] at h
  linarith

/-- **The hyperbolic tangent lies below the identity.** -/
theorem tanh_le_self {x : ℝ} (hx : 0 ≤ x) : Real.tanh x ≤ x := by
  have hc : 0 < Real.cosh x := Real.cosh_pos x
  rw [Real.tanh_eq_sinh_div_cosh, div_le_iff₀ hc]
  exact sinh_le_mul_cosh hx

/-- **The inverse hyperbolic tangent lies above the identity.** -/
theorem self_le_artanh {x : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) : x ≤ Real.artanh x := by
  have hmem : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, hx1⟩
  have h := tanh_le_self (Real.artanh_nonneg hx)
  rwa [Real.tanh_artanh hmem] at h

theorem artanh_neg_self {x : ℝ} (hx : |x| < 1) : Real.artanh (-x) = -Real.artanh x := by
  rw [abs_lt] at hx
  rw [Real.artanh_eq_half_log ⟨by linarith, by linarith⟩,
    Real.artanh_eq_half_log ⟨by linarith, by linarith⟩,
    show (1 + -x) / (1 - -x) = ((1 + x) / (1 - x))⁻¹ by
      rw [inv_div]
      ring_nf,
    Real.log_inv]
  ring

/-- `(LPC.25)`, pointwise: the contrast rapidity dominates the contrast quadratically. -/
theorem sq_le_mul_artanh {d : ℝ} (hd : |d| < 1) : d ^ 2 ≤ d * Real.artanh d := by
  rw [abs_lt] at hd
  rcases le_total 0 d with h | h
  · nlinarith [self_le_artanh h hd.2]
  · have hneg : (0:ℝ) ≤ -d := by linarith
    have hlt : -d < 1 := by linarith [hd.1]
    have h1 := self_le_artanh hneg hlt
    rw [artanh_neg_self (by rw [abs_lt]; constructor <;> linarith)] at h1
    nlinarith [h1]

end GaloisForLFunctions.HTGeometry
