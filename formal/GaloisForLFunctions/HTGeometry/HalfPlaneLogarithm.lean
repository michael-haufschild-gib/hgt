import GaloisForLFunctions.HTGeometry.RightHalfPlanePrimitive
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# A normalized logarithm from a holomorphic scalar differential equation

A solution of f' = Phi * f equal to one at a basepoint is the exponential of
the primitive of Phi normalized to zero there.
-/

open Complex Set

namespace GaloisForLFunctions.HTGeometry

/-- Integrate a scalar holomorphic differential equation on any right half-plane. -/
theorem exists_halfPlane_exp_primitive {a : ℝ} {Φ f : ℂ → ℂ}
    (hΦ : DifferentiableOn ℂ Φ {z : ℂ | a < z.re})
    (hf : ∀ z : ℂ, a < z.re → HasDerivAt f (Φ z * f z) z)
    {b : ℂ} (hb : a < b.re) (hfb : f b = 1) :
    ∃ P : ℂ → ℂ, P b = 0 ∧
      (∀ z : ℂ, a < z.re → HasDerivAt P (Φ z) z) ∧
      ∀ z : ℂ, a < z.re → Complex.exp (P z) = f z := by
  obtain ⟨P, hPb, hP⟩ := (isExactOn_rightHalfPlane hΦ).with_val_at b 0
  let U : Set ℂ := {z : ℂ | a < z.re}
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  let H : ℂ → ℂ := fun z => f z * Complex.exp (-P z)
  have hHd : ∀ z ∈ U, HasDerivAt H 0 z := by
    intro z hz
    exact ((hf z hz).mul (hP z hz).neg.cexp).congr_deriv (by ring)
  have hHdiff : DifferentiableOn ℂ H U :=
    fun z hz => (hHd z hz).differentiableAt.differentiableWithinAt
  have hH0 : EqOn (deriv H) 0 U := fun z hz => (hHd z hz).deriv
  refine ⟨P, hPb, hP, fun z hz => ?_⟩
  have hc := hUo.is_const_of_deriv_eq_zero (convex_halfSpace_re_gt a).isPreconnected
    hHdiff hH0 hz hb
  have hc1 : f z * Complex.exp (-P z) = 1 := by
    simpa [H, hfb, hPb] using hc
  calc
    Complex.exp (P z) = (f z * Complex.exp (-P z)) * Complex.exp (P z) := by
      rw [hc1, one_mul]
    _ = f z := by rw [mul_assoc, ← Complex.exp_add]; simp

end GaloisForLFunctions.HTGeometry
