import Mathlib

/-!
# Holomorphic square roots on a disk

A holomorphic function that is nonvanishing on a disk has a holomorphic square root there
(`exists_sqrt_of_ne_zero`).  The disk is simply connected, so the logarithmic derivative `f'/f`
has a holomorphic primitive `g` (Morera's theorem for a disk, `DifferentiableOn.isExactOn_ball`);
then `f·e^{-g}` has vanishing derivative, hence is a constant `C ≠ 0`, so `f = C·e^{g}` and
`s := e^{(log C + g)/2}` is a holomorphic square root.

This is the analytic input of the Riesz factorization `H¹ = H² · H²`: a zero-free `H¹` function has
a holomorphic square root in `H²`, which underlies the F.&M. Riesz theorem.
-/

open Complex Metric Set

namespace GaloisForLFunctions.HTGeometry

/-- **Holomorphic square root on a disk.**  A function holomorphic and nonvanishing on the ball
`ball c r` has a holomorphic square root there. -/
theorem exists_sqrt_of_ne_zero {c : ℂ} {r : ℝ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball c r)) (hne : ∀ z ∈ ball c r, f z ≠ 0) :
    ∃ s : ℂ → ℂ, DifferentiableOn ℂ s (ball c r) ∧ ∀ z ∈ ball c r, s z ^ 2 = f z := by
  by_cases hr : 0 < r
  swap
  · have hr' : r ≤ 0 := not_lt.mp hr
    exact ⟨0, differentiableOn_const 0, fun z hz => absurd hz (by
      simp [Metric.ball_eq_empty.mpr hr'])⟩
  have hc : c ∈ ball c r := mem_ball_self hr
  have hfa : AnalyticOnNhd ℂ f (ball c r) := hf.analyticOnNhd isOpen_ball
  have hderiv_a : AnalyticOnNhd ℂ (deriv f) (ball c r) := hfa.deriv
  have hld : DifferentiableOn ℂ (fun z => deriv f z / f z) (ball c r) :=
    (hderiv_a.differentiableOn).div hf hne
  obtain ⟨g, hg⟩ := hld.isExactOn_ball
  have hg_diff : DifferentiableOn ℂ g (ball c r) :=
    fun z hz => (hg z hz).differentiableAt.differentiableWithinAt
  have hderiv_f : ∀ z ∈ ball c r, HasDerivAt f (deriv f z) z :=
    fun z hz => (hfa z hz).differentiableAt.hasDerivAt
  set h : ℂ → ℂ := fun z => f z * Complex.exp (-g z) with hh
  have hh0 : ∀ z ∈ ball c r, HasDerivAt h 0 z := by
    intro z hz
    have hdf := hderiv_f z hz
    have hexp : HasDerivAt (fun w => Complex.exp (-g w))
        (Complex.exp (-g z) * (-(deriv f z / f z))) z := ((hg z hz).neg).cexp
    have hzero : (0 : ℂ) = deriv f z * Complex.exp (-g z)
        + f z * (Complex.exp (-g z) * (-(deriv f z / f z))) := by
      field_simp [hne z hz]; ring
    rw [hh, hzero]
    exact hdf.mul hexp
  have hconst : ∀ z ∈ ball c r, h z = h c := by
    intro z hz
    refine Convex.is_const_of_fderivWithin_eq_zero (convex_ball c r)
      (fun w hw => (hh0 w hw).differentiableAt.differentiableWithinAt) (fun w hw => ?_) hz hc
    rw [fderivWithin_eq_fderiv (isOpen_ball.uniqueDiffWithinAt hw) (hh0 w hw).differentiableAt,
      (hh0 w hw).hasFDerivAt.fderiv]
    simp
  set C : ℂ := f c * Complex.exp (-g c) with hC
  have hCne : C ≠ 0 := mul_ne_zero (hne c hc) (Complex.exp_ne_zero _)
  refine ⟨fun z => Complex.exp ((Complex.log C + g z) / 2), ?_, ?_⟩
  · exact fun z hz => (((differentiableWithinAt_const _).add
      (hg_diff z hz)).div_const 2).cexp
  · intro z hz
    have hfz : f z = C * Complex.exp (g z) := by
      have hc2 := hconst z hz
      simp only [hh] at hc2
      have key : f z * Complex.exp (-g z) * Complex.exp (g z)
          = f c * Complex.exp (-g c) * Complex.exp (g z) := by rw [hc2]
      rw [mul_assoc (f z), ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one] at key
      rw [hC]; exact key
    rw [← Complex.exp_nat_mul, show ((2 : ℕ) : ℂ) * ((Complex.log C + g z) / 2)
        = Complex.log C + g z by push_cast; ring,
      Complex.exp_add, Complex.exp_log hCne, hfz]

end GaloisForLFunctions.HTGeometry
