import GaloisForLFunctions.HTGeometry.HyperbolicLevyKhintchine
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-! # Four sine harmonics approximate an eigenangle difference -/

open Real
namespace GaloisForLFunctions.HTGeometry.CircuitSynthesis.PauliAverages.Interpolation
noncomputable section

/-- Odd trigonometric polynomial matching the identity through degree seven. -/
def sinePolynomial (x : ℝ) :=
  8/5*sin x-2/5*sin (2*x)+8/105*sin (3*x)-1/140*sin (4*x)

private theorem error_deriv (x : ℝ) :
    HasDerivAt (fun y => y-sinePolynomial y) (8/35*(1-cos x)^4) x := by
  have hs (c : ℝ) : HasDerivAt (fun y => sin (c*y)) (cos (c*x)*c) x := by
    have hlin : HasDerivAt (fun y : ℝ => c*y) c x := hasDerivAt_const_mul c
    exact hlin.sin
  have h := (hasDerivAt_id x).sub (((((Real.hasDerivAt_sin x).const_mul (8/5)).sub
    ((hs 2).const_mul (2/5))).add ((hs 3).const_mul (8/105))).sub ((hs 4).const_mul (1/140)))
  refine h.congr_deriv ?_
  rw [show (4:ℝ)*x=2*(2*x) by ring,Real.cos_two_mul (2*x),Real.cos_three_mul,Real.cos_two_mul]
  ring

/-- The angular error is at most $|x|^9/630$. The exact derivative
of the error is a nonnegative fourth power of the cosine deficit. -/
theorem sine_error (x : ℝ) : |x-sinePolynomial x|≤|x|^9/630 := by
  let g (y : ℝ) := y-sinePolynomial y
  let h (y : ℝ) := y^9/630-g y
  have hg (y) : HasDerivAt g (8/35*(1-cos y)^4) y := error_deriv y
  have hh (y) : HasDerivAt h (9*y^8/630-8/35*(1-cos y)^4) y := by
    exact (((hasDerivAt_pow 9 y).div_const 630).sub (hg y)).congr_deriv (by norm_num)
  have hgm : Monotone g := monotone_of_deriv_nonneg (fun y => (hg y).differentiableAt)
    (fun y => by rw [(hg y).deriv]; positivity)
  have hhm : Monotone h := monotone_of_deriv_nonneg (fun y => (hh y).differentiableAt) (fun y => by
    rw [(hh y).deriv]
    have hb := pow_le_pow_left₀ (sub_nonneg.mpr (Real.cos_le_one y))
      (_root_.HTGeometry.one_sub_cos_le_sq_div_two y) 4
    nlinarith only [hb])
  have h₀ : g 0=0 := by simp [g,sinePolynomial]
  have hh₀ : h 0=0 := by simp [h,h₀]
  change |g x|≤_
  rcases le_total 0 x with hx|hx
  · have h₁ := hgm hx
    have h₂ := hhm hx
    rw [h₀] at h₁
    rw [hh₀] at h₂
    rw [abs_of_nonneg h₁,abs_of_nonneg hx]
    exact sub_nonneg.mp h₂
  · have h₁ := hgm hx
    have h₂ := hhm hx
    rw [h₀] at h₁
    rw [hh₀] at h₂
    rw [abs_of_nonpos h₁,abs_of_nonpos hx]
    change x^9/630-g x ≤ 0 at h₂
    nlinarith only [h₂]

#print axioms sine_error
end
end GaloisForLFunctions.HTGeometry.CircuitSynthesis.PauliAverages.Interpolation
