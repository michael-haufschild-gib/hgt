import Mathlib

/-!
# Uniqueness for the exponential differential equation

A differentiable complex-valued function on the line satisfying `f' = c · f` and normalized at
the origin is the exponential `x ↦ exp (c x)`.  mathlib carries Gronwall estimates and the
Picard--Lindelöf existence-uniqueness theorem, but no directly usable statement of this form;
the proof here avoids both by differentiating `f(x) · exp(-c x)`, which has vanishing derivative
and is therefore constant.

If in addition the function is unimodular, the exponent is purely imaginary.  This is the step
that converts a unimodular one-parameter character into a real generator eigenvalue.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

/-- The derivative of `x ↦ exp (c x)` along the real line. -/
theorem hasDerivAt_cexp_const_mul (c : ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (c * (y : ℂ))) (Complex.exp (c * (x : ℂ)) * c) x := by
  have h1 : HasDerivAt (fun y : ℝ => c * (y : ℂ)) c x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul c
  exact h1.cexp

/-- **Uniqueness for `f' = c f`.**  A solution normalized at the origin is the exponential. -/
theorem eq_cexp_of_hasDerivAt {f : ℝ → ℂ} {c : ℂ}
    (hf : ∀ x : ℝ, HasDerivAt f (c * f x) x) (h0 : f 0 = 1) (x : ℝ) :
    f x = Complex.exp (c * (x : ℂ)) := by
  set g : ℝ → ℂ := fun y => f y * Complex.exp (-(c * (y : ℂ))) with hg
  have hgderiv : ∀ y : ℝ, HasDerivAt g 0 y := by
    intro y
    have h2 : HasDerivAt (fun z : ℝ => Complex.exp (-(c * (z : ℂ))))
        (Complex.exp (-(c * (y : ℂ))) * (-c)) y := by
      have h1 : HasDerivAt (fun z : ℝ => (-c) * (z : ℂ)) (-c) y := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := y)).const_mul (-c)
      have := h1.cexp
      simpa [neg_mul] using this
    have h3 := (hf y).mul h2
    rw [show c * f y * Complex.exp (-(c * (y : ℂ)))
        + f y * (Complex.exp (-(c * (y : ℂ))) * (-c)) = 0 from by ring] at h3
    exact h3
  have hdiff : Differentiable ℝ g := fun y => (hgderiv y).differentiableAt
  have hconst : g x = g 0 :=
    is_const_of_deriv_eq_zero hdiff (fun y => (hgderiv y).deriv) x 0
  have hg0 : g 0 = 1 := by
    simp [hg, h0]
  have hgx : f x * Complex.exp (-(c * (x : ℂ))) = 1 := by
    have := hconst.trans hg0
    simpa [hg] using this
  have hmul : Complex.exp (-(c * (x : ℂ))) * Complex.exp (c * (x : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    simp
  calc f x = f x * (Complex.exp (-(c * (x : ℂ))) * Complex.exp (c * (x : ℂ))) := by
        rw [hmul, mul_one]
    _ = f x * Complex.exp (-(c * (x : ℂ))) * Complex.exp (c * (x : ℂ)) := by ring
    _ = Complex.exp (c * (x : ℂ)) := by rw [hgx, one_mul]

/-- **A unimodular exponential has a purely imaginary exponent.**  This is the real generator
eigenvalue of a unimodular one-parameter character. -/
theorem re_eq_zero_of_norm_cexp_eq_one {c : ℂ} (h : ∀ x : ℝ, ‖Complex.exp (c * (x : ℂ))‖ = 1) :
    c.re = 0 := by
  have h1 := h 1
  rw [Complex.norm_exp] at h1
  have h2 : (c * ((1 : ℝ) : ℂ)).re = 0 := by
    have := Real.exp_eq_one_iff (x := (c * ((1 : ℝ) : ℂ)).re)
    exact this.mp h1
  simpa using h2

/-! ## Characters -/

/-- A multiplicative function differentiable at the origin is differentiable everywhere, with
derivative `c · f`.  The group law turns one difference quotient into all of them. -/
theorem hasDerivAt_of_multiplicative {f : ℝ → ℂ} {c : ℂ}
    (hmul : ∀ s t : ℝ, f (s + t) = f s * f t) (h0 : HasDerivAt f c 0) (s : ℝ) :
    HasDerivAt f (c * f s) s := by
  have hshift : HasDerivAt (fun h : ℝ => f (s + h)) (f s * c) (-s + s) := by
    have hfun : (fun h : ℝ => f (s + h)) = fun h : ℝ => f s * f h := funext fun h => hmul s h
    rw [hfun]
    simpa using h0.const_mul (f s)
  have hcomp := hshift.comp_const_add (-s) s
  have hEq : f =ᶠ[nhds s] fun x : ℝ => f (s + (-s + x)) :=
    Filter.Eventually.of_forall fun x => by congr 1; ring
  have hfinal := hcomp.congr_of_eventuallyEq hEq
  simpa [mul_comm] using hfinal

/-- **A character differentiable at the origin is an exponential.** -/
theorem eq_cexp_of_multiplicative {f : ℝ → ℂ} {c : ℂ}
    (hmul : ∀ s t : ℝ, f (s + t) = f s * f t) (hone : f 0 = 1) (h0 : HasDerivAt f c 0) (x : ℝ) :
    f x = Complex.exp (c * (x : ℂ)) :=
  eq_cexp_of_hasDerivAt (fun s => hasDerivAt_of_multiplicative hmul h0 s) hone x

/-- **A unimodular character has a real generator.**  A multiplicative unimodular function
differentiable at the origin is `x ↦ exp (i λ x)` for a real `λ`, the generator eigenvalue. -/
theorem exists_real_generator_of_unimodular_character {f : ℝ → ℂ} {c : ℂ}
    (hmul : ∀ s t : ℝ, f (s + t) = f s * f t) (hone : f 0 = 1) (h0 : HasDerivAt f c 0)
    (hnorm : ∀ x : ℝ, ‖f x‖ = 1) :
    ∃ lam : ℝ, ∀ x : ℝ, f x = Complex.exp (Complex.I * ((lam : ℂ) * (x : ℂ))) := by
  have hexp : ∀ x : ℝ, f x = Complex.exp (c * (x : ℂ)) :=
    fun x => eq_cexp_of_multiplicative hmul hone h0 x
  have hnormexp : ∀ x : ℝ, ‖Complex.exp (c * (x : ℂ))‖ = 1 := by
    intro x
    rw [← hexp x]
    exact hnorm x
  have hre : c.re = 0 := re_eq_zero_of_norm_cexp_eq_one hnormexp
  set lam : ℝ := c.im with hlam
  have hc : c = Complex.I * (lam : ℂ) := by
    apply Complex.ext <;> simp [hre, hlam]
  refine ⟨lam, fun x => ?_⟩
  rw [hexp x, hc]
  congr 1
  ring

end GaloisForLFunctions.HTGeometry
