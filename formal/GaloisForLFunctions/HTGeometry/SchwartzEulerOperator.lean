import GaloisForLFunctions.HTGeometry.HermiteOrthogonality

/-!
# The Euler operator on the Schwartz space

The Euler operator `θf(x) = x f'(x)` is the generator of the multiplicative flow: it is the
derivative along the logarithmic coordinate, `d/dt f(a e^t) = (θf)(a e^t)`.  It preserves the two
conditions cutting out Meyer's space — it kills the value at the origin outright, and the Fourier
rules turn it into `𝓕(θf) = −𝓕f − θ𝓕f`, whose value at the origin is `−𝓕f(0)` — and it preserves
parity.

So the constraints of Meyer's space propagate to every multiplicative derivative of a Poisson sum,
which is what makes the sum decay at both ends in every derivative.

* `eulerSCLM` : the Euler operator, as a continuous linear map.
* `hasDerivAt_comp_exp` : **it is the derivative along the multiplicative flow.**
* `eulerSCLM_even` : it preserves parity.
* `fourierSCLM_eulerSCLM` : **`𝓕(θf) = −𝓕f − θ𝓕f`**, hence `𝓕(θf)(0) = −𝓕f(0)`.
-/

open scoped Real SchwartzMap FourierTransform
open Complex

noncomputable section

namespace GaloisForLFunctions

/-- **The Euler operator** `θ f(x) = x f'(x)`, the generator of the multiplicative flow. -/
def eulerSCLM : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) := mulXCLM.comp derivSCLM

@[simp] theorem eulerSCLM_apply (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    eulerSCLM f x = (x : ℂ) * deriv (f : ℝ → ℂ) x := by
  show mulXCLM (derivSCLM f) x = _
  rw [mulXCLM_apply, derivSCLM_apply]

theorem eulerSCLM_apply_zero (f : 𝓢(ℝ, ℂ)) : eulerSCLM f 0 = 0 := by
  rw [eulerSCLM_apply]
  simp

/-! ## The multiplicative flow -/

/-- **The Euler operator is the derivative along the multiplicative flow.** -/
theorem hasDerivAt_comp_exp (f : 𝓢(ℝ, ℂ)) (a t : ℝ) :
    HasDerivAt (fun s : ℝ => f (a * Real.exp s))
      (eulerSCLM f (a * Real.exp t)) t := by
  have hexp : HasDerivAt (fun s : ℝ => a * Real.exp s) (a * Real.exp t) t :=
    (Real.hasDerivAt_exp t).const_mul a
  have hcomp := (f.hasDerivAt (a * Real.exp t)).scomp t hexp
  have hval : (a * Real.exp t) • deriv (f : ℝ → ℂ) (a * Real.exp t)
      = eulerSCLM f (a * Real.exp t) := by
    rw [eulerSCLM_apply, Complex.real_smul]
  rw [← hval]
  exact hcomp

/-! ## Parity -/

/-- The derivative of an even Schwartz function is odd. -/
theorem deriv_neg_of_even_schwartz {f : 𝓢(ℝ, ℂ)} (hf : ∀ x : ℝ, f (-x) = f x) (x : ℝ) :
    deriv (f : ℝ → ℂ) (-x) = -deriv (f : ℝ → ℂ) x := by
  have hfun : (fun y : ℝ => (f : ℝ → ℂ) (-y)) = (f : ℝ → ℂ) := funext hf
  have h1 : deriv (fun y : ℝ => (f : ℝ → ℂ) (-y)) x = -deriv (f : ℝ → ℂ) (-x) :=
    deriv_comp_neg (f : ℝ → ℂ) x
  rw [hfun] at h1
  rw [h1]
  ring

/-- **The Euler operator preserves parity.** -/
theorem eulerSCLM_even {f : 𝓢(ℝ, ℂ)} (hf : ∀ x : ℝ, f (-x) = f x) (x : ℝ) :
    eulerSCLM f (-x) = eulerSCLM f x := by
  rw [eulerSCLM_apply, eulerSCLM_apply, deriv_neg_of_even_schwartz hf x]
  push_cast
  ring

/-! ## The Fourier rule -/

/-- **The Fourier transform intertwines the Euler operator with minus its adjoint**:
`𝓕(θf) = −𝓕f − θ𝓕f`.  Both Fourier rules enter: the transform of a derivative and the derivative
of a transform. -/
theorem fourierSCLM_eulerSCLM (f : 𝓢(ℝ, ℂ)) :
    fourierSCLM (eulerSCLM f) = -(fourierSCLM f) - eulerSCLM (fourierSCLM f) := by
  have h1 := derivSCLM_fourierSCLM (derivSCLM f)
  rw [fourierSCLM_derivSCLM f, map_smul, derivSCLM_mulXCLM] at h1
  have h2 : (2 * (π : ℂ) * I) • (fourierSCLM f + mulXCLM (derivSCLM (fourierSCLM f)))
      = (-2 * (π : ℂ) * I) • fourierSCLM (eulerSCLM f) := by
    rw [h1]
    rfl
  have h3 : (-2 * (π : ℂ) * I) • fourierSCLM (eulerSCLM f)
      = (-2 * (π : ℂ) * I) • (-(fourierSCLM f) - eulerSCLM (fourierSCLM f)) := by
    rw [← h2]
    have hval : (-2 * (π : ℂ) * I) • (-(fourierSCLM f) - eulerSCLM (fourierSCLM f))
        = (2 * (π : ℂ) * I) • (fourierSCLM f + eulerSCLM (fourierSCLM f)) := by
      rw [smul_sub, smul_neg, smul_add]
      have hc : (-2 * (π : ℂ) * I) = -(2 * (π : ℂ) * I) := by ring
      rw [hc, neg_smul, neg_smul, neg_neg]
      abel
    rw [hval]
    rfl
  have hne : (-2 * (π : ℂ) * I) ≠ 0 := by
    have h : (2 * (π : ℂ) * I) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
    intro hzero
    refine h ?_
    have : (-2 * (π : ℂ) * I) = -(2 * (π : ℂ) * I) := by ring
    rw [this, neg_eq_zero] at hzero
    exact hzero
  exact smul_right_injective _ hne h3

/-- The Fourier constraint propagates: `𝓕(θf)(0) = −𝓕f(0)`. -/
theorem fourierSCLM_eulerSCLM_zero (f : 𝓢(ℝ, ℂ)) :
    fourierSCLM (eulerSCLM f) 0 = -(fourierSCLM f 0) := by
  rw [fourierSCLM_eulerSCLM]
  show -(fourierSCLM f 0) - eulerSCLM (fourierSCLM f) 0 = -(fourierSCLM f 0)
  rw [eulerSCLM_apply_zero, sub_zero]

end GaloisForLFunctions

end
