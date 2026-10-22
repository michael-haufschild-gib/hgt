import GaloisForLFunctions.RHTower.Deninger.DeningerPoissonDerivative

/-!
# The exponential weights of the Poisson sum

The Poisson sum is linear in its argument, so the derivative rule `G_f' = G_{θf}` combines with the
product rule into

`d/dt (e^{st} G_f(t)) = e^{st} G_{(s + θ)f}(t)`,

a single operator `A_s = s + θ` acting on the Schwartz argument.  Meyer's space is stable under it,
so every derivative of every exponential weight of a Poisson sum is again an exponentially weighted
Poisson sum of a member of Meyer's space.

* `deningerShiftCLM` : the operator `A_s = s + θ`.
* `hasDerivAt_deningerPoissonWeight` : **`(e^{st}G_f)' = e^{st}G_{A_s f}`.**
* `iteratedDeriv_deningerPoissonWeight` : **the `n`-th derivative is `e^{st}G_{A_sⁿ f}`.**
* `contDiff_deningerPoissonWeight` : the weights are smooth.
-/

open scoped Real SchwartzMap FourierTransform ContDiff
open Complex MeasureTheory GaloisForLFunctions GaloisForLFunctions.RHTower

noncomputable section

namespace RHTower

/-! ## Linearity of the Poisson sum -/

theorem deningerPoissonLog_add (f g : 𝓢(ℝ, ℂ)) (t : ℝ) :
    deningerPoissonLog (f + g) t = deningerPoissonLog f t + deningerPoissonLog g t := by
  rw [deningerPoissonLog, deningerPoissonLog, deningerPoissonLog,
    ← (summable_deningerPoissonLogTerm f t).tsum_add (summable_deningerPoissonLogTerm g t)]
  refine tsum_congr fun n => ?_
  rfl

theorem deningerPoissonLog_smul (c : ℂ) (f : 𝓢(ℝ, ℂ)) (t : ℝ) :
    deningerPoissonLog (c • f) t = c * deningerPoissonLog f t := by
  rw [deningerPoissonLog, deningerPoissonLog, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rfl

/-! ## The shifted Euler operator -/

/-- **The generator of the weighted flow** `A_s = s + θ`. -/
def deningerShiftCLM (s : ℤ) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  ((s : ℂ)) • ContinuousLinearMap.id ℂ 𝓢(ℝ, ℂ) + eulerSCLM

theorem deningerShiftCLM_apply (s : ℤ) (f : 𝓢(ℝ, ℂ)) :
    deningerShiftCLM s f = ((s : ℂ)) • f + eulerSCLM f := rfl

/-- **Meyer's space is stable under the generator of the weighted flow.** -/
theorem deningerMeyerCap_shiftCLM {f : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerMeyerCap) (s : ℤ) :
    deningerShiftCLM s f ∈ DeningerMeyerCap := by
  rw [deningerShiftCLM_apply]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ hf) (deningerMeyerCap_eulerSCLM hf)

theorem deningerMeyerCap_shiftCLM_iterate {f : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerMeyerCap) (s : ℤ)
    (n : ℕ) : ((deningerShiftCLM s)^[n]) f ∈ DeningerMeyerCap := by
  induction n generalizing f with
  | zero =>
    rw [Function.iterate_zero_apply]
    exact hf
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    exact ih (deningerMeyerCap_shiftCLM hf s)

/-! ## The exponential weight -/

/-- The exponential weight `e^{st}` as a complex-valued function of the logarithmic
coordinate. -/
def deningerExpWeight (s : ℤ) (t : ℝ) : ℂ := ((Real.exp ((s : ℝ) * t) : ℝ) : ℂ)

theorem hasDerivAt_deningerExpWeight (s : ℤ) (t : ℝ) :
    HasDerivAt (deningerExpWeight s) ((s : ℂ) * deningerExpWeight s t) t := by
  have hreal : HasDerivAt (fun y : ℝ => Real.exp ((s : ℝ) * y))
      ((s : ℝ) * Real.exp ((s : ℝ) * t)) t := by
    have hlin : HasDerivAt (fun y : ℝ => (s : ℝ) * y) (s : ℝ) t := by
      simpa using (hasDerivAt_id t).const_mul ((s : ℝ))
    have hcomp := (Real.hasDerivAt_exp ((s : ℝ) * t)).comp t hlin
    have hfun : (Real.exp ∘ fun y : ℝ => (s : ℝ) * y)
        = fun y : ℝ => Real.exp ((s : ℝ) * y) := rfl
    rw [hfun] at hcomp
    exact hcomp.congr_deriv (by ring)
  have hcomp := hreal.ofReal_comp
  refine hcomp.congr_deriv ?_
  rw [deningerExpWeight]
  push_cast
  ring

/-- **The weighted Poisson sum**, `t ↦ e^{st}G_f(t)`. -/
def deningerPoissonWeight (s : ℤ) (f : 𝓢(ℝ, ℂ)) (t : ℝ) : ℂ :=
  deningerExpWeight s t * deningerPoissonLog f t

/-- **The derivative of a weighted Poisson sum is the weighted Poisson sum of the shifted Euler
transform.** -/
theorem hasDerivAt_deningerPoissonWeight (s : ℤ) (f : 𝓢(ℝ, ℂ)) (t : ℝ) :
    HasDerivAt (deningerPoissonWeight s f)
      (deningerPoissonWeight s (deningerShiftCLM s f) t) t := by
  have hprod := (hasDerivAt_deningerExpWeight s t).mul (hasDerivAt_deningerPoissonLog f t)
  refine hprod.congr_deriv ?_
  rw [deningerPoissonWeight, deningerShiftCLM_apply, deningerPoissonLog_add,
    deningerPoissonLog_smul]
  ring

theorem differentiable_deningerPoissonWeight (s : ℤ) (f : 𝓢(ℝ, ℂ)) :
    Differentiable ℝ (deningerPoissonWeight s f) := fun t =>
  (hasDerivAt_deningerPoissonWeight s f t).differentiableAt

theorem deriv_deningerPoissonWeight (s : ℤ) (f : 𝓢(ℝ, ℂ)) :
    deriv (deningerPoissonWeight s f) = deningerPoissonWeight s (deningerShiftCLM s f) := by
  funext t
  exact (hasDerivAt_deningerPoissonWeight s f t).deriv

/-! ## Smoothness and the iterated derivatives -/

theorem contDiff_nat_deningerPoissonWeight (n : ℕ) (s : ℤ) (f : 𝓢(ℝ, ℂ)) :
    ContDiff ℝ n (deningerPoissonWeight s f) := by
  induction n generalizing f with
  | zero =>
    have h : ContDiff ℝ 0 (deningerPoissonWeight s f) :=
      contDiff_zero.mpr (differentiable_deningerPoissonWeight s f).continuous
    simpa using h
  | succ n ih =>
    have hcast : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by
      push_cast
      ring
    rw [hcast]
    refine contDiff_succ_iff_deriv.mpr ⟨differentiable_deningerPoissonWeight s f, ?_, ?_⟩
    · intro hω
      exact absurd hω (by simp)
    · rw [deriv_deningerPoissonWeight]
      exact ih (deningerShiftCLM s f)

/-- **The weighted Poisson sums are smooth.** -/
theorem contDiff_deningerPoissonWeight (s : ℤ) (f : 𝓢(ℝ, ℂ)) :
    ContDiff ℝ ∞ (deningerPoissonWeight s f) :=
  contDiff_infty.mpr fun n => contDiff_nat_deningerPoissonWeight n s f

/-- **Every derivative of a weighted Poisson sum is a weighted Poisson sum.** -/
theorem iteratedDeriv_deningerPoissonWeight (n : ℕ) (s : ℤ) (f : 𝓢(ℝ, ℂ)) :
    iteratedDeriv n (deningerPoissonWeight s f)
      = deningerPoissonWeight s (((deningerShiftCLM s)^[n]) f) := by
  induction n generalizing f with
  | zero =>
    rw [iteratedDeriv_zero, Function.iterate_zero_apply]
  | succ n ih =>
    rw [iteratedDeriv_succ', deriv_deningerPoissonWeight, ih (deningerShiftCLM s f),
      Function.iterate_succ_apply]

end RHTower

end
