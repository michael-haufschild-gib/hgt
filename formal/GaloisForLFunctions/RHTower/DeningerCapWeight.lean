import GaloisForLFunctions.RHTower.DeningerCapVanishing
import GaloisForLFunctions.RHTower.DeningerPoissonWeight

/-!
# The logarithmic weights of a member of Meyer's space

Read in the logarithmic coordinate used by the Mellin transform, a member of Meyer's space becomes
`u ↦ e^{-su}f(e^{-u})`.  Differentiating produces the shifted Euler operator with the sign of the
reflected coordinate:

`(e^{-su}f(e^{-u}))' = e^{-su}(B_s f)(e^{-u})`,   `B_s = −(s + θ)`.

Meyer's space is stable under `B_s`, so every derivative of a weight is again a weight of a member
of Meyer's space — the structure that makes the weights Schwartz.

* `deningerCapWeight` : the weight `e^{-su}f(e^{-u})`.
* `deningerCapShiftCLM` : the generator `B_s = −(s + θ)`.
* `hasDerivAt_deningerCapWeight` : **the derivative is the weight of `B_s f`.**
* `iteratedDeriv_deningerCapWeight`, `contDiff_deningerCapWeight` : all derivatives, and
  smoothness.
-/

open scoped Real SchwartzMap ContDiff
open Complex GaloisForLFunctions

noncomputable section

namespace RHTower

/-! ## The generator of the reflected flow -/

/-- The generator of the weighted flow in the reflected coordinate, `B_s = −(s + θ)`. -/
def deningerCapShiftCLM (s : ℤ) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) := -(deningerShiftCLM s)

theorem deningerCapShiftCLM_apply (s : ℤ) (f : 𝓢(ℝ, ℂ)) :
    deningerCapShiftCLM s f = -(deningerShiftCLM s f) := rfl

theorem deningerMeyerCap_capShiftCLM {f : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerMeyerCap) (s : ℤ) :
    deningerCapShiftCLM s f ∈ DeningerMeyerCap := by
  rw [deningerCapShiftCLM_apply]
  exact Submodule.neg_mem _ (deningerMeyerCap_shiftCLM hf s)

theorem deningerMeyerCap_capShiftCLM_iterate {f : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerMeyerCap) (s : ℤ)
    (n : ℕ) : ((deningerCapShiftCLM s)^[n]) f ∈ DeningerMeyerCap := by
  induction n generalizing f with
  | zero =>
    rw [Function.iterate_zero_apply]
    exact hf
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    exact ih (deningerMeyerCap_capShiftCLM hf s)

/-! ## The weight and its derivative -/

/-- The logarithmic weight of a Schwartz function in the reflected coordinate. -/
def deningerCapWeight (s : ℤ) (f : 𝓢(ℝ, ℂ)) (u : ℝ) : ℂ :=
  ((Real.exp (-(s : ℝ) * u) : ℝ) : ℂ) * f (Real.exp (-u))

theorem hasDerivAt_capExp (s : ℤ) (u : ℝ) :
    HasDerivAt (fun y : ℝ => ((Real.exp (-(s : ℝ) * y) : ℝ) : ℂ))
      (-(s : ℂ) * ((Real.exp (-(s : ℝ) * u) : ℝ) : ℂ)) u := by
  have hreal : HasDerivAt (fun y : ℝ => Real.exp (-(s : ℝ) * y))
      (-(s : ℝ) * Real.exp (-(s : ℝ) * u)) u := by
    have hlin : HasDerivAt (fun y : ℝ => -(s : ℝ) * y) (-(s : ℝ)) u := by
      simpa using (hasDerivAt_id u).const_mul (-(s : ℝ))
    have hcomp := (Real.hasDerivAt_exp (-(s : ℝ) * u)).comp u hlin
    have hfun : (Real.exp ∘ fun y : ℝ => -(s : ℝ) * y)
        = fun y : ℝ => Real.exp (-(s : ℝ) * y) := rfl
    rw [hfun] at hcomp
    exact hcomp.congr_deriv (by ring)
  have hcast := hreal.ofReal_comp
  refine hcast.congr_deriv ?_
  push_cast
  ring

theorem hasDerivAt_comp_exp_neg (f : 𝓢(ℝ, ℂ)) (u : ℝ) :
    HasDerivAt (fun y : ℝ => f (Real.exp (-y))) (-(eulerSCLM f (Real.exp (-u)))) u := by
  have hbase := hasDerivAt_comp_exp f 1 (-u)
  have hfun : (fun y : ℝ => f (1 * Real.exp y)) = fun y : ℝ => f (Real.exp y) := by
    funext y
    rw [one_mul]
  rw [hfun] at hbase
  have hneg : HasDerivAt (fun y : ℝ => -y) (-1 : ℝ) u := hasDerivAt_neg u
  have hcomp := hbase.scomp u hneg
  have hval : eulerSCLM f (1 * Real.exp (-u)) = eulerSCLM f (Real.exp (-u)) := by
    rw [one_mul]
  rw [hval] at hcomp
  refine hcomp.congr_deriv ?_
  rw [neg_one_smul]

/-- **The derivative of a weight is the weight of the reflected shifted Euler transform.** -/
theorem hasDerivAt_deningerCapWeight (s : ℤ) (f : 𝓢(ℝ, ℂ)) (u : ℝ) :
    HasDerivAt (deningerCapWeight s f)
      (deningerCapWeight s (deningerCapShiftCLM s f) u) u := by
  have hprod := (hasDerivAt_capExp s u).mul (hasDerivAt_comp_exp_neg f u)
  refine hprod.congr_deriv ?_
  rw [deningerCapWeight, deningerCapShiftCLM_apply, deningerShiftCLM_apply]
  show -(s : ℂ) * ((Real.exp (-(s : ℝ) * u) : ℝ) : ℂ) * f (Real.exp (-u))
      + ((Real.exp (-(s : ℝ) * u) : ℝ) : ℂ) * -(eulerSCLM f (Real.exp (-u)))
    = ((Real.exp (-(s : ℝ) * u) : ℝ) : ℂ)
      * (-(((s : ℂ)) • f + eulerSCLM f)) (Real.exp (-u))
  rw [_root_.neg_apply, _root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring

theorem differentiable_deningerCapWeight (s : ℤ) (f : 𝓢(ℝ, ℂ)) :
    Differentiable ℝ (deningerCapWeight s f) := fun u =>
  (hasDerivAt_deningerCapWeight s f u).differentiableAt

theorem deriv_deningerCapWeight (s : ℤ) (f : 𝓢(ℝ, ℂ)) :
    deriv (deningerCapWeight s f) = deningerCapWeight s (deningerCapShiftCLM s f) := by
  funext u
  exact (hasDerivAt_deningerCapWeight s f u).deriv

/-! ## Smoothness and the iterated derivatives -/

theorem contDiff_nat_deningerCapWeight (n : ℕ) (s : ℤ) (f : 𝓢(ℝ, ℂ)) :
    ContDiff ℝ n (deningerCapWeight s f) := by
  induction n generalizing f with
  | zero =>
    have h : ContDiff ℝ 0 (deningerCapWeight s f) :=
      contDiff_zero.mpr (differentiable_deningerCapWeight s f).continuous
    simpa using h
  | succ n ih =>
    have hcast : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by
      push_cast
      ring
    rw [hcast]
    refine contDiff_succ_iff_deriv.mpr ⟨differentiable_deningerCapWeight s f, ?_, ?_⟩
    · intro hω
      exact absurd hω (by simp)
    · rw [deriv_deningerCapWeight]
      exact ih (deningerCapShiftCLM s f)

/-- **The weights are smooth.** -/
theorem contDiff_deningerCapWeight (s : ℤ) (f : 𝓢(ℝ, ℂ)) :
    ContDiff ℝ ∞ (deningerCapWeight s f) :=
  contDiff_infty.mpr fun n => contDiff_nat_deningerCapWeight n s f

/-- **Every derivative of a weight is a weight.** -/
theorem iteratedDeriv_deningerCapWeight (n : ℕ) (s : ℤ) (f : 𝓢(ℝ, ℂ)) :
    iteratedDeriv n (deningerCapWeight s f)
      = deningerCapWeight s (((deningerCapShiftCLM s)^[n]) f) := by
  induction n generalizing f with
  | zero =>
    rw [iteratedDeriv_zero, Function.iterate_zero_apply]
  | succ n ih =>
    rw [iteratedDeriv_succ', deriv_deningerCapWeight, ih (deningerCapShiftCLM s f),
      Function.iterate_succ_apply]

end RHTower

end
