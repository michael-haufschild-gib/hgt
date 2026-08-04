import GaloisForLFunctions.RHTower.DeningerFullAverage
import GaloisForLFunctions.RHTower.DeningerStageExactDescent
import GaloisForLFunctions.RHTower.DeningerConstantFormVanishing

/-!
# Closed forms on a character stage are constant forms up to exact forms

The descent of a constant form along the exponential covering is the stage form whose coefficients
are constant in the logarithmic coordinates.  Every closed holomorphic form on a character stage is
such a form plus an exact form: its pullback is closed and periodic on the covering space, and
averaging over all the periods makes it constant while changing it only by the exterior derivative
of a periodic form, which descends.  The constant form is determined by the class: the difference of
two constant forms that is exact pulls back to a constant form with a periodic primitive.

* `deningerConstantStageForm` : the stage form with constant coefficients in the logarithms.
* `deningerStage_closed_form_decomposition` : every closed holomorphic form is a constant form plus
  an exact form.
* `deningerConstantStageForm_unique` : the constant form is determined by the class.
-/

namespace RHTower

open Complex ContinuousAlternatingMap

section ConstantStageForm

variable {r n : ℕ}

/-- **The stage form with constant coefficients in the logarithmic coordinates**: the descent of a
constant form along the exponential covering. -/
noncomputable def deningerConstantStageForm (α : (Fin r → ℂ) [⋀^Fin n]→L[ℂ] ℂ) :
    DeningerStageForm r n :=
  deningerDescendForm (fun _ : Fin r → ℂ => α)

theorem deningerConstantStageForm_apply (α : (Fin r → ℂ) [⋀^Fin n]→L[ℂ] ℂ) (z : Fin r → ℂ) :
    deningerConstantStageForm α z = α.compContinuousLinearMap (deningerLogBranchDeriv z) := rfl

/-- **The pullback of a constant stage form along the covering is the constant form.** -/
theorem deningerConstantStageForm_pullback (α : (Fin r → ℂ) [⋀^Fin n]→L[ℂ] ℂ) (w : Fin r → ℂ) :
    deningerExpPullbackForm (deningerConstantStageForm α) w = α :=
  deningerDescendForm_pullback (fun _ _ => rfl) w

/-- The pullback along the covering is additive in the form. -/
theorem deningerExpPullbackForm_add (A B : DeningerStageForm r n) (w : Fin r → ℂ) :
    deningerExpPullbackForm (fun z => A z + B z) w =
      deningerExpPullbackForm A w + deningerExpPullbackForm B w := by
  ext v
  rfl

/-- The pullback along the covering is compatible with differences of forms. -/
theorem deningerExpPullbackForm_sub (A B : DeningerStageForm r n) (w : Fin r → ℂ) :
    deningerExpPullbackForm (fun z => A z - B z) w =
      deningerExpPullbackForm A w - deningerExpPullbackForm B w := by
  ext v
  rfl

end ConstantStageForm

end RHTower

namespace RHTower

open Complex ContinuousAlternatingMap

section Decomposition

variable {r n : ℕ}

/-- **Every closed holomorphic form on a character stage is a constant form plus an exact form.**
The pullback along the exponential covering is closed and periodic, so averaging it over all the
coordinate periods produces a constant form and a periodic primitive of the difference, and a
periodic primitive descends to the stage. -/
theorem deningerStage_closed_form_decomposition {ω : DeningerStageForm r (n + 1)}
    (hω : DeningerIsHolomorphicForm ω)
    (hclosed : ∀ z ∈ deningerStageTorus r, extDeriv ω z = 0) :
    ∃ (α : (Fin r → ℂ) [⋀^Fin (n + 1)]→L[ℂ] ℂ) (θ : DeningerStageForm r n),
      ∀ z ∈ deningerStageTorus r, ω z = deningerConstantStageForm α z + extDeriv θ z := by
  obtain ⟨α, η, hηdiff, -, hηper, hηeq⟩ :=
    deningerPeriodic_closed_eq_const_add_exact
      (deningerExpPullbackForm_differentiable hω)
      (deningerExpPullbackForm_fderiv_continuous hω)
      (fun l w => deningerExpPullbackForm_periodic ω l w)
      (deningerExpPullbackForm_closed hω hclosed)
  refine ⟨α, deningerDescendForm η, fun z hz => ?_⟩
  have hprim : ∀ w : Fin r → ℂ, extDeriv η w =
      deningerExpPullbackForm (fun y => ω y - deningerConstantStageForm α y) w := by
    intro w
    rw [deningerExpPullbackForm_sub, deningerConstantStageForm_pullback, hηeq w]
    abel
  have hexact := deningerStage_exact_of_primitive
    (ω := fun y => ω y - deningerConstantStageForm α y) hηdiff hηper hprim hz
  show ω z = deningerConstantStageForm α z + extDeriv (deningerDescendForm η) z
  rw [hexact]
  abel

/-- **The constant form of a class is determined by the class.**  If two constant stage forms differ
by the exterior derivative of a holomorphic form, then the difference pulls back to a constant form
whose primitive is periodic, hence vanishes. -/
theorem deningerConstantStageForm_unique {α α' : (Fin r → ℂ) [⋀^Fin (n + 1)]→L[ℂ] ℂ}
    {θ : DeningerStageForm r n} (hθ : DeningerIsHolomorphicForm θ)
    (h : ∀ z ∈ deningerStageTorus r,
      deningerConstantStageForm α z = deningerConstantStageForm α' z + extDeriv θ z) :
    α = α' := by
  have hpull : ∀ w : Fin r → ℂ, extDeriv (deningerExpPullbackForm θ) w = α - α' := by
    intro w
    have hz : deningerExpMap r w ∈ deningerStageTorus r := deningerExpMap_mem w
    have hstep : deningerExpPullbackForm (deningerConstantStageForm α) w =
        deningerExpPullbackForm (fun z => deningerConstantStageForm α' z + extDeriv θ z) w := by
      show (deningerConstantStageForm α (deningerExpMap r w)).compContinuousLinearMap
          (fderiv ℂ (deningerExpMap r) w) =
        (deningerConstantStageForm α' (deningerExpMap r w) +
          extDeriv θ (deningerExpMap r w)).compContinuousLinearMap
            (fderiv ℂ (deningerExpMap r) w)
      rw [h _ hz]
    rw [deningerExpPullbackForm_add, deningerConstantStageForm_pullback,
      deningerConstantStageForm_pullback] at hstep
    have hcomm : extDeriv (deningerExpPullbackForm θ) w =
        deningerExpPullbackForm (extDeriv θ) w := by
      rw [deningerExpPullbackForm, deningerPullbackForm_extDeriv
        (hθ _ (deningerExpMap_mem w)).differentiableAt (deningerExpMap_analyticAt w).contDiffAt]
      rfl
    rw [hcomm, hstep]
    abel
  have hzero : α - α' = 0 :=
    deningerConstantForm_eq_zero n (α - α') (deningerExpPullbackForm θ)
      (deningerExpPullbackForm_differentiable hθ)
      (deningerExpPullbackForm_fderiv_continuous hθ)
      (fun l w => deningerExpPullbackForm_periodic θ l w) hpull
  exact sub_eq_zero.1 hzero

end Decomposition

end RHTower
