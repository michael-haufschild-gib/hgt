import GaloisForLFunctions.RHTower.Deninger.DeningerConstantFormVanishing
import GaloisForLFunctions.RHTower.Deninger.DeningerWedgePullback

/-!
# The generators are not exact

An exterior product of logarithmic differentials on a character stage is not the exterior derivative
of a holomorphic form.  Pulled back along the exponential covering it becomes a constant form whose
primitive is periodic, and such a form vanishes; but the determinant form is one on the coordinate
basis it selects.

* `deningerDlogWedge_not_exact` : the generators are not exact, in every degree.
-/

namespace RHTower

open Complex

section WedgeNotExact

variable {r k : ℕ}

/-- **The exterior product of logarithmic differentials is not exact on the stage.**  This is the
independence of the generators of `(5)` in every degree. -/
theorem deningerDlogWedge_not_exact {σ : Fin (k + 1) → Fin r} (hσ : Function.Injective σ)
    (θ : DeningerStageForm r k) (hθ : DeningerIsHolomorphicForm θ)
    (hd : ∀ z ∈ deningerStageTorus r, extDeriv θ z = deningerDlogWedge σ z) : False := by
  -- the pullback of the primitive is periodic and continuously differentiable
  have hdiff : Differentiable ℂ (deningerExpPullbackForm θ) :=
    deningerExpPullbackForm_differentiable hθ
  have hcont : Continuous (fderiv ℂ (deningerExpPullbackForm θ)) :=
    deningerExpPullbackForm_fderiv_continuous hθ
  have hper : ∀ (l : Fin r) (w : Fin r → ℂ),
      deningerExpPullbackForm θ (w + (2 * Real.pi * Complex.I) •
        (Pi.single l (1 : ℂ) : Fin r → ℂ)) = deningerExpPullbackForm θ w :=
    fun l w => deningerExpPullbackForm_periodic θ l w
  -- its exterior derivative is the constant determinant form
  have hderiv : ∀ w : Fin r → ℂ,
      extDeriv (deningerExpPullbackForm θ) w = deningerDetForm σ := by
    intro w
    rw [deningerExpPullbackForm, deningerPullbackForm_extDeriv
      (hθ _ (deningerExpMap_mem w)).differentiableAt (deningerExpMap_analyticAt w).contDiffAt]
    show ((extDeriv θ) (deningerExpMap r w)).compContinuousLinearMap
      (fderiv ℂ (deningerExpMap r) w) = deningerDetForm σ
    rw [hd _ (deningerExpMap_mem w)]
    exact deningerExpPullback_dlogWedge σ w
  have hzero : deningerDetForm σ = (0 : (Fin r → ℂ) [⋀^Fin (k + 1)]→L[ℂ] ℂ) :=
    deningerConstantForm_eq_zero k (deningerDetForm σ) (deningerExpPullbackForm θ)
      hdiff hcont hper hderiv
  -- but the determinant form is one on the coordinate basis it selects
  have hone : deningerDetForm σ (fun a => (Pi.single (σ a) (1 : ℂ) : Fin r → ℂ)) = 1 :=
    deningerDetForm_stdBasis hσ
  rw [hzero] at hone
  exact one_ne_zero hone.symm

end WedgeNotExact

end RHTower
