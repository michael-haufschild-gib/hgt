import GaloisForLFunctions.RHTower.DeningerPoincareKForm
import GaloisForLFunctions.RHTower.DeningerExpCover
import GaloisForLFunctions.RHTower.DeningerFormPullback

/-!
# Closed forms of every degree on a character stage

A closed holomorphic form of any degree on a character stage pulls back along the exponential
covering to a closed holomorphic form on the whole covering space, where the Poincaré lemma makes it
exact.  The pullback is periodic in every coordinate, which is the datum from which the descent to
the stage is computed.

* `deningerExpPullbackForm` : the pullback of a stage form of any degree along the covering.
* `deningerExpPullbackForm_closed`, `deningerExpPullbackForm_periodic` : it is closed and periodic.
* `deningerStage_closed_form_exact_upstairs` : it is exact on the covering space.
-/

namespace RHTower

open Complex

section ExpPullbackForm

variable {r n : ℕ}

/-- The pullback of a stage form of any degree along the exponential covering. -/
noncomputable def deningerExpPullbackForm (ω : DeningerStageForm r n) :
    (Fin r → ℂ) → (Fin r → ℂ) [⋀^Fin n]→L[ℂ] ℂ :=
  deningerPullbackForm (deningerExpMap r) ω

/-- The pullback of a holomorphic stage form along the covering is holomorphic everywhere. -/
theorem deningerExpPullbackForm_analytic {ω : DeningerStageForm r n}
    (hω : DeningerIsHolomorphicForm ω) :
    AnalyticOnNhd ℂ (deningerExpPullbackForm ω) Set.univ := by
  intro w _
  refine deningerPullbackForm_analyticAt (hω _ (deningerExpMap_mem w))
    (deningerExpMap_analyticAt w) ?_
  have hexpana : AnalyticOnNhd ℂ (deningerExpMap r) Set.univ :=
    fun y _ => deningerExpMap_analyticAt y
  exact (hexpana.fderiv_of_isOpen isOpen_univ) w (Set.mem_univ w)

/-- **The pullback of a closed form along the covering is closed.** -/
theorem deningerExpPullbackForm_closed {ω : DeningerStageForm r n}
    (hω : DeningerIsHolomorphicForm ω)
    (hclosed : ∀ z ∈ deningerStageTorus r, extDeriv ω z = 0) (w : Fin r → ℂ) :
    extDeriv (deningerExpPullbackForm ω) w = 0 := by
  rw [deningerExpPullbackForm, deningerPullbackForm_extDeriv
    (hω _ (deningerExpMap_mem w)).differentiableAt (deningerExpMap_analyticAt w).contDiffAt]
  show ((extDeriv ω) (deningerExpMap r w)).compContinuousLinearMap
    (fderiv ℂ (deningerExpMap r) w) = 0
  rw [hclosed _ (deningerExpMap_mem w)]
  ext v
  rfl

/-- **The pullback along the covering is periodic in each coordinate**, in every degree. -/
theorem deningerExpPullbackForm_periodic (ω : DeningerStageForm r n) (j : Fin r)
    (w : Fin r → ℂ) :
    deningerExpPullbackForm ω (w + (2 * Real.pi * Complex.I) •
        (Pi.single j (1 : ℂ) : Fin r → ℂ)) = deningerExpPullbackForm ω w := by
  have hfd : ∀ y : Fin r → ℂ, fderiv ℂ (deningerExpMap r) y = deningerExpDeriv y :=
    fun y => (deningerExpMap_hasFDerivAt y).fderiv
  have hderiv : deningerExpDeriv (w + (2 * Real.pi * Complex.I) •
      (Pi.single j (1 : ℂ) : Fin r → ℂ)) = deningerExpDeriv w := by
    refine ContinuousLinearMap.ext fun u => ?_
    funext l
    show Complex.exp ((w + (2 * Real.pi * Complex.I) •
      (Pi.single j (1 : ℂ) : Fin r → ℂ)) l) * u l = Complex.exp (w l) * u l
    rw [show Complex.exp ((w + (2 * Real.pi * Complex.I) •
      (Pi.single j (1 : ℂ) : Fin r → ℂ)) l) = Complex.exp (w l) from
        congrFun (deningerExpMap_periodic j w) l]
  show (ω (deningerExpMap r (w + (2 * Real.pi * Complex.I) •
      (Pi.single j (1 : ℂ) : Fin r → ℂ)))).compContinuousLinearMap
        (fderiv ℂ (deningerExpMap r) (w + (2 * Real.pi * Complex.I) •
          (Pi.single j (1 : ℂ) : Fin r → ℂ))) =
    (ω (deningerExpMap r w)).compContinuousLinearMap (fderiv ℂ (deningerExpMap r) w)
  rw [deningerExpMap_periodic j w, hfd, hfd, hderiv]

/-- **A closed holomorphic form of any degree on a character stage becomes exact on the covering
space**: its pullback is the exterior derivative of the homotopy operator applied to it. -/
theorem deningerStage_closed_form_exact_upstairs {ω : DeningerStageForm r (n + 1)}
    (hω : DeningerIsHolomorphicForm ω)
    (hclosed : ∀ z ∈ deningerStageTorus r, extDeriv ω z = 0) :
    ∀ w : Fin r → ℂ,
      extDeriv (deningerHomotopyOperator (deningerExpPullbackForm ω)) w =
        deningerExpPullbackForm ω w :=
  fun w => deningerExtDeriv_homotopyOperator (deningerExpPullbackForm_analytic hω)
    (deningerExpPullbackForm_closed hω hclosed) w

end ExpPullbackForm

end RHTower
