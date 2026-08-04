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

/-- The pullback along the covering is differentiable everywhere. -/
theorem deningerExpPullbackForm_differentiable {ω : DeningerStageForm r n}
    (hω : DeningerIsHolomorphicForm ω) : Differentiable ℂ (deningerExpPullbackForm ω) :=
  fun w => ((deningerExpPullbackForm_analytic hω) w (Set.mem_univ w)).differentiableAt

/-- The derivative of the pullback along the covering is continuous. -/
theorem deningerExpPullbackForm_fderiv_continuous {ω : DeningerStageForm r n}
    (hω : DeningerIsHolomorphicForm ω) :
    Continuous (fderiv ℂ (deningerExpPullbackForm ω)) := by
  rw [continuous_iff_continuousAt]
  intro w
  exact (((deningerExpPullbackForm_analytic hω).fderiv_of_isOpen isOpen_univ) w
    (Set.mem_univ w)).continuousAt

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
  fun w => deningerExtDeriv_homotopyOperator (deningerExpPullbackForm_differentiable hω)
    (deningerExpPullbackForm_fderiv_continuous hω) (deningerExpPullbackForm_closed hω hclosed) w

end ExpPullbackForm

end RHTower

namespace RHTower

section Translate

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {n : ℕ}

/-- Composing an alternating form with the identity does nothing. -/
theorem deningerCompContinuousLinearMap_id (A : E [⋀^Fin n]→L[ℂ] ℂ) :
    A.compContinuousLinearMap (ContinuousLinearMap.id ℂ E) = A := by
  ext v
  rfl

/-- **The exterior derivative commutes with translation.** -/
theorem deningerExtDeriv_translate (η : E → E [⋀^Fin n]→L[ℂ] ℂ) (c w : E)
    (hη : DifferentiableAt ℂ η (w + c)) :
    extDeriv (fun y => η (y + c)) w = extDeriv η (w + c) := by
  have hpull : deningerPullbackForm (fun y : E => y + c) η = fun y => η (y + c) := by
    funext y
    show (η (y + c)).compContinuousLinearMap (fderiv ℂ (fun z : E => z + c) y) = η (y + c)
    have hfd : fderiv ℂ (fun z : E => z + c) y = ContinuousLinearMap.id ℂ E :=
      ((hasFDerivAt_id y).add_const c).fderiv
    rw [hfd]
    exact deningerCompContinuousLinearMap_id _
  have hf : ContDiffAt ℂ ⊤ (fun y : E => y + c) w :=
    (contDiff_id.add contDiff_const).contDiffAt
  have h := deningerPullbackForm_extDeriv (f := fun y : E => y + c) (ω := η) hη hf
  rw [hpull] at h
  rw [h]
  show (extDeriv η (w + c)).compContinuousLinearMap (fderiv ℂ (fun z : E => z + c) w) =
    extDeriv η (w + c)
  have hfdw : fderiv ℂ (fun z : E => z + c) w = ContinuousLinearMap.id ℂ E :=
    ((hasFDerivAt_id w).add_const c).fderiv
  rw [hfdw]
  exact deningerCompContinuousLinearMap_id _

end Translate

section PeriodDefect

variable {r n : ℕ}

/-- **The periodicity defect of the primitive on the covering space is a closed form** of one degree
lower.  This is the first step of the descent: the classes of these defects are what the cohomology
of the stage is built from. -/
theorem deningerPeriodDefect_closed {ω : DeningerStageForm r (n + 1)}
    (hω : DeningerIsHolomorphicForm ω)
    (hclosed : ∀ z ∈ deningerStageTorus r, extDeriv ω z = 0) (j : Fin r) (w : Fin r → ℂ) :
    extDeriv ((fun y : Fin r → ℂ => deningerHomotopyOperator (deningerExpPullbackForm ω)
        (y + (2 * Real.pi * Complex.I) • (Pi.single j (1 : ℂ) : Fin r → ℂ))) +
      (-1 : ℂ) • deningerHomotopyOperator (deningerExpPullbackForm ω)) w = 0 := by
  set c : Fin r → ℂ := (2 * Real.pi * Complex.I) • (Pi.single j (1 : ℂ) : Fin r → ℂ) with hc
  set η := deningerHomotopyOperator (deningerExpPullbackForm ω) with hη
  have hdiff : ∀ y : Fin r → ℂ, DifferentiableAt ℂ η y := fun y =>
    (deningerHomotopyOperator_hasFDerivAt (deningerExpPullbackForm_differentiable hω)
      (deningerExpPullbackForm_fderiv_continuous hω) y).differentiableAt
  have hshift : DifferentiableAt ℂ (fun y : Fin r → ℂ => η (y + c)) w := by
    have hadd : DifferentiableAt ℂ (fun y : Fin r → ℂ => y + c) w :=
      (differentiableAt_id).add_const c
    exact (hdiff (w + c)).comp w hadd
  rw [extDeriv_add hshift ((hdiff w).const_smul _), extDeriv_smul,
    deningerExtDeriv_translate η c w (hdiff (w + c))]
  rw [hη, deningerStage_closed_form_exact_upstairs hω hclosed,
    deningerStage_closed_form_exact_upstairs hω hclosed]
  rw [hc, deningerExpPullbackForm_periodic ω j w]
  simp

end PeriodDefect

end RHTower
