import GaloisForLFunctions.RHTower.DeningerStageDlogCohomology
import GaloisForLFunctions.HTGeometry.PolydiscAnalytic

/-!
# The descended primitive is holomorphic

A periodic form on the covering space that is complex differentiable is analytic, by the several
variable analyticity of a complex differentiable function; near a point of the stage the descended
form is its pullback along a branch of the logarithm, which is analytic there, so the descended form
is a holomorphic stage form.  The primitives produced by the averaging construction are therefore
holomorphic, and the cohomology of a character stage is computed inside the holomorphic de Rham
complex.

* `deningerLogBranch_analyticAt` : a branch of the logarithm is analytic on its domain.
* `deningerDescendForm_holomorphic` : the descent of a periodic `C^(1 : ℕ)` form is holomorphic.
* `deningerStage_closed_form_decomposition_hol` : the decomposition with a holomorphic primitive.
-/

namespace RHTower

open Complex Filter Topology

section BranchAnalytic

variable {r : ℕ}

/-- The domain of a branch of the logarithm centred at a point of the stage. -/
def deningerBranchDomain (z₀ : Fin r → ℂ) : Set (Fin r → ℂ) :=
  {z : Fin r → ℂ | ∀ j, z j / z₀ j ∈ Complex.slitPlane}

theorem deningerBranchDomain_isOpen (z₀ : Fin r → ℂ) : IsOpen (deningerBranchDomain z₀) := by
  have hset : deningerBranchDomain z₀ =
      ⋂ j : Fin r, {z : Fin r → ℂ | z j / z₀ j ∈ Complex.slitPlane} := by
    ext z
    simp [deningerBranchDomain, Set.mem_iInter]
  rw [hset]
  refine isOpen_iInter_of_finite fun j => ?_
  exact Complex.isOpen_slitPlane.preimage (by fun_prop)

theorem deningerBranchDomain_mem_self {z₀ : Fin r → ℂ} (hz₀ : z₀ ∈ deningerStageTorus r) :
    z₀ ∈ deningerBranchDomain z₀ := by
  intro j
  rw [div_self (hz₀ j)]
  exact Complex.one_mem_slitPlane

/-- **A branch of the logarithm is analytic on its domain.** -/
theorem deningerLogBranch_analyticAt {z₀ z : Fin r → ℂ}
    (hz : z ∈ deningerBranchDomain z₀) : AnalyticAt ℂ (deningerLogBranch z₀) z := by
  refine AnalyticAt.pi fun j => ?_
  have hdivana : AnalyticAt ℂ (fun y : Fin r → ℂ => y j / z₀ j) z := by
    have hfun : (fun y : Fin r → ℂ => y j / z₀ j) =
        ⇑((z₀ j)⁻¹ • (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) j)) := by
      funext y
      show y j / z₀ j = (z₀ j)⁻¹ * y j
      rw [div_eq_inv_mul]
    rw [hfun]
    exact ((z₀ j)⁻¹ •
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) j)).analyticAt z
  have hlogana : AnalyticAt ℂ Complex.log ((fun y : Fin r → ℂ => y j / z₀ j) z) := by
    show AnalyticAt ℂ Complex.log (z j / z₀ j)
    have hdiffOn : DifferentiableOn ℂ Complex.log Complex.slitPlane :=
      fun x hx => (Complex.differentiableAt_log hx).differentiableWithinAt
    exact (hdiffOn.analyticOnNhd Complex.isOpen_slitPlane) _ (hz j)
  exact AnalyticAt.add analyticAt_const
    (AnalyticAt.comp (f := fun y : Fin r → ℂ => y j / z₀ j) hlogana hdivana)

/-- **The derivative of a branch of the logarithm is analytic.** -/
theorem deningerLogBranchDeriv_analyticAt {z₀ : Fin r → ℂ} (hz₀ : z₀ ∈ deningerStageTorus r) :
    AnalyticAt ℂ (fderiv ℂ (deningerLogBranch z₀)) z₀ := by
  have hana : AnalyticOnNhd ℂ (deningerLogBranch z₀) (deningerBranchDomain z₀) :=
    fun z hz => deningerLogBranch_analyticAt hz
  exact (hana.fderiv_of_isOpen (deningerBranchDomain_isOpen z₀)) z₀
    (deningerBranchDomain_mem_self hz₀)

end BranchAnalytic

end RHTower

namespace RHTower

open Complex Filter Topology GaloisForLFunctions.HTGeometry

section HolomorphicDescent

variable {r n : ℕ}

/-- **The descent of a periodic complex differentiable form is a holomorphic stage form.**  The
form is analytic on the covering space because a complex differentiable function of several
variables is analytic, and near a point of the stage the descended form is its pullback along a
branch of the logarithm. -/
theorem deningerDescendForm_holomorphic {η : (Fin r → ℂ) → (Fin r → ℂ) [⋀^Fin n]→L[ℂ] ℂ}
    (hdiff : Differentiable ℂ η)
    (hper : ∀ (j : Fin r) (w : Fin r → ℂ),
      η (w + (2 * Real.pi * Complex.I) • (Pi.single j (1 : ℂ) : Fin r → ℂ)) = η w) :
    DeningerIsHolomorphicForm (deningerDescendForm η) := by
  intro z₀ hz₀
  have hpull : AnalyticAt ℂ (deningerPullbackForm (deningerLogBranch z₀) η) z₀ := by
    refine deningerPullbackForm_analyticAt ?_ ?_ (deningerLogBranchDeriv_analyticAt hz₀)
    · exact analyticAt_of_differentiable hdiff _
    · exact deningerLogBranch_analyticAt (deningerBranchDomain_mem_self hz₀)
  exact hpull.congr (deningerDescendForm_eventuallyEq hper hz₀).symm

/-- **A constant stage form is holomorphic.** -/
theorem deningerConstantStageForm_holomorphic (α : (Fin r → ℂ) [⋀^Fin n]→L[ℂ] ℂ) :
    DeningerIsHolomorphicForm (deningerConstantStageForm α) :=
  deningerDescendForm_holomorphic (differentiable_const α) fun _ _ => rfl

/-- **Every closed holomorphic form on a character stage is a constant form plus the exterior
derivative of a holomorphic form.**  This is the cohomology of the stage computed inside the
holomorphic de Rham complex. -/
theorem deningerStage_closed_form_decomposition_hol {ω : DeningerStageForm r (n + 1)}
    (hω : DeningerIsHolomorphicForm ω)
    (hclosed : ∀ z ∈ deningerStageTorus r, extDeriv ω z = 0) :
    ∃ (α : (Fin r → ℂ) [⋀^Fin (n + 1)]→L[ℂ] ℂ) (θ : DeningerStageForm r n),
      DeningerIsHolomorphicForm θ ∧
      ∀ z ∈ deningerStageTorus r, ω z = deningerConstantStageForm α z + extDeriv θ z := by
  obtain ⟨α, η, hηdiff, -, hηper, hηeq⟩ :=
    deningerPeriodic_closed_eq_const_add_exact
      (deningerExpPullbackForm_differentiable hω)
      (deningerExpPullbackForm_fderiv_continuous hω)
      (fun l w => deningerExpPullbackForm_periodic ω l w)
      (deningerExpPullbackForm_closed hω hclosed)
  refine ⟨α, deningerDescendForm η,
    deningerDescendForm_holomorphic hηdiff (fun j w => hηper j w), fun z hz => ?_⟩
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

/-- **The cohomology of a character stage, inside the holomorphic de Rham complex**: every closed
holomorphic form is a combination of the exterior products of the logarithmic differentials of the
coordinates plus the exterior derivative of a holomorphic form. -/
theorem deningerStage_closed_form_dlog_decomposition_hol {ω : DeningerStageForm r (n + 1)}
    (hω : DeningerIsHolomorphicForm ω)
    (hclosed : ∀ z ∈ deningerStageTorus r, extDeriv ω z = 0) :
    ∃ (c : Finset (Fin r) → ℂ) (θ : DeningerStageForm r n),
      DeningerIsHolomorphicForm θ ∧
      ∀ z ∈ deningerStageTorus r,
        ω z = (∑ s : Finset (Fin r), c s • deningerSubsetWedge (n + 1) s z) + extDeriv θ z := by
  obtain ⟨α, θ, hθ, hdecomp⟩ := deningerStage_closed_form_decomposition_hol hω hclosed
  refine ⟨deningerSubsetCoeff α, θ, hθ, fun z hz => ?_⟩
  rw [hdecomp z hz, deningerConstantStageForm_eq_dlog_sum]

end HolomorphicDescent

end RHTower
