import GaloisForLFunctions.RHTower.Deninger.DeningerFormDescent
import GaloisForLFunctions.RHTower.Deninger.DeningerStageKFormExact

/-!
# Exactness on the stage from a periodic primitive

If the primitive of the pulled-back form is periodic in every coordinate, it descends to the stage
and its exterior derivative there is the original form.  Near a point of the stage the descended
form is the pullback of the primitive along a local branch of the logarithm, so its exterior
derivative can be computed by the compatibility of the pullback with the exterior derivative.

* `deningerLogBranch_hasFDerivAt_of_slit` : the derivative of a local branch near its centre.
* `deningerDescendForm_eventuallyEq` : the descended form is locally a pullback along a branch.
* `deningerStage_exact_of_primitive` : a periodic primitive makes the form exact.
-/

namespace RHTower

open Complex Filter Topology

section BranchDerivative

variable {r : ℕ}

/-- **The derivative of a local branch of the logarithm** at any point where the branch is
holomorphic. -/
theorem deningerLogBranch_hasFDerivAt_of_slit {z₀ z : Fin r → ℂ}
    (hz₀ : z₀ ∈ deningerStageTorus r) (hz : z ∈ deningerStageTorus r)
    (hslit : ∀ j, z j / z₀ j ∈ Complex.slitPlane) :
    HasFDerivAt (deningerLogBranch z₀) (deningerLogBranchDeriv z) z := by
  refine hasFDerivAt_pi.2 fun j => ?_
  have hdiv : HasFDerivAt (fun y : Fin r → ℂ => y j / z₀ j)
      ((z₀ j)⁻¹ • (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) j)) z := by
    have hfun : (fun y : Fin r → ℂ => y j / z₀ j) =
        ⇑((z₀ j)⁻¹ • (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) j)) := by
      funext y
      show y j / z₀ j = (z₀ j)⁻¹ * y j
      rw [div_eq_inv_mul]
    rw [hfun]
    exact ((z₀ j)⁻¹ •
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) j)).hasFDerivAt
  have hlog : HasDerivAt Complex.log (z j / z₀ j)⁻¹ (z j / z₀ j) :=
    Complex.hasDerivAt_log (hslit j)
  have hcomp : HasFDerivAt (fun y : Fin r → ℂ => Complex.log (y j / z₀ j))
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) ((z j / z₀ j)⁻¹)).comp
        ((z₀ j)⁻¹ • (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) j))) z :=
    HasFDerivAt.comp (g := Complex.log) z (hlog.hasFDerivAt) hdiv
  have hfinal : HasFDerivAt (fun y : Fin r → ℂ => Complex.log (y j / z₀ j))
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) j).comp
        (deningerLogBranchDeriv z)) z := by
    refine hcomp.congr_fderiv ?_
    refine ContinuousLinearMap.ext fun u => ?_
    show ((z₀ j)⁻¹ * u j) • (z j / z₀ j)⁻¹ = (z j)⁻¹ * u j
    rw [smul_eq_mul, inv_div]
    field_simp [hz₀ j, hz j]
  exact hfinal.const_add _

end BranchDerivative

section ExactDescent

variable {r n : ℕ}

/-- **The descended form is locally the pullback of the primitive along a branch of the
logarithm.** -/
theorem deningerDescendForm_eventuallyEq {η : (Fin r → ℂ) → (Fin r → ℂ) [⋀^Fin n]→L[ℂ] ℂ}
    (hper : ∀ (j : Fin r) (w : Fin r → ℂ),
      η (w + (2 * Real.pi * Complex.I) • (Pi.single j (1 : ℂ) : Fin r → ℂ)) = η w)
    {z₀ : Fin r → ℂ} (hz₀ : z₀ ∈ deningerStageTorus r) :
    deningerDescendForm η =ᶠ[𝓝 z₀] deningerPullbackForm (deningerLogBranch z₀) η := by
  have hone : (1 : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    norm_num
  have hslitev : ∀ᶠ z in 𝓝 z₀, ∀ j : Fin r, z j / z₀ j ∈ Complex.slitPlane := by
    refine eventually_all.2 fun j => ?_
    have hcont : ContinuousAt (fun z : Fin r → ℂ => z j / z₀ j) z₀ :=
      ((continuous_apply j).continuousAt).div_const _
    refine hcont (Complex.isOpen_slitPlane.mem_nhds ?_)
    show z₀ j / z₀ j ∈ Complex.slitPlane
    rw [div_self (hz₀ j)]
    exact hone
  have htorus : ∀ᶠ z in 𝓝 z₀, z ∈ deningerStageTorus r :=
    (deningerStageTorus_isOpen r).mem_nhds hz₀
  filter_upwards [hslitev, htorus] with z hslit hz
  have hval : η (fun j => Complex.log (z j)) = η (deningerLogBranch z₀ z) := by
    refine deningerPeriodicDescent hper ?_
    have h1 : deningerExpMap r (fun j => Complex.log (z j)) = z := by
      funext j
      exact Complex.exp_log (hz j)
    have h2 : deningerExpMap r (deningerLogBranch z₀ z) = z :=
      deningerLogBranch_exp hz₀ hz
    rw [h1, h2]
  show (η (fun j => Complex.log (z j))).compContinuousLinearMap (deningerLogBranchDeriv z) =
    (η (deningerLogBranch z₀ z)).compContinuousLinearMap
      (fderiv ℂ (deningerLogBranch z₀) z)
  rw [hval, (deningerLogBranch_hasFDerivAt_of_slit hz₀ hz hslit).fderiv]

/-- **A periodic primitive of the pulled-back form makes the form exact on the stage.**  Near a
point of the stage the descended primitive is the pullback of the primitive along a branch of the
logarithm, so its exterior derivative is computed by the compatibility of the pullback with the
exterior derivative. -/
theorem deningerStage_exact_of_primitive {ω : DeningerStageForm r (n + 1)}
    {η : (Fin r → ℂ) → (Fin r → ℂ) [⋀^Fin n]→L[ℂ] ℂ} (hdiff : Differentiable ℂ η)
    (hper : ∀ (j : Fin r) (w : Fin r → ℂ),
      η (w + (2 * Real.pi * Complex.I) • (Pi.single j (1 : ℂ) : Fin r → ℂ)) = η w)
    (hprim : ∀ w : Fin r → ℂ, extDeriv η w = deningerExpPullbackForm ω w)
    {z₀ : Fin r → ℂ} (hz₀ : z₀ ∈ deningerStageTorus r) :
    extDeriv (deningerDescendForm η) z₀ = ω z₀ := by
  have hbranchdiff : ContDiffAt ℂ ⊤ (deningerLogBranch z₀) z₀ := by
    have hana : AnalyticAt ℂ (deningerLogBranch z₀) z₀ := by
      refine AnalyticAt.pi fun j => ?_
      have hone : (1 : ℂ) ∈ Complex.slitPlane := by
        rw [Complex.mem_slitPlane_iff]
        left
        norm_num
      have hdivana : AnalyticAt ℂ (fun y : Fin r → ℂ => y j / z₀ j) z₀ := by
        have hfun : (fun y : Fin r → ℂ => y j / z₀ j) =
            ⇑((z₀ j)⁻¹ • (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) j)) := by
          funext y
          show y j / z₀ j = (z₀ j)⁻¹ * y j
          rw [div_eq_inv_mul]
        rw [hfun]
        exact ((z₀ j)⁻¹ •
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) j)).analyticAt z₀
      have hlogana : AnalyticAt ℂ Complex.log ((fun y : Fin r → ℂ => y j / z₀ j) z₀) := by
        show AnalyticAt ℂ Complex.log (z₀ j / z₀ j)
        have hdiffOn : DifferentiableOn ℂ Complex.log Complex.slitPlane :=
          fun x hx => (Complex.differentiableAt_log hx).differentiableWithinAt
        have hana := hdiffOn.analyticOnNhd Complex.isOpen_slitPlane
        rw [div_self (hz₀ j)]
        exact hana 1 hone
      have hcomp : AnalyticAt ℂ (fun y : Fin r → ℂ => Complex.log (y j / z₀ j)) z₀ :=
        AnalyticAt.comp (f := fun y : Fin r → ℂ => y j / z₀ j) hlogana hdivana
      exact AnalyticAt.add analyticAt_const hcomp
    exact hana.contDiffAt
  rw [(deningerDescendForm_eventuallyEq hper hz₀).extDeriv_eq]
  rw [deningerPullbackForm_extDeriv (hdiff (deningerLogBranch z₀ z₀)) hbranchdiff]
  have hexp : deningerExpMap r (deningerLogBranch z₀ z₀) = z₀ :=
    deningerLogBranch_exp hz₀ hz₀
  have hd : extDeriv η (deningerLogBranch z₀ z₀) =
      deningerExpPullbackForm ω (deningerLogBranch z₀ z₀) :=
    hprim _
  show (extDeriv η (deningerLogBranch z₀ z₀)).compContinuousLinearMap
    (fderiv ℂ (deningerLogBranch z₀) z₀) = ω z₀
  rw [hd]
  show ((ω (deningerExpMap r (deningerLogBranch z₀ z₀))).compContinuousLinearMap
      (fderiv ℂ (deningerExpMap r) (deningerLogBranch z₀ z₀))).compContinuousLinearMap
        (fderiv ℂ (deningerLogBranch z₀) z₀) = ω z₀
  rw [hexp, (deningerExpMap_hasFDerivAt (deningerLogBranch z₀ z₀)).fderiv,
    (deningerLogBranch_hasFDerivAt hz₀).fderiv]
  ext v
  have hcancel : ∀ u : Fin r → ℂ,
      (deningerExpDeriv (deningerLogBranch z₀ z₀)) (deningerLogBranchDeriv z₀ u) = u := by
    intro u
    have h := deningerExpDeriv_logBranchDeriv (deningerLogBranch z₀ z₀)
    rw [hexp] at h
    exact congrArg (fun L : (Fin r → ℂ) →L[ℂ] (Fin r → ℂ) => L u) h
  show (ω z₀) (fun i => (deningerExpDeriv (deningerLogBranch z₀ z₀))
    (deningerLogBranchDeriv z₀ (v i))) = (ω z₀) v
  simp only [hcancel]

/-- **A periodic primitive makes the closed form exact on the stage**, applied to the primitive
produced by the Poincaré lemma on the covering space. -/
theorem deningerStage_exact_of_periodic_primitive {ω : DeningerStageForm r (n + 1)}
    (hω : DeningerIsHolomorphicForm ω)
    (hclosed : ∀ z ∈ deningerStageTorus r, extDeriv ω z = 0)
    (hper : ∀ (j : Fin r) (w : Fin r → ℂ),
      deningerHomotopyOperator (deningerExpPullbackForm ω)
          (w + (2 * Real.pi * Complex.I) • (Pi.single j (1 : ℂ) : Fin r → ℂ)) =
        deningerHomotopyOperator (deningerExpPullbackForm ω) w)
    {z₀ : Fin r → ℂ} (hz₀ : z₀ ∈ deningerStageTorus r) :
    extDeriv (deningerDescendForm (deningerHomotopyOperator (deningerExpPullbackForm ω))) z₀ =
      ω z₀ :=
  deningerStage_exact_of_primitive
    (deningerHomotopyOperator_differentiable (deningerExpPullbackForm_differentiable hω)
      (deningerExpPullbackForm_fderiv_continuous hω))
    hper (deningerStage_closed_form_exact_upstairs hω hclosed) hz₀

end ExactDescent

end RHTower
