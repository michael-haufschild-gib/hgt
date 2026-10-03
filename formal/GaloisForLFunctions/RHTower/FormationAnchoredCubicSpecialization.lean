import GaloisForLFunctions.RHTower.RectangleBoundaryPhaseHomotopy
import GaloisForLFunctions.RHTower.GaussianFormationAnchorContinuity
import GaloisForLFunctions.RHTower.FormationAnchoredCubicContourCharge
import GaloisForLFunctions.RHTower.FormationAnchoredCubicRelativeIndex
import GaloisForLFunctions.RHTower.XiGuinandWeilRectangleExhaustion
import GaloisForLFunctions.RHTower.XiRelativeResolventTrace
import GaloisForLFunctions.RHTower.XiRelativeResolventFlux
import GaloisForLFunctions.RHTower.CircleSzegoCommutatorKernel
import GaloisForLFunctions.RHTower.GaussianFormationPrimeFactorization

/-!
# The formation-anchored cubic homotopy defect of a strict-right rectangle

Fix a rectangle `D` compactly inside the strip `1/2 < Re s < 1`, written in the centered
coordinate `s = 1/2 + z i` (so `-1/2 < Im z < 0`), with the completed Xi function nonvanishing on
its boundary.  Along the boundary loop `γ` take the normalized phases

* `u_{D,0}` of the completed function `XiC(z) = ξ(1/2 + z i)`;
* `u_{D,x}` of the zero-free Gaussian Euler–continuum formation `Φₓ(1/2 + z i)`, `x > 0`,

with polarizations `R_{D,x} = M_{u_{D,x}}† P M_{u_{D,x}}`.  The formation-anchored defect is
`T_D = (R_{D,0} - R_{D,1})³`.  It is self-adjoint and trace class, and

`Tr T_D = wind(u_{D,0}) - wind(u_{D,1}) = wind(u_{D,0})
        = (2πi)⁻¹ ∮_{∂D} continuedPrimeArchSourceRelativeTrace = #(enclosed Xi zero copies)`.

Every anchor `x > 0` gives the same trace, `Tr (R_{D,x} - R_{D,y})³ = 0`, and `x ↦ T_{D,x}` is
continuous in trace norm on `(0, ∞)`: a trace-class homotopy through `T_D = T_{D,1}`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology ContinuousLinearMap
open scoped Real

namespace RHTower

theorem rectangleBoundaryPath_on_boundary (z₁ z₂ : ℂ) (t : ℝ) :
    (rectangleBoundaryPath z₁ z₂ t).re = z₁.re ∨ (rectangleBoundaryPath z₁ z₂ t).re = z₂.re ∨
      (rectangleBoundaryPath z₁ z₂ t).im = z₁.im ∨ (rectangleBoundaryPath z₁ z₂ t).im = z₂.im := by
  unfold rectangleBoundaryPath rectangleEdgePath
  split_ifs <;> simp

/-- Gaussian formation in the centered coordinate. -/
def gaussianFormationCentered (x : ℝ) (z : ℂ) : ℂ :=
  gaussianEulerContinuumFormation x (1 / 2 + z * I)

theorem re_half_add_mul_I (z : ℂ) : (1 / 2 + z * I).re = 1 / 2 - z.im := by
  simp [Complex.mul_re]
  ring

/-- The centered half-plane `Im z < 1/2`, i.e. `Re s > 0`. -/
def centeredRightHalfPlane : Set ℂ := {z | z.im < 1 / 2}

theorem isOpen_centeredRightHalfPlane : IsOpen centeredRightHalfPlane :=
  isOpen_lt Complex.continuous_im continuous_const

theorem differentiableAt_gaussianFormationCentered {x : ℝ} (hx : 0 < x) {z : ℂ}
    (hz : z ∈ centeredRightHalfPlane) :
    DifferentiableAt ℂ (gaussianFormationCentered x) z := by
  have hs : 0 < (1 / 2 + z * I).re := by
    rw [re_half_add_mul_I]; have : z.im < 1 / 2 := hz; linarith
  exact (differentiableAt_gaussianEulerContinuumFormation hx hs).comp z
    ((differentiableAt_const _).add (differentiableAt_id.mul_const I))

theorem gaussianFormationCentered_ne_zero (x : ℝ) {z : ℂ} (hz : z ∈ centeredRightHalfPlane) :
    gaussianFormationCentered x z ≠ 0 := by
  have hs : 0 < (1 / 2 + z * I).re := by
    rw [re_half_add_mul_I]; have : z.im < 1 / 2 := hz; linarith
  exact gaussianEulerContinuumFormation_ne_zero x hs

theorem logDeriv_gaussianFormationCentered {x : ℝ} (hx : 0 < x) {z : ℂ}
    (hz : z ∈ centeredRightHalfPlane) :
    logDeriv (gaussianFormationCentered x) z =
      logDeriv (gaussianEulerContinuumFormation x) (1 / 2 + z * I) * I := by
  have hs : 0 < (1 / 2 + z * I).re := by
    rw [re_half_add_mul_I]; have : z.im < 1 / 2 := hz; linarith
  have hg : DifferentiableAt ℂ (fun w : ℂ => 1 / 2 + w * I) z :=
    (differentiableAt_const _).add (differentiableAt_id.mul_const I)
  have h := logDeriv_comp (f := gaussianEulerContinuumFormation x)
    (g := fun w : ℂ => 1 / 2 + w * I) (x := z)
    (differentiableAt_gaussianEulerContinuumFormation hx hs) hg
  have hd : deriv (fun w : ℂ => 1 / 2 + w * I) z = I := by
    have : HasDerivAt (fun w : ℂ => 1 / 2 + w * I) I z := by
      simpa using ((hasDerivAt_id z).mul_const I).const_add (1 / 2 : ℂ)
    exact this.deriv
  rw [hd] at h
  exact h

/-- A rectangle compactly inside the strip `1/2 < Re s < 1` (centered: `-1/2 < Im z < 0`) whose
boundary avoids the zeros of the completed Xi function. -/
structure FormationRectangle where
  z₁ : ℂ
  z₂ : ℂ
  re_lt : z₁.re < z₂.re
  im_lt : z₁.im < z₂.im
  im_lower : -(1 / 2) < z₁.im
  im_upper : z₂.im < 0
  xi_ne_zero : ∀ z ∈ (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im),
    (z.re = z₁.re ∨ z.re = z₂.re ∨ z.im = z₁.im ∨ z.im = z₂.im) → XiC z ≠ 0

namespace FormationRectangle

variable (R : FormationRectangle)

theorem path_mem (t : ℝ) :
    rectangleBoundaryPath R.z₁ R.z₂ t ∈ (uIcc R.z₁.re R.z₂.re ×ℂ uIcc R.z₁.im R.z₂.im) :=
  rectangleBoundaryPath_mem_reProdIm R.z₁ R.z₂ R.re_lt.le R.im_lt.le t

theorem path_im_lt (t : ℝ) : (rectangleBoundaryPath R.z₁ R.z₂ t).im < 1 / 2 := by
  have h := (Complex.mem_reProdIm.1 (R.path_mem t)).2
  rw [uIcc_of_le R.im_lt.le] at h
  linarith [h.2, R.im_upper]

theorem rect_subset :
    (uIcc R.z₁.re R.z₂.re ×ℂ uIcc R.z₁.im R.z₂.im) ⊆ centeredRightHalfPlane := by
  intro z hz
  have h := (Complex.mem_reProdIm.1 hz).2
  rw [uIcc_of_le R.im_lt.le] at h
  change z.im < 1 / 2
  linarith [h.2, R.im_upper]

/-- The completed endpoint: boundary data of `XiC`. -/
def completedDatum : RectangleArgumentDatum where
  F := XiC
  z₁ := R.z₁
  z₂ := R.z₂
  U := univ
  isOpen := isOpen_univ
  differentiableOn := XiC_differentiable.differentiableOn
  path_mem _ := mem_univ _
  ne_zero t := R.xi_ne_zero _ (R.path_mem t) (rectangleBoundaryPath_on_boundary R.z₁ R.z₂ t)

/-- The Gaussian endpoint at anchor `x > 0`. -/
def gaussianDatum (x : Ioi (0 : ℝ)) : RectangleArgumentDatum where
  F := gaussianFormationCentered x.1
  z₁ := R.z₁
  z₂ := R.z₂
  U := centeredRightHalfPlane
  isOpen := isOpen_centeredRightHalfPlane
  differentiableOn _ hz :=
    (differentiableAt_gaussianFormationCentered x.2 hz).differentiableWithinAt
  path_mem t := R.path_im_lt t
  ne_zero t := gaussianFormationCentered_ne_zero x.1 (R.path_im_lt t)

/-- Completed boundary phase `u_{D,0}`. -/
abbrev completedPhase : PiecewiseSmoothCirclePhase := R.completedDatum.toPhase

/-- Gaussian boundary phase `u_{D,x}`. -/
abbrev gaussianPhase (x : Ioi (0 : ℝ)) : PiecewiseSmoothCirclePhase := (R.gaussianDatum x).toPhase

/-- The anchor `x = 1`. -/
def unitAnchor : Ioi (0 : ℝ) := ⟨1, Set.mem_Ioi.2 one_pos⟩

/-- Anchored cubic defect `T_{D,x} = (R_{D,0} - R_{D,x})³`. -/
def anchoredCubicDefect (x : Ioi (0 : ℝ)) : CCMCircleL2 →L[ℂ] CCMCircleL2 :=
  restrictedProjectionCubicDefect R.completedPhase.polarization (R.gaussianPhase x).polarization

/-- The formation-anchored cubic homotopy defect `T_D = (R_{D,0} - R_{D,1})³`. -/
def formationCubicDefect : CCMCircleL2 →L[ℂ] CCMCircleL2 := R.anchoredCubicDefect unitAnchor

/-! ## Operator structure -/

theorem anchoredDisplacement_isHilbertSchmidt (x : Ioi (0 : ℝ)) :
    (restrictedProjectionDisplacement R.completedPhase.polarization
      (R.gaussianPhase x).polarization).IsHilbertSchmidt :=
  (R.gaussianPhase x).polarization_displacement_isHilbertSchmidt R.completedPhase

theorem anchoredCubicDefect_memSchattenClass_one (x : Ioi (0 : ℝ)) :
    MemSchattenClass 1 (R.anchoredCubicDefect x) :=
  restrictedProjectionCubicDefect_memSchattenClass_one _ _ (R.anchoredDisplacement_isHilbertSchmidt x)

theorem adjoint_anchoredCubicDefect (x : Ioi (0 : ℝ)) :
    ContinuousLinearMap.adjoint (R.anchoredCubicDefect x) = R.anchoredCubicDefect x :=
  adjoint_restrictedProjectionCubicDefect _ _
    R.completedPhase.toHankelPhase.datum.conjugateProjection_adjoint
    (R.gaussianPhase x).toHankelPhase.datum.conjugateProjection_adjoint

/-- Exact two-channel identity `T = R₀(1 - Rₓ)R₀ - Rₓ(1 - R₀)Rₓ`. -/
theorem anchoredCubicDefect_eq_channels (x : Ioi (0 : ℝ)) :
    R.anchoredCubicDefect x =
      restrictedProjectionPositiveChannel R.completedPhase.polarization
          (R.gaussianPhase x).polarization -
        restrictedProjectionPositiveChannel (R.gaussianPhase x).polarization
          R.completedPhase.polarization :=
  restrictedProjectionCubicDefect_eq_channels _ _
    R.completedPhase.toHankelPhase.datum.conjugateProjection_idempotent
    (R.gaussianPhase x).toHankelPhase.datum.conjugateProjection_idempotent

/-! ## Windings of the two endpoints -/

/-- Every Gaussian boundary phase has zero winding. -/
theorem windingNumber_gaussianPhase (x : Ioi (0 : ℝ)) : (R.gaussianPhase x).windingNumber = 0 := by
  have hdiff : DifferentiableOn ℂ (gaussianFormationCentered x.1) centeredRightHalfPlane :=
    fun _ hz => (differentiableAt_gaussianFormationCentered x.2 hz).differentiableWithinAt
  have hzero : opTrace (restrictedProjectionCubicDefect (R.gaussianPhase x).polarization
      ccmCircleHardyProjection) = 0 :=
    (R.gaussianDatum x).opTrace_cubicDefect_eq_zero_of_zeroFree R.rect_subset
      (hdiff.analyticOnNhd isOpen_centeredRightHalfPlane)
      (fun _ hz => gaussianFormationCentered_ne_zero x.1 hz)
  rw [← (R.gaussianPhase x).opTrace_cubicDefect]
  exact hzero

/-- Every edge point of the rectangle is Xi-explicit-admissible. -/
theorem admissible_of_boundary {z : ℂ}
    (hz : z ∈ (uIcc R.z₁.re R.z₂.re ×ℂ uIcc R.z₁.im R.z₂.im))
    (hb : z.re = R.z₁.re ∨ z.re = R.z₂.re ∨ z.im = R.z₁.im ∨ z.im = R.z₂.im) :
    XiExplicitAdmissible z := by
  have h := (Complex.mem_reProdIm.1 hz).2
  rw [uIcc_of_le R.im_lt.le] at h
  refine XiExplicitAdmissible_of_im_lt_half_of_ne_one_of_XiC_ne_zero
    (by linarith [h.2, R.im_upper]) ?_ (R.xi_ne_zero z hz hb)
  intro h1
  have := congrArg Complex.re h1
  rw [re_half_add_mul_I, Complex.one_re] at this
  linarith [h.1, R.im_lower]

private theorem bot_mem {r : ℝ} (hr : r ∈ uIcc R.z₁.re R.z₂.re) :
    ((r : ℂ) + R.z₁.im * I) ∈ (uIcc R.z₁.re R.z₂.re ×ℂ uIcc R.z₁.im R.z₂.im) ∧
      (((r : ℂ) + R.z₁.im * I).re = R.z₁.re ∨ ((r : ℂ) + R.z₁.im * I).re = R.z₂.re ∨
        ((r : ℂ) + R.z₁.im * I).im = R.z₁.im ∨ ((r : ℂ) + R.z₁.im * I).im = R.z₂.im) := by
  refine ⟨Complex.mem_reProdIm.2 ⟨by simpa using hr, by simp⟩, Or.inr (Or.inr (Or.inl ?_))⟩
  simp

private theorem top_mem {r : ℝ} (hr : r ∈ uIcc R.z₁.re R.z₂.re) :
    ((r : ℂ) + R.z₂.im * I) ∈ (uIcc R.z₁.re R.z₂.re ×ℂ uIcc R.z₁.im R.z₂.im) ∧
      (((r : ℂ) + R.z₂.im * I).re = R.z₁.re ∨ ((r : ℂ) + R.z₂.im * I).re = R.z₂.re ∨
        ((r : ℂ) + R.z₂.im * I).im = R.z₁.im ∨ ((r : ℂ) + R.z₂.im * I).im = R.z₂.im) := by
  refine ⟨Complex.mem_reProdIm.2 ⟨by simpa using hr, by simp⟩, Or.inr (Or.inr (Or.inr ?_))⟩
  simp

private theorem right_mem {y : ℝ} (hy : y ∈ uIcc R.z₁.im R.z₂.im) :
    ((R.z₂.re : ℂ) + y * I) ∈ (uIcc R.z₁.re R.z₂.re ×ℂ uIcc R.z₁.im R.z₂.im) ∧
      (((R.z₂.re : ℂ) + y * I).re = R.z₁.re ∨ ((R.z₂.re : ℂ) + y * I).re = R.z₂.re ∨
        ((R.z₂.re : ℂ) + y * I).im = R.z₁.im ∨ ((R.z₂.re : ℂ) + y * I).im = R.z₂.im) := by
  refine ⟨Complex.mem_reProdIm.2 ⟨by simp, by simpa using hy⟩, Or.inr (Or.inl ?_)⟩
  simp

private theorem left_mem {y : ℝ} (hy : y ∈ uIcc R.z₁.im R.z₂.im) :
    ((R.z₁.re : ℂ) + y * I) ∈ (uIcc R.z₁.re R.z₂.re ×ℂ uIcc R.z₁.im R.z₂.im) ∧
      (((R.z₁.re : ℂ) + y * I).re = R.z₁.re ∨ ((R.z₁.re : ℂ) + y * I).re = R.z₂.re ∨
        ((R.z₁.re : ℂ) + y * I).im = R.z₁.im ∨ ((R.z₁.re : ℂ) + y * I).im = R.z₂.im) := by
  refine ⟨Complex.mem_reProdIm.2 ⟨by simp, by simpa using hy⟩, Or.inl ?_⟩
  simp

/-- On the boundary the completed logarithmic current is the continued prime--Gamma source
trace. -/
theorem rectIntegral_logDeriv_XiC_eq_source :
    rectIntegral (logDeriv XiC) R.z₁ R.z₂ =
      rectIntegral continuedPrimeArchSourceRelativeTrace R.z₁ R.z₂ := by
  let S : Set ℂ := {z | z ∈ (uIcc R.z₁.re R.z₂.re ×ℂ uIcc R.z₁.im R.z₂.im) ∧
    (z.re = R.z₁.re ∨ z.re = R.z₂.re ∨ z.im = R.z₁.im ∨ z.im = R.z₂.im)}
  refine rectIntegral_congr (S := S) (fun z hz => ?_) (fun _ hr => R.bot_mem hr)
    (fun _ hr => R.top_mem hr) (fun _ hy => R.right_mem hy) (fun _ hy => R.left_mem hy)
  have ha := R.admissible_of_boundary hz.1 hz.2
  rw [logDeriv_XiC_eq_relativeResolventTrace (XiC_ne_zero_of_admissible ha),
    continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace ha.re_pos ha.ne_one
      ha.zeta_ne]

/-- The completed boundary phase winds once around each enclosed Xi zero copy. -/
theorem windingNumber_completedPhase :
    R.completedPhase.windingNumber = formationCompletedRectangleWinding R.z₁ R.z₂ := by
  rw [R.completedDatum.windingNumber_toPhase, formationCompletedRectangleWinding]
  change (2 * π * I)⁻¹ * rectIntegral (logDeriv XiC) R.z₁ R.z₂ = _
  rw [R.rectIntegral_logDeriv_XiC_eq_source]

theorem formationCompletedRectangleWinding_eq_card :
    formationCompletedRectangleWinding R.z₁ R.z₂ =
      ((xiZeroCopyClosedRectangle R.z₁ R.z₂).card : ℂ) :=
  formationCompletedRectangleWinding_eq_xiMultiplicityCopies R.re_lt R.im_lt
    (fun _ hr => R.admissible_of_boundary (R.bot_mem hr).1 (R.bot_mem hr).2)
    (fun _ hr => R.admissible_of_boundary (R.top_mem hr).1 (R.top_mem hr).2)
    (fun _ hy => R.admissible_of_boundary (R.right_mem hy).1 (R.right_mem hy).2)
    (fun _ hy => R.admissible_of_boundary (R.left_mem hy).1 (R.left_mem hy).2)

/-! ## The integral trace -/

/-- **FACHD-B, trace chain.**  For every anchor `x > 0`,
`Tr (R_{D,0} - R_{D,x})³ = wind(u_{D,0}) - wind(u_{D,x}) = wind(u_{D,0})`. -/
theorem opTrace_anchoredCubicDefect (x : Ioi (0 : ℝ)) :
    opTrace (R.anchoredCubicDefect x) =
      R.completedPhase.windingNumber - (R.gaussianPhase x).windingNumber ∧
    opTrace (R.anchoredCubicDefect x) = R.completedPhase.windingNumber := by
  have h := R.completedPhase.opTrace_relativeCubicDefect (R.gaussianPhase x)
  unfold anchoredCubicDefect
  refine ⟨h, ?_⟩
  rw [h, R.windingNumber_gaussianPhase, sub_zero]

/-- **FACHD-B.**  `Tr T_D = (2πi)⁻¹ ∮_{∂D} continuedPrimeArchSourceRelativeTrace` is the number
of enclosed Xi zero copies (with multiplicity). -/
theorem opTrace_formationCubicDefect :
    opTrace R.formationCubicDefect = formationCompletedRectangleWinding R.z₁ R.z₂ ∧
    opTrace R.formationCubicDefect = ((xiZeroCopyClosedRectangle R.z₁ R.z₂).card : ℂ) := by
  have h : opTrace R.formationCubicDefect = formationCompletedRectangleWinding R.z₁ R.z₂ := by
    rw [formationCubicDefect, (R.opTrace_anchoredCubicDefect unitAnchor).2,
      R.windingNumber_completedPhase]
  exact ⟨h, h.trans R.formationCompletedRectangleWinding_eq_card⟩

/-- **(FACHD.13)** Any two Gaussian anchors have zero mutual cubic charge. -/
theorem opTrace_gaussianMutualCubicDefect (x y : Ioi (0 : ℝ)) :
    opTrace (restrictedProjectionCubicDefect (R.gaussianPhase x).polarization
      (R.gaussianPhase y).polarization) = 0 := by
  rw [(R.gaussianPhase x).opTrace_relativeCubicDefect (R.gaussianPhase y),
    R.windingNumber_gaussianPhase, R.windingNumber_gaussianPhase, sub_zero]

/-- **(FACHD.14)** Cocycle conservation through the Gaussian endpoint:
`Tr (R_{D,0} - P)³ = Tr T_{D,x} + Tr (R_{D,x} - P)³ = Tr T_{D,x}`. -/
theorem opTrace_completed_eq_anchored (x : Ioi (0 : ℝ)) :
    opTrace (restrictedProjectionCubicDefect R.completedPhase.polarization
        ccmCircleHardyProjection) =
      opTrace (R.anchoredCubicDefect x) +
        opTrace (restrictedProjectionCubicDefect (R.gaussianPhase x).polarization
          ccmCircleHardyProjection) ∧
    opTrace (restrictedProjectionCubicDefect (R.gaussianPhase x).polarization
        ccmCircleHardyProjection) = 0 := by
  have hcoc := opTrace_restrictedProjectionCubicDefect_cocycle R.completedPhase.polarization
    (R.gaussianPhase x).polarization ccmCircleHardyProjection
    R.completedPhase.toHankelPhase.datum.conjugateProjection_idempotent
    (R.gaussianPhase x).toHankelPhase.datum.conjugateProjection_idempotent
    ccmCircleHardyProjection_idempotent (R.anchoredDisplacement_isHilbertSchmidt x)
    (R.gaussianPhase x).toHankelPhase.datum.displacement_isHilbertSchmidt
  refine ⟨hcoc, ?_⟩
  have hg := (R.gaussianPhase x).opTrace_cubicDefect
  change opTrace (restrictedProjectionCubicDefect (R.gaussianPhase x).polarization
    ccmCircleHardyProjection) = _ at hg
  rw [hg, R.windingNumber_gaussianPhase]

/-! ## Anchor homotopy -/

/-- Logarithmic currents of nearby Gaussian anchors are uniformly close on the boundary. -/
theorem gaussian_logDeriv_convergence (x : Ioi (0 : ℝ)) :
    ∀ ε > 0, ∀ᶠ y in 𝓝 x, ∀ t,
      ‖logDeriv (R.gaussianDatum y).F (rectangleBoundaryPath (R.gaussianDatum x).z₁
          (R.gaussianDatum x).z₂ t) -
        logDeriv (R.gaussianDatum x).F (rectangleBoundaryPath (R.gaussianDatum x).z₁
          (R.gaussianDatum x).z₂ t)‖ ≤ ε := by
  intro ε hε
  have h := eventually_norm_logDeriv_gaussianFormation_sub_le x.2 hε
  have hmap : Tendsto (fun y : Ioi (0 : ℝ) => (y : ℝ)) (𝓝 x) (𝓝 (x : ℝ)) :=
    continuous_subtype_val.tendsto x
  filter_upwards [hmap.eventually h] with y hy t
  have hmem : rectangleBoundaryPath R.z₁ R.z₂ t ∈ centeredRightHalfPlane := R.path_im_lt t
  have hs : 0 < (1 / 2 + rectangleBoundaryPath R.z₁ R.z₂ t * I).re := by
    rw [re_half_add_mul_I]; have := R.path_im_lt t; linarith
  change ‖logDeriv (gaussianFormationCentered y.1) (rectangleBoundaryPath R.z₁ R.z₂ t) -
    logDeriv (gaussianFormationCentered x.1) (rectangleBoundaryPath R.z₁ R.z₂ t)‖ ≤ ε
  rw [logDeriv_gaussianFormationCentered y.2 hmem, logDeriv_gaussianFormationCentered x.2 hmem,
    ← sub_mul, norm_mul, Complex.norm_I, mul_one]
  exact hy.2 _ hs

/-- **(FACHD.12) Anchor homotopy.**  `x ↦ T_{D,x}` is continuous in trace norm on `(0, ∞)`. -/
theorem tendsto_traceNorm_anchoredCubicDefect (x : Ioi (0 : ℝ)) :
    Tendsto (fun y => traceNorm CCMCircleL2 (R.anchoredCubicDefect y - R.anchoredCubicDefect x))
      (𝓝 x) (𝓝 0) := by
  obtain ⟨hval, hder⟩ := (R.gaussianDatum x).phase_convergence (fun y => R.gaussianDatum y)
    (fun _ => rfl) (fun _ => rfl) (R.gaussian_logDeriv_convergence x)
  exact (R.gaussianPhase x).tendsto_traceNorm_relativeCubicDefect R.completedPhase
    (fun y => R.gaussianPhase y) hval hder

/-- The anchored defects all have the trace of `T_D`. -/
theorem opTrace_anchoredCubicDefect_eq (x : Ioi (0 : ℝ)) :
    opTrace (R.anchoredCubicDefect x) = opTrace R.formationCubicDefect := by
  rw [formationCubicDefect, (R.opTrace_anchoredCubicDefect x).2,
    (R.opTrace_anchoredCubicDefect unitAnchor).2]

/-! ## The relative phase form `(RUCRI.17)`–`(RUCRI.18)` -/

/-- Relative boundary phase `v_{D,x} = u_{D,0} \overline{u_{D,x}}`. -/
abbrev relativePhase (x : Ioi (0 : ℝ)) : PiecewiseSmoothCirclePhase :=
  R.completedPhase.mulConj (R.gaussianPhase x)

/-- **(RUCRI.18)** The restricted-unitary defect of the relative phase,
`Tr (V† P V - P)³` with `V = M_{v_{D,x}}`, is the enclosed Xi multiplicity. -/
theorem opTrace_relativePhaseCubicDefect (x : Ioi (0 : ℝ)) :
    opTrace (restrictedProjectionCubicDefect (R.relativePhase x).polarization
        ccmCircleHardyProjection) = ((xiZeroCopyClosedRectangle R.z₁ R.z₂).card : ℂ) := by
  have h := (R.relativePhase x).opTrace_cubicDefect
  change opTrace (restrictedProjectionCubicDefect (R.relativePhase x).polarization
    ccmCircleHardyProjection) = _ at h
  rw [h, PiecewiseSmoothCirclePhase.windingNumber_mulConj, R.windingNumber_gaussianPhase, sub_zero,
    R.windingNumber_completedPhase, R.formationCompletedRectangleWinding_eq_card]

end FormationRectangle

/-! ## Relative cubic defects of two restricted unitaries (FACHD-A) -/

namespace RestrictedUnitaryDatum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- For two restricted unitaries sharing one polarization, the relative displacement
`R_U - R_V` is Hilbert–Schmidt. -/
theorem relativeDisplacement_isHilbertSchmidt (D E : RestrictedUnitaryDatum H)
    (h : D.projection = E.projection) :
    (restrictedProjectionDisplacement D.conjugateProjection E.conjugateProjection).IsHilbertSchmidt := by
  have heq : restrictedProjectionDisplacement D.conjugateProjection E.conjugateProjection =
      restrictedProjectionDisplacement D.conjugateProjection D.projection -
        restrictedProjectionDisplacement E.conjugateProjection E.projection := by
    simp only [restrictedProjectionDisplacement, h]
    abel
  rw [heq]
  exact D.displacement_isHilbertSchmidt.sub E.displacement_isHilbertSchmidt

/-- **FACHD-A (1)–(5).**  The relative cubic defect `T(U,V) = (R_U - R_V)³` is self-adjoint and
trace class, splits into its two positive channels, and its trace is the relative index. -/
theorem relativeCubicDefect_laws (D E : RestrictedUnitaryDatum H)
    (h : D.projection = E.projection) :
    ContinuousLinearMap.adjoint (restrictedProjectionDisplacement D.conjugateProjection
        E.conjugateProjection) =
      restrictedProjectionDisplacement D.conjugateProjection E.conjugateProjection ∧
    MemSchattenClass 1 (restrictedProjectionCubicDefect D.conjugateProjection
      E.conjugateProjection) ∧
    ContinuousLinearMap.adjoint (restrictedProjectionCubicDefect D.conjugateProjection
        E.conjugateProjection) =
      restrictedProjectionCubicDefect D.conjugateProjection E.conjugateProjection ∧
    restrictedProjectionCubicDefect D.conjugateProjection E.conjugateProjection =
      restrictedProjectionPositiveChannel D.conjugateProjection E.conjugateProjection -
        restrictedProjectionPositiveChannel E.conjugateProjection D.conjugateProjection ∧
    opTrace (restrictedProjectionCubicDefect D.conjugateProjection E.conjugateProjection) =
      (restrictedProjectionRelativeIndex D.conjugateProjection E.conjugateProjection : ℂ) := by
  have hHS := D.relativeDisplacement_isHilbertSchmidt E h
  exact ⟨adjoint_restrictedProjectionDisplacement _ _ D.conjugateProjection_adjoint
      E.conjugateProjection_adjoint,
    restrictedProjectionCubicDefect_memSchattenClass_one _ _ hHS,
    adjoint_restrictedProjectionCubicDefect _ _ D.conjugateProjection_adjoint
      E.conjugateProjection_adjoint,
    restrictedProjectionCubicDefect_eq_channels _ _ D.conjugateProjection_idempotent
      E.conjugateProjection_idempotent,
    opTrace_formationAnchoredCubicDefect_eq_relativeIndex _ _ D.conjugateProjection_idempotent
      E.conjugateProjection_idempotent D.conjugateProjection_adjoint E.conjugateProjection_adjoint
      hHS⟩

/-- **(FACHD.7)–(FACHD.8)** For three restricted unitaries sharing one polarization the cubic
trace is an exact cocycle, and the operator associator is trace class with zero trace. -/
theorem relativeCubicDefect_cocycle (D E G : RestrictedUnitaryDatum H)
    (hDE : D.projection = E.projection) (hEG : E.projection = G.projection) :
    opTrace (restrictedProjectionCubicDefect D.conjugateProjection G.conjugateProjection) =
      opTrace (restrictedProjectionCubicDefect D.conjugateProjection E.conjugateProjection) +
        opTrace (restrictedProjectionCubicDefect E.conjugateProjection G.conjugateProjection) ∧
    MemSchattenClass 1 (formationAnchoredCubicAssociator D.conjugateProjection
      E.conjugateProjection G.conjugateProjection) ∧
    opTrace (formationAnchoredCubicAssociator D.conjugateProjection E.conjugateProjection
      G.conjugateProjection) = 0 := by
  have h1 := D.relativeDisplacement_isHilbertSchmidt E hDE
  have h2 := E.relativeDisplacement_isHilbertSchmidt G hEG
  exact ⟨opTrace_restrictedProjectionCubicDefect_cocycle _ _ _ D.conjugateProjection_idempotent
      E.conjugateProjection_idempotent G.conjugateProjection_idempotent h1 h2,
    formationAnchoredCubicAssociator_memSchattenClass_one _ _ _ h1 h2,
    opTrace_formationAnchoredCubicAssociator_eq_zero _ _ _ D.conjugateProjection_idempotent
      E.conjugateProjection_idempotent G.conjugateProjection_idempotent h1 h2⟩

end RestrictedUnitaryDatum

/-! ## Kernel form and prime mixing of the anchored defect -/

namespace FormationRectangle

variable (R : FormationRectangle)

/-- **(FACHD.9)–(FACHD.10)** `T_{D,x}` is the nuclear integral operator with threefold cyclic
kernel `d ⋆ d ⋆ d`, `d(z,w) = (\overline{u_{D,0}(z)} u_{D,0}(w) - \overline{u_{D,x}(z)} u_{D,x}(w))
S(z - w)`. -/
theorem anchoredCubicDefect_eq_kernel_op (x : Ioi (0 : ℝ)) :
    (szegoRelativeCubicSqIntKernel R.completedPhase.toHankelPhase
      (R.gaussianPhase x).toHankelPhase).op = R.anchoredCubicDefect x :=
  szegoRelativeCubicSqIntKernel_op _ _

/-- **Prime mixing of the Gaussian endpoint.**  Along the boundary the Gaussian phase is
`(h_∞/|h_∞|) · exp(i Im Aₓ) · exp(i Im Lₓ)` at `s = 1/2 + γ(t) i`, and `exp(i Im Lₓ)` is the product
over all primes of the prime-local phases `exp(i Im ℓ_{x,p})`. -/
theorem gaussianDatum_value_div_norm (x : Ioi (0 : ℝ)) (t : ℝ) :
    (R.gaussianDatum x).value t / (‖(R.gaussianDatum x).value t‖ : ℂ) =
        gaussianArchimedeanHalfFactor (1 / 2 + rectangleBoundaryPath R.z₁ R.z₂ t * I) /
            (‖gaussianArchimedeanHalfFactor (1 / 2 + rectangleBoundaryPath R.z₁ R.z₂ t * I)‖ : ℂ) *
          Complex.exp (I * ((gaussianContinuumPrimitive x.1
            (1 / 2 + rectangleBoundaryPath R.z₁ R.z₂ t * I)).im : ℂ)) *
          Complex.exp (I * ((gaussianEulerLog x.1
            (1 / 2 + rectangleBoundaryPath R.z₁ R.z₂ t * I)).im : ℂ)) ∧
      HasProd (fun p : Nat.Primes => Complex.exp (I * ((gaussianPrimeLocalLog x.1 p
          (1 / 2 + rectangleBoundaryPath R.z₁ R.z₂ t * I)).im : ℂ)))
        (Complex.exp (I * ((gaussianEulerLog x.1
          (1 / 2 + rectangleBoundaryPath R.z₁ R.z₂ t * I)).im : ℂ))) := by
  have hs : 0 < (1 / 2 + rectangleBoundaryPath R.z₁ R.z₂ t * I).re := by
    rw [re_half_add_mul_I]; have := R.path_im_lt t; linarith
  exact ⟨gaussianEulerContinuumFormation_div_norm x.1 hs,
    hasProd_exp_im_gaussianPrimeLocalLog x.2 _⟩

end FormationRectangle

end RHTower
