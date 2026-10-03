import GaloisForLFunctions.RHTower.RectangleBoundaryPath
import GaloisForLFunctions.RHTower.PiecewiseSmoothCirclePhaseHomotopy

/-!
# Boundary phase of an analytic function on a rectangle

Let `F` be holomorphic on an open set containing the boundary of a rectangle and nonvanishing on
it.  Along the periodic boundary loop `γ`, the normalized phase

`u(t) = (F(γ t) / |F(γ t)|) · (F(γ 0) / |F(γ 0)|)⁻¹`

is a piecewise smooth circle phase, with `u' = u · i Im((F'/F)(γ) γ')` off the corner times.  The
real part `Re((F'/F)(γ) γ')` is the derivative of `log |F(γ)|`, so it integrates to zero over a
period, and the winding number of `u` is the normalized contour integral

`wind(u) = (2πi)⁻¹ ∮_{∂R} F'/F = (2πi)⁻¹ rectIntegral (logDeriv F) z₁ z₂`.

Hence `Tr (M_u† P M_u - P)³` is this contour integral; it vanishes when `F` is holomorphic and
zero-free on a neighbourhood of the closed rectangle.
-/

noncomputable section

open Complex MeasureTheory intervalIntegral Set Filter Topology ContinuousLinearMap
open scoped Real

namespace RHTower

theorem rectangleBoundaryPath_mem_reProdIm (z₁ z₂ : ℂ) (hre : z₁.re ≤ z₂.re)
    (him : z₁.im ≤ z₂.im) (t : ℝ) :
    rectangleBoundaryPath z₁ z₂ t ∈ (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) := by
  have h0 := Int.fract_nonneg t
  have h1 := Int.fract_lt_one t
  have hx : 0 ≤ z₂.re - z₁.re := sub_nonneg.2 hre
  have hy : 0 ≤ z₂.im - z₁.im := sub_nonneg.2 him
  rw [uIcc_of_le hre, uIcc_of_le him, Complex.mem_reProdIm]
  unfold rectangleBoundaryPath rectangleEdgePath
  set τ := Int.fract t
  split_ifs with ha hb hc
  · have e1 : 0 ≤ 4 * τ := by linarith
    have e2 : 4 * τ ≤ 1 := by linarith
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp <;>
      nlinarith [mul_nonneg e1 hx, mul_nonneg (sub_nonneg.2 e2) hx]
  · have e1 : 0 ≤ 4 * τ - 1 := by linarith
    have e2 : 4 * τ - 1 ≤ 1 := by linarith
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp <;>
      nlinarith [mul_nonneg e1 hy, mul_nonneg (sub_nonneg.2 e2) hy]
  · have e1 : 0 ≤ 4 * τ - 2 := by linarith
    have e2 : 4 * τ - 2 ≤ 1 := by linarith
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp <;>
      nlinarith [mul_nonneg e1 hx, mul_nonneg (sub_nonneg.2 e2) hx]
  · have e1 : 0 ≤ 4 * τ - 3 := by linarith
    have e2 : 4 * τ - 3 ≤ 1 := by linarith
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp <;>
      nlinarith [mul_nonneg e1 hy, mul_nonneg (sub_nonneg.2 e2) hy]

/-- A holomorphic function on an open neighbourhood of a rectangle boundary, nonvanishing there. -/
structure RectangleArgumentDatum where
  F : ℂ → ℂ
  z₁ : ℂ
  z₂ : ℂ
  U : Set ℂ
  isOpen : IsOpen U
  differentiableOn : DifferentiableOn ℂ F U
  path_mem : ∀ t, rectangleBoundaryPath z₁ z₂ t ∈ U
  ne_zero : ∀ t, F (rectangleBoundaryPath z₁ z₂ t) ≠ 0

namespace RectangleArgumentDatum

variable (D : RectangleArgumentDatum)

/-- Boundary values `F ∘ γ`. -/
def value (t : ℝ) : ℂ := D.F (rectangleBoundaryPath D.z₁ D.z₂ t)

/-- Logarithmic velocity `(F'/F)(γ t) γ'(t)`. -/
def logVelocity (t : ℝ) : ℂ :=
  logDeriv D.F (rectangleBoundaryPath D.z₁ D.z₂ t) * rectangleBoundaryVelocity D.z₁ D.z₂ t

/-- Base point phase `F(γ 0)/|F(γ 0)|`. -/
def basePhase : ℂ := D.value 0 / (‖D.value 0‖ : ℂ)

/-- The normalized boundary phase. -/
def phase (t : ℝ) : ℂ := D.value t / (‖D.value t‖ : ℂ) * D.basePhase⁻¹

/-- Its derivative off the corners. -/
def phaseDeriv (t : ℝ) : ℂ := D.phase t * (I * ((D.logVelocity t).im : ℂ))

theorem value_ne_zero (t : ℝ) : D.value t ≠ 0 := D.ne_zero t

theorem norm_value_pos (t : ℝ) : 0 < ‖D.value t‖ := norm_pos_iff.2 (D.value_ne_zero t)

theorem continuous_value : Continuous D.value :=
  D.differentiableOn.continuousOn.comp_continuous (continuous_rectangleBoundaryPath _ _)
    D.path_mem

theorem continuous_logDeriv_comp :
    Continuous fun t => logDeriv D.F (rectangleBoundaryPath D.z₁ D.z₂ t) := by
  have hderiv : ContinuousOn (deriv D.F) D.U :=
    (D.differentiableOn.deriv D.isOpen).continuousOn
  have h1 : Continuous fun t => deriv D.F (rectangleBoundaryPath D.z₁ D.z₂ t) :=
    hderiv.comp_continuous (continuous_rectangleBoundaryPath _ _) D.path_mem
  exact h1.div D.continuous_value D.value_ne_zero

theorem norm_basePhase : ‖D.basePhase‖ = 1 := by
  rw [basePhase, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm,
    div_self (D.norm_value_pos 0).ne']

theorem norm_phase (t : ℝ) : ‖D.phase t‖ = 1 := by
  rw [phase, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm,
    div_self (D.norm_value_pos t).ne', norm_inv, D.norm_basePhase, inv_one, one_mul]

theorem continuous_phase : Continuous D.phase := by
  refine (D.continuous_value.div (continuous_ofReal.comp D.continuous_value.norm) ?_).mul
    continuous_const
  intro t; exact ofReal_ne_zero.2 (D.norm_value_pos t).ne'

theorem periodic_value : Function.Periodic D.value 1 := fun t => by
  simp only [value, periodic_rectangleBoundaryPath D.z₁ D.z₂ t]

theorem periodic_phase : Function.Periodic D.phase 1 := fun t => by
  simp only [phase, D.periodic_value t]

theorem periodic_logVelocity : Function.Periodic D.logVelocity 1 := fun t => by
  simp only [logVelocity, periodic_rectangleBoundaryPath D.z₁ D.z₂ t,
    periodic_rectangleBoundaryVelocity D.z₁ D.z₂ t]

theorem hasDerivAt_value {t : ℝ} (ht : t ∉ rectangleCornerTimes) :
    HasDerivAt D.value (D.value t * D.logVelocity t) t := by
  have hF : HasDerivAt D.F (deriv D.F (rectangleBoundaryPath D.z₁ D.z₂ t))
      (rectangleBoundaryPath D.z₁ D.z₂ t) :=
    (D.differentiableOn.differentiableAt (D.isOpen.mem_nhds (D.path_mem t))).hasDerivAt
  have h := hF.comp t (hasDerivAt_rectangleBoundaryPath D.z₁ D.z₂ ht)
  have hv := D.ne_zero t
  have heq : deriv D.F (rectangleBoundaryPath D.z₁ D.z₂ t) *
      rectangleBoundaryVelocity D.z₁ D.z₂ t = D.value t * D.logVelocity t := by
    simp only [logVelocity, logDeriv_apply, value]
    field_simp
  rw [heq] at h
  exact h

/-- Off the corners the modulus has logarithmic derivative `Re((F'/F)(γ) γ')`. -/
theorem hasDerivAt_norm_value {t : ℝ} (ht : t ∉ rectangleCornerTimes) :
    HasDerivAt (fun s => ‖D.value s‖) (‖D.value t‖ * (D.logVelocity t).re) t := by
  have hsq := (D.hasDerivAt_value ht).norm_sq
  have hpos : (‖D.value t‖ ^ 2) ≠ 0 := pow_ne_zero 2 (D.norm_value_pos t).ne'
  have hsqrt := hsq.sqrt hpos
  have heq : (fun s => √(‖D.value s‖ ^ 2)) = fun s => ‖D.value s‖ := by
    funext s; exact Real.sqrt_sq (norm_nonneg _)
  rw [heq] at hsqrt
  convert hsqrt using 1
  rw [Real.sqrt_sq (norm_nonneg _), Complex.inner]
  have hre : (D.value t * D.logVelocity t * starRingEnd ℂ (D.value t)).re =
      ‖D.value t‖ ^ 2 * (D.logVelocity t).re := by
    rw [mul_comm (D.value t), mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      Complex.re_mul_ofReal]
    ring
  rw [hre]
  field_simp [(D.norm_value_pos t).ne']

/-- **Phase derivative**: `u' = u · i Im((F'/F)(γ) γ')` off the corners. -/
theorem hasDerivAt_phase {t : ℝ} (ht : t ∉ rectangleCornerTimes) :
    HasDerivAt D.phase (D.phaseDeriv t) t := by
  have hm : HasDerivAt (fun s => ((‖D.value s‖ : ℝ) : ℂ))
      (((‖D.value t‖ * (D.logVelocity t).re : ℝ)) : ℂ) t :=
    (D.hasDerivAt_norm_value ht).ofReal_comp
  have hne : ((‖D.value t‖ : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 (D.norm_value_pos t).ne'
  have h := ((D.hasDerivAt_value ht).div hm hne).mul_const D.basePhase⁻¹
  have heq : (D.value t * D.logVelocity t * ((‖D.value t‖ : ℝ) : ℂ) -
        D.value t * (((‖D.value t‖ * (D.logVelocity t).re : ℝ)) : ℂ)) /
          ((‖D.value t‖ : ℝ) : ℂ) ^ 2 * D.basePhase⁻¹ = D.phaseDeriv t := by
    simp only [phaseDeriv, phase]
    have hw := Complex.re_add_im (D.logVelocity t)
    field_simp
    push_cast
    linear_combination -(D.value t * ‖D.value t‖ * D.basePhase⁻¹) * hw
  rw [heq] at h
  exact h

theorem measurable_phaseDeriv : Measurable D.phaseDeriv := by
  unfold phaseDeriv logVelocity
  refine D.continuous_phase.measurable.mul (measurable_const.mul
    (Complex.measurable_ofReal.comp (Complex.measurable_im.comp
      (D.continuous_logDeriv_comp.measurable.mul
        (measurable_rectangleBoundaryVelocity D.z₁ D.z₂)))))

theorem exists_bound_logDeriv : ∃ C, ∀ t,
    ‖logDeriv D.F (rectangleBoundaryPath D.z₁ D.z₂ t)‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    D.continuous_logDeriv_comp.continuousOn
  refine ⟨C, fun t => ?_⟩
  have h := hC (Int.fract t) ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
  have hp : rectangleBoundaryPath D.z₁ D.z₂ (Int.fract t) = rectangleBoundaryPath D.z₁ D.z₂ t := by
    simp [rectangleBoundaryPath, Int.fract_fract]
  rwa [hp] at h

/-- The normalized boundary phase as a piecewise smooth circle phase. -/
def toPhase : PiecewiseSmoothCirclePhase where
  f := D.phase
  f' := D.phaseDeriv
  periodic := D.periodic_phase
  continuous := D.continuous_phase
  corners := rectangleCornerTimes
  countable_corners := countable_rectangleCornerTimes
  hasDerivAt _ hx := D.hasDerivAt_phase hx
  periodic' t := by simp only [phaseDeriv, D.periodic_phase t, D.periodic_logVelocity t]
  measurable' := D.measurable_phaseDeriv
  bound := D.exists_bound_logDeriv.choose * (4 * (|D.z₂.re - D.z₁.re| + |D.z₂.im - D.z₁.im|))
  norm_deriv_le t := by
    rw [phaseDeriv, norm_mul, D.norm_phase, one_mul, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs]
    refine (abs_im_le_norm _).trans ?_
    rw [logVelocity, norm_mul]
    exact mul_le_mul (D.exists_bound_logDeriv.choose_spec t)
      (norm_rectangleBoundaryVelocity_le _ _ t) (norm_nonneg _)
      ((norm_nonneg _).trans (D.exists_bound_logDeriv.choose_spec t))
  norm_eq_one := D.norm_phase

theorem integral_re_logVelocity : ∫ t in (0 : ℝ)..1, ((D.logVelocity t).re : ℂ) = 0 := by
  rw [intervalIntegral.integral_ofReal]
  have hint : IntervalIntegrable (fun t => (D.logVelocity t).re) volume 0 1 := by
    have h := intervalIntegrable_mul_rectangleBoundaryVelocity D.z₁ D.z₂
      D.continuous_logDeriv_comp 0 1
    rw [intervalIntegrable_iff] at h ⊢
    exact h.re
  have hlog : ∀ t ∈ Ioo (0 : ℝ) 1 \ rectangleCornerTimes,
      HasDerivAt (fun s => Real.log ‖D.value s‖) ((D.logVelocity t).re) t := by
    intro t ht
    have h := (D.hasDerivAt_norm_value ht.2).log (D.norm_value_pos t).ne'
    convert h using 1
    field_simp [(D.norm_value_pos t).ne']
  have hcont : ContinuousOn (fun s => Real.log ‖D.value s‖) (Icc 0 1) :=
    (D.continuous_value.norm.log fun s => (D.norm_value_pos s).ne').continuousOn
  rw [integral_eq_of_hasDerivAt_off_countable_of_le _ _ zero_le_one
    countable_rectangleCornerTimes hcont hlog hint]
  have h10 : D.value 1 = D.value 0 := by simpa using D.periodic_value 0
  rw [h10, sub_self, ofReal_zero]

/-- **Winding number of a rectangle boundary phase** is the normalized contour integral of the
logarithmic derivative. -/
theorem windingNumber_toPhase :
    D.toPhase.windingNumber = (2 * π * I)⁻¹ * rectIntegral (logDeriv D.F) D.z₁ D.z₂ := by
  rw [PiecewiseSmoothCirclePhase.windingNumber, ← integral_rectangleBoundary_eq_rectIntegral
    D.z₁ D.z₂ (logDeriv D.F) D.continuous_logDeriv_comp]
  congr 1
  have hpt : ∀ t, D.toPhase.f' t / D.toPhase.f t =
      D.logVelocity t - ((D.logVelocity t).re : ℂ) := by
    intro t
    change D.phaseDeriv t / D.phase t = _
    have hne : D.phase t ≠ 0 := by
      intro h; have := D.norm_phase t; rw [h, norm_zero] at this; exact zero_ne_one this
    rw [phaseDeriv, mul_div_cancel_left₀ _ hne]
    have hw := Complex.re_add_im (D.logVelocity t)
    linear_combination hw
  simp_rw [hpt]
  have hint1 : IntervalIntegrable D.logVelocity volume 0 1 :=
    intervalIntegrable_mul_rectangleBoundaryVelocity D.z₁ D.z₂ D.continuous_logDeriv_comp 0 1
  have hint2 : IntervalIntegrable (fun t => ((D.logVelocity t).re : ℂ)) volume 0 1 := by
    rw [intervalIntegrable_iff] at hint1 ⊢
    exact hint1.re.ofReal
  rw [intervalIntegral.integral_sub hint1 hint2, D.integral_re_logVelocity, sub_zero]
  rfl

/-- **Cubic trace of a rectangle boundary phase**: `Tr (M_u† P M_u - P)³` is the normalized
contour integral of `F'/F` around the rectangle. -/
theorem opTrace_cubicDefect :
    opTrace (restrictedProjectionCubicDefect D.toPhase.polarization ccmCircleHardyProjection) =
      (2 * π * I)⁻¹ * rectIntegral (logDeriv D.F) D.z₁ D.z₂ := by
  rw [← D.windingNumber_toPhase]
  exact D.toPhase.opTrace_cubicDefect

/-- A function holomorphic and zero-free on a neighbourhood of the closed rectangle has a
boundary phase of zero cubic trace. -/
theorem opTrace_cubicDefect_eq_zero_of_zeroFree {V : Set ℂ}
    (hsub : (uIcc D.z₁.re D.z₂.re ×ℂ uIcc D.z₁.im D.z₂.im) ⊆ V)
    (han : AnalyticOnNhd ℂ D.F V) (hne : ∀ z ∈ V, D.F z ≠ 0) :
    opTrace (restrictedProjectionCubicDefect D.toPhase.polarization ccmCircleHardyProjection) =
      0 := by
  have hrect := rectIntegral_logDeriv_multi_zero (t := (∅ : Finset Empty))
    (ρ := fun i : Empty => nomatch i) (m := fun i : Empty => nomatch i)
    (z₁ := D.z₁) (z₂ := D.z₂) (U := V) (by simp) hsub han hne
  have hzero : rectIntegral (logDeriv D.F) D.z₁ D.z₂ = 0 := by simpa using hrect
  rw [D.opTrace_cubicDefect, hzero, mul_zero]

end RectangleArgumentDatum

end RHTower
