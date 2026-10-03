import GaloisForLFunctions.RHTower.RectangleBoundaryPhaseWinding

/-!
# Rectangle boundary phases depend `C¹`-continuously on the logarithmic current

The normalized boundary phase of a rectangle argument datum is the exponential of its integrated
angular velocity: `u(t) = exp(i θ(t))`, `θ(t) = ∫₀ᵗ Im((F'/F)(γ) γ')`.  Consequently, if the
logarithmic derivatives of two data differ by at most `ε` along the boundary, the phases differ
by at most `ε V` and their derivatives by `O(ε)` uniformly, where `V` bounds the boundary velocity.
A family of data whose logarithmic currents converge uniformly on the boundary therefore yields
piecewise smooth phases converging in `C¹`, hence a trace-class homotopy of cubic defects.
-/

noncomputable section

open Complex MeasureTheory intervalIntegral Set Filter Topology ContinuousLinearMap
open scoped Real

namespace RHTower

/-- Off the corner times the boundary velocity is locally constant. -/
theorem eventually_rectangleBoundaryVelocity_eq (z₁ z₂ : ℂ) {t : ℝ}
    (ht : t ∉ rectangleCornerTimes) :
    ∀ᶠ y in 𝓝 t, rectangleBoundaryVelocity z₁ z₂ y = rectangleBoundaryVelocity z₁ z₂ t := by
  obtain ⟨h0, h1, h2, h3⟩ := rectangleCornerTimes_of_fract ht
  have hlt : Int.fract t < 1 := Int.fract_lt_one t
  set k : ℤ := ⌊t⌋
  have hloc : ∀ᶠ y : ℝ in 𝓝 t, Int.fract y = y - (k : ℝ) := by
    have hmem : Ioo (k : ℝ) (k + 1) ∈ 𝓝 t := by
      refine Ioo_mem_nhds ?_ ?_
      · have := Int.floor_add_fract t; linarith
      · have := Int.floor_add_fract t; linarith
    filter_upwards [hmem] with y hy
    rw [Int.fract, Int.floor_eq_iff.2 ⟨hy.1.le, hy.2⟩]
  have hft : Int.fract t = t - k := by rw [Int.fract]
  have hcont : Tendsto (fun y : ℝ => y - (k : ℝ)) (𝓝 t) (𝓝 (Int.fract t)) := by
    rw [hft]; exact (continuous_id.sub continuous_const).tendsto t
  have hedge : ∀ᶠ τ in 𝓝 (Int.fract t),
      rectangleEdgeVelocity z₁ z₂ τ = rectangleEdgeVelocity z₁ z₂ (Int.fract t) := by
    rcases lt_or_gt_of_ne h1 with hq | hq
    · filter_upwards [Iio_mem_nhds hq] with τ hτ
      rw [rectangleEdgeVelocity, rectangleEdgeVelocity, if_pos (le_of_lt hτ), if_pos hq.le]
    rcases lt_or_gt_of_ne h2 with hq2 | hq2
    · filter_upwards [Ioo_mem_nhds hq hq2] with τ hτ
      rw [rectangleEdgeVelocity, rectangleEdgeVelocity, if_neg (not_le.2 hτ.1),
        if_pos (le_of_lt hτ.2), if_neg (not_le.2 hq), if_pos hq2.le]
    rcases lt_or_gt_of_ne h3 with hq3 | hq3
    · filter_upwards [Ioo_mem_nhds hq2 hq3] with τ hτ
      rw [rectangleEdgeVelocity, rectangleEdgeVelocity, if_neg (by linarith [hτ.1]),
        if_neg (not_le.2 hτ.1), if_pos (le_of_lt hτ.2), if_neg (by linarith),
        if_neg (not_le.2 hq2), if_pos hq3.le]
    · filter_upwards [Ioi_mem_nhds hq3] with τ hτ
      have hτ' : 3 / 4 < τ := hτ
      rw [rectangleEdgeVelocity, rectangleEdgeVelocity, if_neg (by linarith),
        if_neg (by linarith), if_neg (not_le.2 hτ'), if_neg (by linarith), if_neg (by linarith),
        if_neg (not_le.2 hq3)]
  filter_upwards [hloc, hcont.eventually hedge] with y hy hy'
  rw [rectangleBoundaryVelocity, rectangleBoundaryVelocity, hy, hy']

namespace RectangleArgumentDatum

variable (D : RectangleArgumentDatum)

/-- Bound for the boundary velocity. -/
def velocityBound : ℝ := 4 * (|D.z₂.re - D.z₁.re| + |D.z₂.im - D.z₁.im|)

theorem velocityBound_nonneg : 0 ≤ D.velocityBound := by
  unfold velocityBound; positivity

theorem continuousAt_logVelocity {t : ℝ} (ht : t ∉ rectangleCornerTimes) :
    ContinuousAt D.logVelocity t := by
  have hv : ContinuousAt (rectangleBoundaryVelocity D.z₁ D.z₂) t :=
    continuousAt_const.congr
      ((eventually_rectangleBoundaryVelocity_eq D.z₁ D.z₂ ht).mono fun _ hy => hy.symm)
  exact D.continuous_logDeriv_comp.continuousAt.mul hv

theorem intervalIntegrable_im_logVelocity (a b : ℝ) :
    IntervalIntegrable (fun s => (D.logVelocity s).im) volume a b := by
  have h := intervalIntegrable_mul_rectangleBoundaryVelocity D.z₁ D.z₂
    D.continuous_logDeriv_comp a b
  rw [intervalIntegrable_iff] at h ⊢
  exact h.im

/-- The integrated angular velocity `θ(t) = ∫₀ᵗ Im((F'/F)(γ) γ')`. -/
def angle (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, (D.logVelocity s).im

theorem measurable_logVelocity : Measurable D.logVelocity :=
  D.continuous_logDeriv_comp.measurable.mul (measurable_rectangleBoundaryVelocity D.z₁ D.z₂)

theorem hasDerivAt_angle {t : ℝ} (ht : t ∉ rectangleCornerTimes) :
    HasDerivAt D.angle (D.logVelocity t).im t :=
  intervalIntegral.integral_hasDerivAt_right (D.intervalIntegrable_im_logVelocity 0 t)
    (Complex.measurable_im.comp D.measurable_logVelocity).stronglyMeasurable.stronglyMeasurableAtFilter
    (Complex.continuous_im.continuousAt.comp (D.continuousAt_logVelocity ht))

theorem continuous_angle : Continuous D.angle :=
  intervalIntegral.continuous_primitive D.intervalIntegrable_im_logVelocity 0

theorem phase_zero : D.phase 0 = 1 := by
  rw [phase, ← basePhase]
  have hne : D.basePhase ≠ 0 := by
    intro h; have := D.norm_basePhase; rw [h, norm_zero] at this; exact zero_ne_one this
  exact mul_inv_cancel₀ hne

/-- **The phase is the exponential of the integrated angle**: `u(t) = exp(i θ(t))` for `t ≥ 0`. -/
theorem phase_eq_exp_angle {t : ℝ} (ht : 0 ≤ t) :
    D.phase t = Complex.exp (I * (D.angle t : ℂ)) := by
  let ψ : ℝ → ℂ := fun s => D.phase s * Complex.exp (-(I * (D.angle s : ℂ)))
  have hψc : ContinuousOn ψ (Icc 0 t) :=
    (D.continuous_phase.mul (Complex.continuous_exp.comp
      ((continuous_const.mul (continuous_ofReal.comp D.continuous_angle)).neg))).continuousOn
  have hψd : ∀ s ∈ Ioo 0 t \ rectangleCornerTimes, HasDerivAt ψ 0 s := by
    intro s hs
    have hθ := (D.hasDerivAt_angle hs.2).ofReal_comp
    have hneg : HasDerivAt (fun y => -(I * (D.angle y : ℂ)))
        (-(I * (((D.logVelocity s).im : ℝ) : ℂ))) s := (hθ.const_mul I).neg
    have hexp := hneg.cexp
    have h := (D.hasDerivAt_phase hs.2).mul hexp
    have hzero : D.phaseDeriv s * Complex.exp (-(I * (D.angle s : ℂ))) +
        D.phase s * (Complex.exp (-(I * (D.angle s : ℂ))) *
          -(I * (((D.logVelocity s).im : ℝ) : ℂ))) = 0 := by
      simp only [phaseDeriv]
      ring
    rw [hzero] at h
    exact h
  have hFTC := integral_eq_of_hasDerivAt_off_countable_of_le ψ (fun _ => 0) ht
    countable_rectangleCornerTimes hψc hψd intervalIntegrable_const
  rw [intervalIntegral.integral_zero] at hFTC
  have hψ0 : ψ 0 = 1 := by
    simp only [ψ, D.phase_zero, angle, intervalIntegral.integral_same, ofReal_zero, mul_zero,
      neg_zero, Complex.exp_zero, mul_one]
  have hψt : ψ t = 1 := by rw [← hψ0]; linear_combination -hFTC
  have hmul : D.phase t = ψ t * Complex.exp (I * (D.angle t : ℂ)) := by
    simp only [ψ, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
  rw [hmul, hψt, one_mul]

/-- The phase at `t` equals the phase at the fractional part of `t`. -/
theorem phase_fract (t : ℝ) : D.phase (Int.fract t) = D.phase t := by
  have := D.periodic_phase.sub_int_mul_eq (x := t) ⌊t⌋
  rw [mul_one] at this
  rw [Int.fract, this]

/-- Two data on the same rectangle: logarithmic currents `ε`-close on the boundary give phases
`ε V`-close. -/
theorem norm_phase_sub_le (D' : RectangleArgumentDatum) (h₁ : D'.z₁ = D.z₁) (h₂ : D'.z₂ = D.z₂)
    {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ t, ‖logDeriv D'.F (rectangleBoundaryPath D.z₁ D.z₂ t) -
      logDeriv D.F (rectangleBoundaryPath D.z₁ D.z₂ t)‖ ≤ ε) (t : ℝ) :
    ‖D'.phase t - D.phase t‖ ≤ ε * D.velocityBound := by
  have hlv : ∀ s, ‖D'.logVelocity s - D.logVelocity s‖ ≤ ε * D.velocityBound := by
    intro s
    rw [logVelocity, logVelocity, h₁, h₂, ← sub_mul, norm_mul]
    exact mul_le_mul (h s) (norm_rectangleBoundaryVelocity_le _ _ s) (norm_nonneg _) hε
  rw [← D.phase_fract, ← D'.phase_fract]
  set τ := Int.fract t
  have hτ0 : 0 ≤ τ := Int.fract_nonneg t
  have hτ1 : τ ≤ 1 := (Int.fract_lt_one t).le
  rw [D.phase_eq_exp_angle hτ0, D'.phase_eq_exp_angle hτ0]
  have hdiff : |D'.angle τ - D.angle τ| ≤ ε * D.velocityBound := by
    rw [angle, angle, ← intervalIntegral.integral_sub (D'.intervalIntegrable_im_logVelocity 0 τ)
      (D.intervalIntegrable_im_logVelocity 0 τ), ← Real.norm_eq_abs]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := ε * D.velocityBound)
      fun s _ => ?_).trans ?_
    · rw [Real.norm_eq_abs, ← Complex.sub_im]
      exact (abs_im_le_norm _).trans (hlv s)
    · rw [sub_zero, abs_of_nonneg hτ0]
      exact mul_le_of_le_one_right (mul_nonneg hε D.velocityBound_nonneg) hτ1
  have hfac : Complex.exp (I * (D'.angle τ : ℂ)) - Complex.exp (I * (D.angle τ : ℂ)) =
      Complex.exp (I * (D.angle τ : ℂ)) *
        (Complex.exp (I * ((D'.angle τ - D.angle τ : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hfac, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le.trans (by rwa [Real.norm_eq_abs])

/-- Bound for the logarithmic derivative along the boundary. -/
def logDerivBound : ℝ := D.exists_bound_logDeriv.choose

theorem norm_logVelocity_le (t : ℝ) : ‖D.logVelocity t‖ ≤ D.logDerivBound * D.velocityBound := by
  rw [logVelocity, norm_mul]
  exact mul_le_mul (D.exists_bound_logDeriv.choose_spec t)
    (norm_rectangleBoundaryVelocity_le _ _ t) (norm_nonneg _)
    ((norm_nonneg _).trans (D.exists_bound_logDeriv.choose_spec t))

/-- Two data on the same rectangle: logarithmic currents `ε`-close on the boundary give phase
derivatives `O(ε)`-close. -/
theorem norm_phaseDeriv_sub_le (D' : RectangleArgumentDatum) (h₁ : D'.z₁ = D.z₁)
    (h₂ : D'.z₂ = D.z₂) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ t, ‖logDeriv D'.F (rectangleBoundaryPath D.z₁ D.z₂ t) -
      logDeriv D.F (rectangleBoundaryPath D.z₁ D.z₂ t)‖ ≤ ε) (t : ℝ) :
    ‖D'.phaseDeriv t - D.phaseDeriv t‖ ≤
      ε * D.velocityBound * (D.logDerivBound * D.velocityBound + ε * D.velocityBound) +
        ε * D.velocityBound := by
  have hlv : ‖D'.logVelocity t - D.logVelocity t‖ ≤ ε * D.velocityBound := by
    rw [logVelocity, logVelocity, h₁, h₂, ← sub_mul, norm_mul]
    exact mul_le_mul (h t) (norm_rectangleBoundaryVelocity_le _ _ t) (norm_nonneg _) hε
  have hw' : ‖D'.logVelocity t‖ ≤ D.logDerivBound * D.velocityBound + ε * D.velocityBound := by
    have := norm_sub_norm_le (D'.logVelocity t) (D.logVelocity t)
    linarith [D.norm_logVelocity_le t]
  have hp := D.norm_phase_sub_le D' h₁ h₂ hε h t
  have heq : D'.phaseDeriv t - D.phaseDeriv t =
      (D'.phase t - D.phase t) * (I * ((D'.logVelocity t).im : ℂ)) +
        D.phase t * (I * (((D'.logVelocity t - D.logVelocity t).im : ℝ) : ℂ)) := by
    simp only [phaseDeriv, Complex.sub_im, ofReal_sub]
    ring
  rw [heq]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul hp ((abs_im_le_norm _).trans hw') (abs_nonneg _)
      (mul_nonneg hε D.velocityBound_nonneg)
  · rw [norm_mul, D.norm_phase, one_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs]
    exact (abs_im_le_norm _).trans hlv

/-- Uniform convergence of logarithmic currents on the boundary gives `C¹` convergence of the
boundary phases. -/
theorem phase_convergence {ι : Type*} {l : Filter ι} (Dj : ι → RectangleArgumentDatum)
    (h₁ : ∀ j, (Dj j).z₁ = D.z₁) (h₂ : ∀ j, (Dj j).z₂ = D.z₂)
    (hconv : ∀ ε > 0, ∀ᶠ j in l, ∀ t, ‖logDeriv (Dj j).F (rectangleBoundaryPath D.z₁ D.z₂ t) -
      logDeriv D.F (rectangleBoundaryPath D.z₁ D.z₂ t)‖ ≤ ε) :
    (∀ ε > 0, ∀ᶠ j in l, ∀ x, ‖(Dj j).toPhase.f x - D.toPhase.f x‖ ≤ ε) ∧
    (∀ ε > 0, ∀ᶠ j in l, ∀ x, ‖(Dj j).toPhase.f' x - D.toPhase.f' x‖ ≤ ε) := by
  set V := D.velocityBound
  set C := D.logDerivBound
  have hV := D.velocityBound_nonneg
  have hC : 0 ≤ C := (norm_nonneg _).trans (D.exists_bound_logDeriv.choose_spec 0)
  constructor
  · intro ε hε
    have hδ : 0 < ε / (V + 1) := by positivity
    filter_upwards [hconv _ hδ] with j hj x
    refine (D.norm_phase_sub_le (Dj j) (h₁ j) (h₂ j) hδ.le hj x).trans ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  · intro ε hε
    set K := V * (C * V + V) + V
    have hK : 0 ≤ K := by positivity
    set δ := min 1 (ε / (K + 1))
    have hδ0 : 0 < δ := lt_min one_pos (by positivity)
    have hδ1 : δ ≤ 1 := min_le_left _ _
    have hδε : δ ≤ ε / (K + 1) := min_le_right _ _
    filter_upwards [hconv _ hδ0] with j hj x
    refine (D.norm_phaseDeriv_sub_le (Dj j) (h₁ j) (h₂ j) hδ0.le hj x).trans ?_
    have h1 : δ * V * (C * V + δ * V) + δ * V ≤ δ * K := by
      have hδV : δ * V ≤ V := mul_le_of_le_one_left hV hδ1
      have : δ * V * (C * V + δ * V) ≤ δ * V * (C * V + V) :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hδ0.le hV)
      simp only [K]
      nlinarith
    have h2 : δ * K ≤ ε := by
      calc δ * K ≤ ε / (K + 1) * K := mul_le_mul_of_nonneg_right hδε hK
        _ ≤ ε := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith
    exact h1.trans h2

end RectangleArgumentDatum

end RHTower
