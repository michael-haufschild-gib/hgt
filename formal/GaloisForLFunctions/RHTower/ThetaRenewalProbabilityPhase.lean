import GaloisForLFunctions.RHTower.ThetaRenewalWaitingTime
import GaloisForLFunctions.RHTower.ThetaRenewalCoshFactorization
import GaloisForLFunctions.HTGeometry.WaveTraceSpectrum
import GaloisForLFunctions.HTGeometry.WaveTracePoleTransform

/-!
# The probability phase of the theta waiting-time law

The sine integral `Si(w) = ∫₀¹ sin(wu)/u du` is entire and odd, with `Si'(w) = ∫₀¹ cos(wu) du`,
`w Si'(w) = sin w` and `‖Si(w)‖ ≤ ‖w‖ e^{|Im w|}`.  For the waiting-time law `μ` put
`Φ(z) = ∫ Si(zT) μ(dT)`.  On `|Im z| < a`, integration by parts against the survival function
`s = μ((t, ∞))` (the boundary term `s(T) Si(zT)` decays because `s ≤ 2e^{-aT}`) gives
`Φ(z) = ∫₀^∞ (s(t)/t) sin(zt) dt = ∫₀^∞ W(t) sin(zt) dt`, and the odd-kernel pairing
`η + S = ∫ W sinh` turns this into `Φ(z) = -i(η(iz) + S(iz)) = arctan(z/a) + ∫₀^∞ Q(t) sin(zt) dt`.
In particular `Φ` is holomorphic on the strip.
-/

open Complex Filter Topology Set MeasureTheory HurwitzZeta
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

local notation "Θ" => evenKernel (0 : UnitAddCircle)

/-! ## The entire sine integral -/

theorem abs_im_mul_ofReal_le (w : ℂ) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    |(w * u).im| ≤ |w.im| := by
  rw [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_add, abs_mul,
    abs_of_nonneg hu.1]
  exact mul_le_of_le_one_right (abs_nonneg _) hu.2

/-- `‖sin z‖ ≤ ‖z‖ e^{|Im z|}`. -/
theorem norm_csin_le_norm_mul_exp (z : ℂ) : ‖Complex.sin z‖ ≤ ‖z‖ * Real.exp |z.im| := by
  have hF : ∀ r ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun r : ℝ => Complex.sin (z * r))
      (Complex.cos (z * r) * z) r := by
    intro r _
    have h := (((hasDerivAt_id (r : ℂ)).const_mul z).csin).comp_ofReal
    simpa using h
  have hcont : Continuous fun r : ℝ => Complex.cos (z * r) * z := by fun_prop
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hF (hcont.intervalIntegrable _ _)
  have hbound : ∀ r ∈ uIoc (0 : ℝ) 1, ‖Complex.cos (z * r) * z‖ ≤ ‖z‖ * Real.exp |z.im| := by
    intro r hr
    rw [uIoc_of_le zero_le_one] at hr
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left ((norm_ccos_le_exp_abs_im _).trans
      (Real.exp_le_exp.mpr (abs_im_mul_ofReal_le z ⟨hr.1.le, hr.2⟩))) (norm_nonneg _)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [hint] at h
  simpa using h

/-- The entire sine integral `Si(w) = ∫₀^w sin v / v dv = ∫₀¹ sin(wu)/u du`. -/
def thetaSineIntegral (w : ℂ) : ℂ := ∫ u in (0 : ℝ)..1, Complex.sin (w * u) / u

/-- The derivative `Si'(w) = ∫₀¹ cos(wu) du`. -/
def thetaSineIntegralDeriv (w : ℂ) : ℂ := ∫ u in (0 : ℝ)..1, Complex.cos (w * u)

theorem norm_sin_mul_div_le (w : ℂ) {u : ℝ} (hu : u ∈ Ioc (0 : ℝ) 1) :
    ‖Complex.sin (w * u) / u‖ ≤ ‖w‖ * Real.exp |w.im| := by
  have h := norm_csin_le_norm_mul_exp (w * u)
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu.1, div_le_iff₀ hu.1]
  calc ‖Complex.sin (w * u)‖ ≤ ‖w * u‖ * Real.exp |(w * u).im| := h
    _ ≤ ‖w‖ * u * Real.exp |w.im| := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu.1]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
          (abs_im_mul_ofReal_le w ⟨hu.1.le, hu.2⟩)) (mul_nonneg (norm_nonneg _) hu.1.le)
    _ = _ := by ring

theorem measurable_sin_mul_div (w : ℂ) : Measurable fun u : ℝ => Complex.sin (w * u) / u :=
  (Complex.continuous_sin.comp (continuous_const.mul Complex.continuous_ofReal)).measurable.div
    Complex.measurable_ofReal

theorem intervalIntegrable_sin_mul_div (w : ℂ) :
    IntervalIntegrable (fun u : ℝ => Complex.sin (w * u) / u) volume 0 1 := by
  refine (intervalIntegrable_const (c := ‖w‖ * Real.exp |w.im|)).mono_fun'
    (measurable_sin_mul_div w).aestronglyMeasurable ?_
  rw [uIoc_of_le zero_le_one]
  exact (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun u hu =>
    norm_sin_mul_div_le w hu)

theorem hasDerivAt_thetaSineIntegral (w₀ : ℂ) :
    HasDerivAt thetaSineIntegral (thetaSineIntegralDeriv w₀) w₀ := by
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℂ)
    (μ := volume) (a := 0) (b := 1) (F := fun w (u : ℝ) => Complex.sin (w * u) / u)
    (F' := fun w (u : ℝ) => Complex.cos (w * u)) (x₀ := w₀) (s := Metric.ball w₀ 1)
    (bound := fun _ => Real.exp (|w₀.im| + 1)) (Metric.ball_mem_nhds _ one_pos)
    (Eventually.of_forall fun w => (measurable_sin_mul_div w).aestronglyMeasurable)
    (intervalIntegrable_sin_mul_div w₀)
    ((by fun_prop : Continuous fun u : ℝ => Complex.cos (w₀ * u)).aestronglyMeasurable)
    (Eventually.of_forall fun u hu w hw => ?_) intervalIntegrable_const
    (Eventually.of_forall fun u hu w _ => ?_)
  · exact key.2
  · rw [uIoc_of_le zero_le_one] at hu
    refine (norm_ccos_le_exp_abs_im _).trans (Real.exp_le_exp.mpr ?_)
    have h1 := abs_im_mul_ofReal_le w ⟨hu.1.le, hu.2⟩
    have h2 : |w.im| ≤ |w₀.im| + 1 := by
      have := Metric.mem_ball.mp hw
      rw [Complex.dist_eq] at this
      have h3 := Complex.abs_im_le_norm (w - w₀)
      rw [Complex.sub_im] at h3
      have h4 := abs_sub_abs_le_abs_sub w.im w₀.im
      linarith
    linarith
  · rw [uIoc_of_le zero_le_one] at hu
    have hu0 : (u : ℂ) ≠ 0 := by exact_mod_cast hu.1.ne'
    have h := (((hasDerivAt_id w).mul_const (u : ℂ)).csin).div_const (u : ℂ)
    refine h.congr_deriv ?_
    simp only [id, one_mul]
    field_simp

theorem differentiable_thetaSineIntegral : Differentiable ℂ thetaSineIntegral := fun w =>
  (hasDerivAt_thetaSineIntegral w).differentiableAt

theorem continuous_thetaSineIntegral : Continuous thetaSineIntegral :=
  differentiable_thetaSineIntegral.continuous

theorem thetaSineIntegral_zero : thetaSineIntegral 0 = 0 := by simp [thetaSineIntegral]

/-- `Si` is odd. -/
theorem thetaSineIntegral_neg (w : ℂ) : thetaSineIntegral (-w) = -thetaSineIntegral w := by
  simp only [thetaSineIntegral, neg_mul, Complex.sin_neg, neg_div, intervalIntegral.integral_neg]

theorem norm_thetaSineIntegral_le (w : ℂ) : ‖thetaSineIntegral w‖ ≤ ‖w‖ * Real.exp |w.im| := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (f := fun u : ℝ => Complex.sin (w * u) / u) fun u hu =>
      norm_sin_mul_div_le w (by rwa [uIoc_of_le zero_le_one] at hu)
  simpa [thetaSineIntegral] using h

theorem continuous_thetaSineIntegralDeriv : Continuous thetaSineIntegralDeriv :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f := fun w (u : ℝ) => Complex.cos (w * u)) (by fun_prop) continuous_const

theorem norm_thetaSineIntegralDeriv_le (w : ℂ) : ‖thetaSineIntegralDeriv w‖ ≤ Real.exp |w.im| := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (f := fun u : ℝ => Complex.cos (w * u)) fun u hu => by
      rw [uIoc_of_le zero_le_one] at hu
      exact (norm_ccos_le_exp_abs_im _).trans
        (Real.exp_le_exp.mpr (abs_im_mul_ofReal_le w ⟨hu.1.le, hu.2⟩))
  simpa [thetaSineIntegralDeriv] using h

/-- `w Si'(w) = sin w`. -/
theorem mul_thetaSineIntegralDeriv (w : ℂ) : w * thetaSineIntegralDeriv w = Complex.sin w := by
  have hF : ∀ r ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun r : ℝ => Complex.sin (w * r))
      (w * Complex.cos (w * r)) r := by
    intro r _
    have h := (((hasDerivAt_id (r : ℂ)).const_mul w).csin).comp_ofReal
    simpa [mul_comm] using h
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    ((by fun_prop : Continuous fun r : ℝ => w * Complex.cos (w * r)).intervalIntegrable _ _)
  rw [thetaSineIntegralDeriv, ← intervalIntegral.integral_const_mul, h]
  simp

/-- `d/dt Si(zt) = z Si'(zt)`, which is `sin(zt)/t` for `t ≠ 0`. -/
theorem hasDerivAt_thetaSineIntegral_mul (z : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => thetaSineIntegral (z * t)) (z * thetaSineIntegralDeriv (z * t)) t := by
  have h := ((hasDerivAt_thetaSineIntegral (z * t)).comp (t : ℂ)
    ((hasDerivAt_id (t : ℂ)).const_mul z)).comp_ofReal
  simpa [mul_comm] using h

theorem mul_thetaSineIntegralDeriv_mul {z : ℂ} {t : ℝ} (ht : t ≠ 0) :
    z * thetaSineIntegralDeriv (z * t) = Complex.sin (z * t) / t := by
  have h := mul_thetaSineIntegralDeriv (z * t)
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  rw [eq_div_iff ht', ← h]
  ring

/-! ## The probability phase -/

/-- The probability phase `Φ(z) = E_μ[Si(zT)]` of the waiting-time law. -/
def thetaWaitingPhase (z : ℂ) : ℂ := ∫ t, thetaSineIntegral (z * t) ∂thetaWaitingTimeLaw

/-- The strip `|Im z| < a`. -/
def thetaPhaseStrip : Set ℂ := {z | |z.im| < 1 / 4}

theorem isOpen_thetaPhaseStrip : IsOpen thetaPhaseStrip :=
  isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const

theorem thetaWaitingPhase_eq_integral (z : ℂ) :
    thetaWaitingPhase z =
      ∫ t in Ioi (0 : ℝ), thetaSineIntegral (z * t) * ((deriv thetaWaitingCDF t : ℝ) : ℂ) := by
  rw [thetaWaitingPhase, thetaWaitingTimeLaw, integral_withDensity_eq_integral_toReal_smul
    continuous_deriv_thetaWaitingCDF.measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [ENNReal.toReal_ofReal (deriv_thetaWaitingCDF_nonneg (le_of_lt ht)), Complex.real_smul,
    mul_comm]

theorem mul_exp_le_exp_div {b σ : ℝ} (hbσ : b < σ) (t : ℝ) :
    t * Real.exp (b * t) ≤ Real.exp (σ * t) / (σ - b) := by
  have h := Real.add_one_le_exp ((σ - b) * t)
  rw [le_div_iff₀ (by linarith)]
  calc t * Real.exp (b * t) * (σ - b) = ((σ - b) * t) * Real.exp (b * t) := by ring
    _ ≤ Real.exp ((σ - b) * t) * Real.exp (b * t) := by
        gcongr; linarith
    _ = Real.exp (σ * t) := by rw [← Real.exp_add]; ring_nf

theorem abs_im_mul_ofReal_eq (z : ℂ) {t : ℝ} (ht : 0 ≤ t) : |(z * t).im| = |z.im| * t := by
  rw [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_add, abs_mul,
    abs_of_nonneg ht]

theorem norm_thetaSineIntegral_mul_le (z : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    ‖thetaSineIntegral (z * t)‖ ≤ ‖z‖ * (t * Real.exp (|z.im| * t)) := by
  have h := norm_thetaSineIntegral_le (z * t)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht,
    abs_im_mul_ofReal_eq z ht] at h
  calc _ ≤ ‖z‖ * t * Real.exp (|z.im| * t) := h
    _ = _ := by ring

theorem tendsto_mul_exp_neg_mul_atTop {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun t : ℝ => t * Real.exp (-(κ * t))) atTop (𝓝 0) := by
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
    (tendsto_id.const_mul_atTop hκ)).div_const κ
  rw [zero_div] at h
  refine h.congr fun t => ?_
  simp only [Function.comp, pow_one, id]
  field_simp

theorem integrableOn_thetaSineIntegral_mul_deriv {z : ℂ} (hz : |z.im| < 1 / 4) :
    IntegrableOn (fun t : ℝ => thetaSineIntegral (z * t) * ((deriv thetaWaitingCDF t : ℝ) : ℂ))
      (Ioi 0) := by
  set b := |z.im|
  set σ := (b + 1 / 4) / 2
  have hbσ : b < σ := by simp only [σ]; linarith
  have hσ : σ < 1 / 4 := by simp only [σ]; linarith
  have hdom := (integrableOn_exp_mul_deriv_thetaWaitingCDF hσ).const_mul (‖z‖ / (σ - b))
  have hM' := continuous_deriv_thetaWaitingCDF
  refine hdom.mono' ((continuous_thetaSineIntegral.comp (continuous_const.mul
    Complex.continuous_ofReal)).mul (Complex.continuous_ofReal.comp hM')).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  have ht0 : 0 ≤ t := le_of_lt ht
  have hM := deriv_thetaWaitingCDF_nonneg ht0
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hM]
  calc ‖thetaSineIntegral (z * t)‖ * deriv thetaWaitingCDF t
      ≤ ‖z‖ * (t * Real.exp (b * t)) * deriv thetaWaitingCDF t :=
        mul_le_mul_of_nonneg_right (norm_thetaSineIntegral_mul_le z ht0) hM
    _ ≤ ‖z‖ * (Real.exp (σ * t) / (σ - b)) * deriv thetaWaitingCDF t := by
        gcongr; exact mul_exp_le_exp_div hbσ t
    _ = ‖z‖ / (σ - b) * (Real.exp (σ * t) * deriv thetaWaitingCDF t) := by ring

theorem hasDerivAt_neg_thetaRenewalReflectionProfile (t : ℝ) :
    HasDerivAt (fun t => -thetaRenewalReflectionProfile t) (deriv thetaWaitingCDF t) t := by
  have h := (hasDerivAt_thetaWaitingCDF_deriv t).sub_const 1
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun u => ?_)
  simp [thetaWaitingCDF]

/-- **Probability-phase identity (13), first form.** `Φ(z) = ∫₀^∞ (s(t)/t) sin(zt) dt`
on `|Im z| < a`. -/
theorem thetaWaitingPhase_eq_oddKernel {z : ℂ} (hz : |z.im| < 1 / 4) :
    thetaWaitingPhase z = ∫ t in Ioi 0, (thetaRenewalOddKernel t : ℂ) * Complex.sin (z * t) := by
  set b := |z.im| with hbdef
  have hκ : 0 < 1 / 4 - b := by linarith
  set y := thetaRenewalReflectionProfile with hy
  have hyc : Continuous y := continuous_thetaRenewalReflectionProfile
  set g : ℝ → ℂ := fun t => (y t : ℂ) * (z * thetaSineIntegralDeriv (z * t)) with hgdef
  have hgc : Continuous g := (Complex.continuous_ofReal.comp hyc).mul (continuous_const.mul
    (continuous_thetaSineIntegralDeriv.comp (continuous_const.mul Complex.continuous_ofReal)))
  have hg_int : IntegrableOn g (Ioi 0) := by
    have hdom : IntegrableOn (fun t : ℝ => 2 * ‖z‖ * Real.exp (-(1 / 4 - b) * t)) (Ioi 0) :=
      (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul _
    refine hdom.mono' hgc.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 ≤ t := le_of_lt ht
    have h1 := thetaRenewalReflectionProfile_le_two_mul ht0
    have h2 := norm_thetaSineIntegralDeriv_le (z * t)
    rw [abs_im_mul_ofReal_eq z ht0] at h2
    simp only [hgdef, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (show 0 < y t from thetaRenewalReflectionProfile_pos ht0)]
    calc y t * (‖z‖ * ‖thetaSineIntegralDeriv (z * t)‖)
        ≤ (2 * Real.exp (-(t / 4))) * (‖z‖ * Real.exp (b * t)) := by
          gcongr
      _ = 2 * ‖z‖ * Real.exp (-(1 / 4 - b) * t) := by
          rw [mul_mul_mul_comm, ← Real.exp_add]; ring_nf
  have hparts : ∀ T : ℝ, 0 ≤ T → ∫ t in (0 : ℝ)..T, thetaSineIntegral (z * t) *
      ((deriv thetaWaitingCDF t : ℝ) : ℂ) = -((y T : ℂ) * thetaSineIntegral (z * T)) +
        ∫ t in (0 : ℝ)..T, g t := by
    intro T _
    have hv : ∀ t, HasDerivAt (fun t : ℝ => ((-y t : ℝ) : ℂ)) ((deriv thetaWaitingCDF t : ℝ) : ℂ) t :=
      fun t => (hasDerivAt_neg_thetaRenewalReflectionProfile t).ofReal_comp
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := T)
      (fun t _ => hasDerivAt_thetaSineIntegral_mul z t) (fun t _ => hv t)
      ((continuous_const.mul (continuous_thetaSineIntegralDeriv.comp (continuous_const.mul
        Complex.continuous_ofReal))).intervalIntegrable _ _)
      ((Complex.continuous_ofReal.comp continuous_deriv_thetaWaitingCDF).intervalIntegrable _ _)
    rw [h]
    have hint : ∫ t in (0 : ℝ)..T, z * thetaSineIntegralDeriv (z * t) * ((-y t : ℝ) : ℂ) =
        -∫ t in (0 : ℝ)..T, g t := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [hgdef]; push_cast; ring
    rw [hint]
    simp [thetaSineIntegral_zero]
    ring
  have hL1 := intervalIntegral_tendsto_integral_Ioi 0 (integrableOn_thetaSineIntegral_mul_deriv hz)
    tendsto_id
  have hL2 := intervalIntegral_tendsto_integral_Ioi 0 hg_int tendsto_id
  have hbd : Tendsto (fun T : ℝ => (y T : ℂ) * thetaSineIntegral (z * T)) atTop (𝓝 0) := by
    have hdom := (tendsto_mul_exp_neg_mul_atTop hκ).const_mul (2 * ‖z‖)
    rw [mul_zero] at hdom
    refine squeeze_zero_norm' ?_ hdom
    filter_upwards [eventually_ge_atTop 0] with T hT
    have h1 := thetaRenewalReflectionProfile_le_two_mul hT
    have h2 := norm_thetaSineIntegral_mul_le z hT
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (thetaRenewalReflectionProfile_pos hT)]
    calc y T * ‖thetaSineIntegral (z * T)‖
        ≤ (2 * Real.exp (-(T / 4))) * (‖z‖ * (T * Real.exp (b * T))) := by gcongr
      _ = 2 * ‖z‖ * (T * Real.exp (-((1 / 4 - b) * T))) := by
          rw [show -((1 / 4 - b) * T) = -(T / 4) + b * T by ring, Real.exp_add]; ring
  have hlim := hbd.neg.add hL2
  rw [neg_zero, zero_add] at hlim
  have heq := tendsto_nhds_unique (hL1.congr' ((eventually_ge_atTop 0).mono fun T hT =>
    (hparts T hT))) hlim
  rw [thetaWaitingPhase_eq_integral, heq]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (t : ℝ) ≠ 0 := ne_of_gt ht
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
  simp only [hgdef]
  rw [mul_thetaSineIntegralDeriv_mul ht0]
  simp only [hy, thetaRenewalOddKernel, thetaRenewalReflectionProfile, thetaRenewalMomentKernel]
  push_cast
  field_simp

/-- **(13), renewal form.** `∫₀^∞ W(t) sin(zt) dt = -i (η(iz) + S(iz))`. -/
theorem integral_oddKernel_mul_sin_eq {z : ℂ} (hz : |z.im| < 1 / 4) :
    ∫ t in Ioi 0, (thetaRenewalOddKernel t : ℂ) * Complex.sin (z * t) =
      -I * (thetaRenewalPhase (I * z) + thetaRenewalSinTransform (I * z)) := by
  have hs : |(I * z).re| < 1 / 4 := by simpa using hz
  rw [thetaRenewalPhase_add_sin_eq_integral hs]
  have e : ∀ t : ℝ, (thetaRenewalOddKernel t : ℂ) * Complex.sinh (I * z * t) =
      (thetaRenewalOddKernel t : ℂ) * Complex.sin (z * t) * I := fun t => by
    rw [show I * z * t = (z * t) * I by ring, Complex.sinh_mul_I]; ring
  simp_rw [e]
  rw [integral_mul_const, ← mul_assoc, mul_comm (-I), mul_assoc, neg_mul, Complex.I_mul_I]
  ring

theorem neg_I_mul_thetaRenewalSinTransform_I_mul (z : ℂ) :
    -I * thetaRenewalSinTransform (I * z) =
      ∫ t in Ioi 0, (thetaRenewalLogKernel t : ℂ) * Complex.sin (z * t) := by
  rw [thetaRenewalSinTransform]
  have e : ∀ t : ℝ, (thetaRenewalLogKernel t : ℂ) * Complex.sinh (I * z * t) =
      (thetaRenewalLogKernel t : ℂ) * Complex.sin (z * t) * I := fun t => by
    rw [show I * z * t = (z * t) * I by ring, Complex.sinh_mul_I]; ring
  simp_rw [e]
  rw [integral_mul_const, ← mul_assoc, mul_comm (-I), mul_assoc, neg_mul, Complex.I_mul_I]
  ring

theorem arg_lt_of_re_pos {w : ℂ} (hw : 0 < w.re) : |w.arg| < Real.pi / 2 :=
  Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw)

/-- `-i η(iz) = arctan(z/a)` on `|Im z| < a`. -/
theorem neg_I_mul_thetaRenewalPhase_I_mul {z : ℂ} (hz : |z.im| < 1 / 4) :
    -I * thetaRenewalPhase (I * z) = Complex.arctan (4 * z) := by
  have hp : 0 < ((1 / 4 : ℂ) + I * z).re := by simp; linarith [abs_lt.mp hz]
  have hm : 0 < ((1 / 4 : ℂ) - I * z).re := by simp; linarith [abs_lt.mp hz]
  have hp0 : (1 / 4 : ℂ) + I * z ≠ 0 := fun h => by rw [h] at hp; simp at hp
  have hm0 : (1 / 4 : ℂ) - I * z ≠ 0 := fun h => by rw [h] at hm; simp at hm
  have hq : (1 + 4 * z * I) / (1 - 4 * z * I) = ((1 / 4 : ℂ) + I * z) / ((1 / 4 : ℂ) - I * z) := by
    rw [div_eq_div_iff (by
      intro h; apply hm0; linear_combination h / 4) hm0]
    ring
  have hlog : Complex.log (((1 / 4 : ℂ) + I * z) / ((1 / 4 : ℂ) - I * z)) =
      Complex.log ((1 / 4 : ℂ) + I * z) - Complex.log ((1 / 4 : ℂ) - I * z) := by
    have he : ((1 / 4 : ℂ) + I * z) / ((1 / 4 : ℂ) - I * z) =
        Complex.exp (Complex.log ((1 / 4 : ℂ) + I * z) - Complex.log ((1 / 4 : ℂ) - I * z)) := by
      rw [Complex.exp_sub, Complex.exp_log hp0, Complex.exp_log hm0]
    have h1 := arg_lt_of_re_pos hp
    have h2 := arg_lt_of_re_pos hm
    rw [he, Complex.log_exp] <;> simp only [Complex.sub_im, Complex.log_im] <;>
      linarith [abs_lt.mp h1, abs_lt.mp h2]
  rw [thetaRenewalPhase, Complex.arctan, hq, hlog]
  ring

/-- **The probability-phase identity (13).** On `|Im z| < a`,
`Φ(z) = ∫₀^∞ (s(t)/t) sin(zt) dt = arctan(z/a) + ∫₀^∞ Q(t) sin(zt) dt`. -/
theorem thetaWaitingPhase_eq_arctan_add {z : ℂ} (hz : |z.im| < 1 / 4) :
    thetaWaitingPhase z = Complex.arctan (4 * z) +
      ∫ t in Ioi 0, (thetaRenewalLogKernel t : ℂ) * Complex.sin (z * t) := by
  rw [thetaWaitingPhase_eq_oddKernel hz, integral_oddKernel_mul_sin_eq hz, mul_add,
    neg_I_mul_thetaRenewalPhase_I_mul hz, neg_I_mul_thetaRenewalSinTransform_I_mul]

theorem thetaWaitingPhase_eq_neg_I_mul {z : ℂ} (hz : |z.im| < 1 / 4) :
    thetaWaitingPhase z = -I * (thetaRenewalPhase (I * z) + thetaRenewalSinTransform (I * z)) := by
  rw [thetaWaitingPhase_eq_oddKernel hz, integral_oddKernel_mul_sin_eq hz]

theorem I_mul_mem_thetaRenewalStrip {z : ℂ} (hz : z ∈ thetaPhaseStrip) :
    I * z ∈ thetaRenewalStrip := by
  simpa [thetaRenewalStrip, thetaPhaseStrip] using hz

/-- `Φ` is holomorphic on the strip `|Im z| < a`. -/
theorem differentiableOn_thetaWaitingPhase :
    DifferentiableOn ℂ thetaWaitingPhase thetaPhaseStrip := by
  have hmap : MapsTo (fun z => I * z) thetaPhaseStrip thetaRenewalStrip :=
    fun z hz => I_mul_mem_thetaRenewalStrip hz
  have h : DifferentiableOn ℂ (fun z => -I * (thetaRenewalPhase (I * z) +
      thetaRenewalSinTransform (I * z))) thetaPhaseStrip :=
    (differentiableOn_const _).mul ((differentiableOn_thetaRenewalPhase.comp
      ((differentiableOn_const I).mul differentiableOn_id) hmap).add
      (differentiableOn_thetaRenewalSinTransform.comp
        ((differentiableOn_const I).mul differentiableOn_id) hmap))
  exact h.congr fun z hz => thetaWaitingPhase_eq_neg_I_mul hz

end RHTower
