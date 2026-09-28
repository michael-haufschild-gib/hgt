import GaloisForLFunctions.RHTower.ThetaRenewalProbabilityPhase

/-!
# The slope of the theta probability phase

On `|Im z| < a` the phase `Φ = -i(η(i·) + S(i·))` has derivative
`Φ'(z) = η'(iz) + S'(iz) = ∫₀^∞ e^{-at} cos(zt) dt + ∫₀^∞ tQ(t) cos(zt) dt = ∫₀^∞ s(t) cos(zt) dt`,
and integration by parts against `s' = -M'` gives `Φ'(z) = ∫ sin(zT)/z μ(dT)` for `z ≠ 0`, with the
removable value `Φ'(0) = ∫₀^∞ s = E_μ[T] > 0`.  On the real axis `Φ'(τ) = ∫₀^∞ s(t) cos(τt) dt` is the
Fourier transform of the finite nonnegative even density `s(|t|)/2`; the identity
`Σ_{j,k} c_j c̄_k cos((τ_j - τ_k)t) = (‖Σ c_j e^{iτ_j t}‖² + ‖Σ c_j e^{-iτ_j t}‖²)/2` makes it
positive definite.
-/

open Complex Filter Topology Set MeasureTheory HurwitzZeta
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

local notation "Θ" => evenKernel (0 : UnitAddCircle)

/-! ## Integrals against the waiting-time law -/

theorem integral_thetaWaitingTimeLaw (g : ℝ → ℂ) :
    ∫ t, g t ∂thetaWaitingTimeLaw =
      ∫ t in Ioi (0 : ℝ), g t * ((deriv thetaWaitingCDF t : ℝ) : ℂ) := by
  rw [thetaWaitingTimeLaw, integral_withDensity_eq_integral_toReal_smul
    continuous_deriv_thetaWaitingCDF.measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [ENNReal.toReal_ofReal (deriv_thetaWaitingCDF_nonneg (le_of_lt ht)), Complex.real_smul,
    mul_comm]

theorem integrableOn_thetaRenewalReflectionProfile_mul_exp {b : ℝ} (hb : b < 1 / 4) :
    IntegrableOn (fun t => thetaRenewalReflectionProfile t * Real.exp (b * t)) (Ioi 0) := by
  have hdom : IntegrableOn (fun t : ℝ => 2 * Real.exp (-(1 / 4 - b) * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul _
  refine hdom.mono' ((continuous_thetaRenewalReflectionProfile.mul
    (by fun_prop : Continuous fun t : ℝ => Real.exp (b * t))).aestronglyMeasurable) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  have ht0 : 0 ≤ t := le_of_lt ht
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos (thetaRenewalReflectionProfile_pos ht0)
    (Real.exp_pos _))]
  calc thetaRenewalReflectionProfile t * Real.exp (b * t)
      ≤ 2 * Real.exp (-(t / 4)) * Real.exp (b * t) :=
        mul_le_mul_of_nonneg_right (thetaRenewalReflectionProfile_le_two_mul ht0)
          (Real.exp_pos _).le
    _ = 2 * Real.exp (-(1 / 4 - b) * t) := by rw [mul_assoc, ← Real.exp_add]; ring_nf

theorem integrableOn_thetaRenewalReflectionProfile :
    IntegrableOn thetaRenewalReflectionProfile (Ioi 0) := by
  simpa using integrableOn_thetaRenewalReflectionProfile_mul_exp (b := 0) (by norm_num)

theorem norm_ccos_mul_ofReal_le_of_nonneg (z : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    ‖Complex.cos (z * t)‖ ≤ Real.exp (|z.im| * t) :=
  (norm_ccos_mul_ofReal_le z t).trans_eq (by rw [abs_of_nonneg ht])

theorem norm_csin_mul_ofReal_le_of_nonneg (z : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    ‖Complex.sin (z * t)‖ ≤ Real.exp (|z.im| * t) :=
  (norm_csin_mul_ofReal_le z t).trans_eq (by rw [abs_of_nonneg ht])

theorem integrableOn_reflectionProfile_mul_ccos {z : ℂ} (hz : |z.im| < 1 / 4) :
    IntegrableOn (fun t : ℝ => (thetaRenewalReflectionProfile t : ℂ) * Complex.cos (z * t))
      (Ioi 0) := by
  refine (integrableOn_thetaRenewalReflectionProfile_mul_exp hz).mono'
    ((Complex.continuous_ofReal.comp continuous_thetaRenewalReflectionProfile).mul
      (by fun_prop : Continuous fun t : ℝ => Complex.cos (z * t))).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  have ht0 : 0 ≤ t := le_of_lt ht
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (thetaRenewalReflectionProfile_pos ht0)]
  exact mul_le_mul_of_nonneg_left (norm_ccos_mul_ofReal_le_of_nonneg z ht0)
    (thetaRenewalReflectionProfile_pos ht0).le

/-! ## The phase derivative (14) -/

theorem integral_exp_mul_ccos {z : ℂ} (hz : |z.im| < 1 / 4) :
    ∫ t in Ioi (0 : ℝ), (Real.exp (-(t / 4)) : ℂ) * Complex.cos (z * t) =
      (1 / (1 / 4 - I * z) + 1 / (1 / 4 + I * z)) / 2 := by
  have ha : (-(1 / 4 : ℂ) + I * z).re < 0 := by simp; linarith [abs_lt.mp hz]
  have hb : (-(1 / 4 : ℂ) - I * z).re < 0 := by simp; linarith [abs_lt.mp hz]
  have h1 := integral_exp_mul_complex_Ioi ha 0
  have h2 := integral_exp_mul_complex_Ioi hb 0
  have i1 := integrableOn_exp_mul_complex_Ioi ha 0
  have i2 := integrableOn_exp_mul_complex_Ioi hb 0
  have e : ∀ t : ℝ, (Real.exp (-(t / 4)) : ℂ) * Complex.cos (z * t) =
      (Complex.exp ((-(1 / 4 : ℂ) + I * z) * t) + Complex.exp ((-(1 / 4 : ℂ) - I * z) * t)) / 2 := by
    intro t
    rw [Complex.cos, Complex.ofReal_exp, ← mul_div_assoc, mul_add, ← Complex.exp_add,
      ← Complex.exp_add]
    congr 3 <;> push_cast <;> ring
  simp_rw [e]
  rw [integral_div, integral_add i1 i2, h1, h2]
  have hp : (1 / 4 : ℂ) - I * z ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith [abs_lt.mp hz]
  have hm : (1 / 4 : ℂ) + I * z ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith [abs_lt.mp hz]
  have hp' : -(1 / 4 : ℂ) + I * z ≠ 0 := by
    intro h; apply hp; linear_combination -h
  have hm' : -(1 / 4 : ℂ) - I * z ≠ 0 := by
    intro h; apply hm; linear_combination -h
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [show -(1 / 4 : ℂ) + I * z = -(1 / 4 - I * z) by ring,
    show -(1 / 4 : ℂ) - I * z = -(1 / 4 + I * z) by ring, neg_div_neg_eq, neg_div_neg_eq]

/-- **The phase derivative (14).** `Φ'(z) = ∫₀^∞ s(t) cos(zt) dt` on `|Im z| < a`. -/
theorem hasDerivAt_thetaWaitingPhase {z : ℂ} (hz : |z.im| < 1 / 4) :
    HasDerivAt thetaWaitingPhase
      (∫ t in Ioi (0 : ℝ), (thetaRenewalReflectionProfile t : ℂ) * Complex.cos (z * t)) z := by
  have hzs : z ∈ thetaPhaseStrip := hz
  have hIz : I * z ∈ thetaRenewalStrip := I_mul_mem_thetaRenewalStrip hzs
  have hIz' : |(I * z).re| < 1 / 4 := hIz
  have h1 : HasDerivAt (fun w : ℂ => I * w) I z := by
    simpa using (hasDerivAt_id z).const_mul I
  have hη : HasDerivAt (fun w => thetaRenewalPhase (I * w))
      ((1 / (1 / 4 - I * z) + 1 / (1 / 4 + I * z)) / 2 * I) z :=
    (hasDerivAt_thetaRenewalPhase hIz').comp z h1
  have hS : HasDerivAt (fun w => thetaRenewalSinTransform (I * w))
      ((∫ t in Ioi (0 : ℝ), (thetaRenewalLogKernel t : ℂ) *
        (Complex.cosh (I * z * t) * t)) * I) z :=
    (hasDerivAt_thetaRenewal_transform Complex.hasDerivAt_sinh Complex.continuous_sinh
      Complex.continuous_cosh norm_sinh_le_exp_abs_re' norm_cosh_le_exp_abs_re hIz).comp z h1
  have hF : HasDerivAt (fun w => -I * (thetaRenewalPhase (I * w) +
      thetaRenewalSinTransform (I * w)))
      ((1 / (1 / 4 - I * z) + 1 / (1 / 4 + I * z)) / 2 +
        ∫ t in Ioi (0 : ℝ), (thetaRenewalLogKernel t : ℂ) *
          (Complex.cosh (I * z * t) * t)) z := by
    refine ((hη.add hS).const_mul (-I)).congr_deriv ?_
    rw [← add_mul, ← mul_assoc, mul_comm (-I), mul_assoc, neg_mul, Complex.I_mul_I, neg_neg,
      mul_one]
  have hev : (fun w => -I * (thetaRenewalPhase (I * w) + thetaRenewalSinTransform (I * w))) =ᶠ[𝓝 z]
      thetaWaitingPhase := by
    filter_upwards [isOpen_thetaPhaseStrip.mem_nhds hzs] with w hw
    exact (thetaWaitingPhase_eq_neg_I_mul hw).symm
  refine (hF.congr_of_eventuallyEq hev.symm).congr_deriv ?_
  have hA : IntegrableOn (fun t : ℝ => (Real.exp (-(t / 4)) : ℂ) * Complex.cos (z * t))
      (Ioi 0) := by
    have hdom : IntegrableOn (fun t : ℝ => Real.exp (-(1 / 4 - |z.im|) * t)) (Ioi 0) :=
      integrableOn_exp_mul_Ioi (by linarith) 0
    refine hdom.mono' ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_id.div_const 4).neg)).mul (Complex.continuous_cos.comp
        (continuous_const.mul Complex.continuous_ofReal))).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-(t / 4)) * ‖Complex.cos (z * t)‖
        ≤ Real.exp (-(t / 4)) * Real.exp (|z.im| * t) :=
          mul_le_mul_of_nonneg_left (norm_ccos_mul_ofReal_le_of_nonneg z (le_of_lt ht))
            (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; ring_nf
  have hB : IntegrableOn (fun t : ℝ => (thetaRenewalLogKernel t : ℂ) *
      (Complex.cosh (I * z * t) * t)) (Ioi 0) := by
    have hdom := integrableOn_mul_exp_mul_thetaRenewalLogKernel hz
    refine hdom.mono' ((Complex.continuous_ofReal.comp continuous_thetaRenewalLogKernel).mul
      ((Complex.continuous_cosh.comp (continuous_const.mul Complex.continuous_ofReal)).mul
        Complex.continuous_ofReal)).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 ≤ t := le_of_lt ht
    rw [show I * z * t = (z * t) * I by ring, Complex.cosh_mul_I, norm_mul, norm_mul,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (thetaRenewalLogKernel_pos ht), abs_of_nonneg ht0]
    calc thetaRenewalLogKernel t * (‖Complex.cos (z * t)‖ * t)
        ≤ thetaRenewalLogKernel t * (Real.exp (|z.im| * t) * t) := by
          gcongr
          · exact (thetaRenewalLogKernel_pos ht).le
          · exact norm_ccos_mul_ofReal_le_of_nonneg z ht0
      _ = _ := by ring
  rw [← integral_exp_mul_ccos hz, ← integral_add hA hB]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [show I * z * t = (z * t) * I by ring, Complex.cosh_mul_I]
  simp only [thetaRenewalReflectionProfile, thetaRenewalMomentKernel]
  push_cast
  ring

theorem thetaRenewalReflectionProfile_mul_ccos_eq_integral {z : ℂ} (hz : |z.im| < 1 / 4)
    (hz0 : z ≠ 0) :
    ∫ t in Ioi (0 : ℝ), (thetaRenewalReflectionProfile t : ℂ) * Complex.cos (z * t) =
      ∫ t in Ioi (0 : ℝ), Complex.sin (z * t) / z * ((deriv thetaWaitingCDF t : ℝ) : ℂ) := by
  set b := |z.im|
  have hκ : 0 < 1 / 4 - b := by linarith
  set y := thetaRenewalReflectionProfile with hy
  have hM' := continuous_deriv_thetaWaitingCDF
  have hint2 : IntegrableOn (fun t : ℝ => Complex.sin (z * t) / z *
      ((deriv thetaWaitingCDF t : ℝ) : ℂ)) (Ioi 0) := by
    have hdom := (integrableOn_exp_mul_deriv_thetaWaitingCDF hz).const_mul (1 / ‖z‖)
    refine hdom.mono' (by fun_prop : Continuous fun t : ℝ => Complex.sin (z * t) / z *
      ((deriv thetaWaitingCDF t : ℝ) : ℂ)).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 ≤ t := le_of_lt ht
    have hM := deriv_thetaWaitingCDF_nonneg ht0
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hM]
    calc ‖Complex.sin (z * t)‖ / ‖z‖ * deriv thetaWaitingCDF t
        ≤ Real.exp (b * t) / ‖z‖ * deriv thetaWaitingCDF t := by
          gcongr; exact norm_csin_mul_ofReal_le_of_nonneg z ht0
      _ = _ := by ring
  have hparts : ∀ T : ℝ, 0 ≤ T → ∫ t in (0 : ℝ)..T, (y t : ℂ) * Complex.cos (z * t) =
      (y T : ℂ) * (Complex.sin (z * T) / z) +
        ∫ t in (0 : ℝ)..T, Complex.sin (z * t) / z * ((deriv thetaWaitingCDF t : ℝ) : ℂ) := by
    intro T _
    have hu : ∀ t, HasDerivAt (fun t : ℝ => (y t : ℂ)) (((-deriv thetaWaitingCDF t : ℝ)) : ℂ) t :=
      fun t => ((hasDerivAt_neg_thetaRenewalReflectionProfile t).neg.congr_of_eventuallyEq
        (Eventually.of_forall fun u => by simp [hy])).ofReal_comp
    have hv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.sin (z * t) / z) (Complex.cos (z * t)) t := by
      intro t
      have h := ((((hasDerivAt_id (t : ℂ)).const_mul z).csin).div_const z).comp_ofReal
      refine h.congr_deriv ?_
      simp only [id, mul_one]
      field_simp
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := T)
      (fun t _ => hu t) (fun t _ => hv t)
      ((Complex.continuous_ofReal.comp hM'.neg).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun t : ℝ => Complex.cos (z * t)).intervalIntegrable _ _)
    rw [h]
    have hint : ∫ t in (0 : ℝ)..T, (((-deriv thetaWaitingCDF t : ℝ)) : ℂ) *
        (Complex.sin (z * t) / z) =
        -∫ t in (0 : ℝ)..T, Complex.sin (z * t) / z * ((deriv thetaWaitingCDF t : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun t _ => ?_
      push_cast; ring
    rw [hint]
    simp
  have hL1 := intervalIntegral_tendsto_integral_Ioi 0 (integrableOn_reflectionProfile_mul_ccos hz)
    tendsto_id
  have hL2 := intervalIntegral_tendsto_integral_Ioi 0 hint2 tendsto_id
  have hbd : Tendsto (fun T : ℝ => (y T : ℂ) * (Complex.sin (z * T) / z)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun T : ℝ => 2 / ‖z‖ * Real.exp (-((1 / 4 - b) * T))) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
        (tendsto_id.const_mul_atTop hκ))).const_mul (2 / ‖z‖)
      rw [mul_zero] at this
      exact this
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 0] with T hT
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (thetaRenewalReflectionProfile_pos hT)]
    calc y T * (‖Complex.sin (z * T)‖ / ‖z‖)
        ≤ (2 * Real.exp (-(T / 4))) * (Real.exp (b * T) / ‖z‖) := by
          gcongr
          · exact thetaRenewalReflectionProfile_le_two_mul hT
          · exact norm_csin_mul_ofReal_le_of_nonneg z hT
      _ = 2 / ‖z‖ * Real.exp (-((1 / 4 - b) * T)) := by
          rw [show -((1 / 4 - b) * T) = -(T / 4) + b * T by ring, Real.exp_add]; ring
  have hlim := hbd.add hL2
  rw [zero_add] at hlim
  exact tendsto_nhds_unique (hL1.congr' ((eventually_ge_atTop 0).mono fun T hT =>
    (hparts T hT))) hlim

/-- **(14), probabilistic form.** For `z ≠ 0` in the strip, `Φ'(z) = ∫ sin(zT)/z μ(dT)`. -/
theorem hasDerivAt_thetaWaitingPhase_eq_expectation {z : ℂ} (hz : |z.im| < 1 / 4)
    (hz0 : z ≠ 0) :
    HasDerivAt thetaWaitingPhase (∫ t, Complex.sin (z * t) / z ∂thetaWaitingTimeLaw) z := by
  rw [integral_thetaWaitingTimeLaw, ← thetaRenewalReflectionProfile_mul_ccos_eq_integral hz hz0]
  exact hasDerivAt_thetaWaitingPhase hz

/-! ## The removable value `Φ'(0) = E[T]` -/

theorem integral_thetaWaitingTimeLaw_real (g : ℝ → ℝ) :
    ∫ t, g t ∂thetaWaitingTimeLaw = ∫ t in Ioi (0 : ℝ), g t * deriv thetaWaitingCDF t := by
  rw [thetaWaitingTimeLaw, integral_withDensity_eq_integral_toReal_smul
    continuous_deriv_thetaWaitingCDF.measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [ENNReal.toReal_ofReal (deriv_thetaWaitingCDF_nonneg (le_of_lt ht)), smul_eq_mul, mul_comm]

/-- The mean waiting time is the integral of the survival function: `E[T] = ∫₀^∞ s`. -/
theorem integral_id_thetaWaitingTimeLaw :
    ∫ t, t ∂thetaWaitingTimeLaw = ∫ t in Ioi (0 : ℝ), thetaRenewalReflectionProfile t := by
  set y := thetaRenewalReflectionProfile with hy
  have hM' := continuous_deriv_thetaWaitingCDF
  have hint1 : IntegrableOn (fun t => t * deriv thetaWaitingCDF t) (Ioi 0) := by
    have hdom := (integrableOn_exp_mul_deriv_thetaWaitingCDF (σ := 1 / 8) (by norm_num)).const_mul
      (1 / (1 / 8 - 0))
    refine hdom.mono' (by fun_prop : Continuous fun t : ℝ =>
      t * deriv thetaWaitingCDF t).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 ≤ t := le_of_lt ht
    have hM := deriv_thetaWaitingCDF_nonneg ht0
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht0 hM)]
    have h := mul_exp_le_exp_div (b := 0) (σ := 1 / 8) (by norm_num) t
    simp only [zero_mul, Real.exp_zero, mul_one] at h
    calc t * deriv thetaWaitingCDF t ≤ Real.exp (1 / 8 * t) / (1 / 8 - 0) * deriv thetaWaitingCDF t :=
          mul_le_mul_of_nonneg_right h hM
      _ = _ := by ring
  have hparts : ∀ T : ℝ, 0 ≤ T → ∫ t in (0 : ℝ)..T, t * deriv thetaWaitingCDF t =
      -(T * y T) + ∫ t in (0 : ℝ)..T, y t := by
    intro T _
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := T)
      (u := fun t : ℝ => t) (u' := fun _ => 1) (v := fun t => -y t)
      (fun t _ => hasDerivAt_id t) (fun t _ => hasDerivAt_neg_thetaRenewalReflectionProfile t)
      intervalIntegrable_const (hM'.intervalIntegrable _ _)
    rw [h]
    simp only [one_mul, zero_mul, sub_zero, intervalIntegral.integral_neg]
    ring
  have hL1 := intervalIntegral_tendsto_integral_Ioi 0 hint1 tendsto_id
  have hL2 := intervalIntegral_tendsto_integral_Ioi 0 integrableOn_thetaRenewalReflectionProfile
    tendsto_id
  have hbd : Tendsto (fun T : ℝ => T * y T) atTop (𝓝 0) := by
    have hdom := (tendsto_mul_exp_neg_mul_atTop (κ := 1 / 4) (by norm_num)).const_mul 2
    rw [mul_zero] at hdom
    refine squeeze_zero' ?_ ?_ hdom
    · filter_upwards [eventually_ge_atTop 0] with T hT
      exact mul_nonneg hT (thetaRenewalReflectionProfile_pos hT).le
    · filter_upwards [eventually_ge_atTop 0] with T hT
      calc T * y T ≤ T * (2 * Real.exp (-(T / 4))) :=
            mul_le_mul_of_nonneg_left (thetaRenewalReflectionProfile_le_two_mul hT) hT
        _ = 2 * (T * Real.exp (-(1 / 4 * T))) := by ring_nf
  have hlim := hbd.neg.add hL2
  rw [neg_zero, zero_add] at hlim
  rw [integral_thetaWaitingTimeLaw_real]
  exact tendsto_nhds_unique (hL1.congr' ((eventually_ge_atTop 0).mono fun T hT =>
    (hparts T hT))) hlim

theorem integral_id_thetaWaitingTimeLaw_pos : 0 < ∫ t, t ∂thetaWaitingTimeLaw := by
  rw [integral_id_thetaWaitingTimeLaw]
  exact setIntegral_Ioi_pos integrableOn_thetaRenewalReflectionProfile fun t ht =>
    thetaRenewalReflectionProfile_pos ht.le

/-- **The removable value.** `Φ'(0) = ∫ T μ(dT) > 0`. -/
theorem hasDerivAt_thetaWaitingPhase_zero :
    HasDerivAt thetaWaitingPhase ((∫ t, t ∂thetaWaitingTimeLaw : ℝ) : ℂ) 0 := by
  have h := hasDerivAt_thetaWaitingPhase (z := 0) (by simp)
  simp only [zero_mul, Complex.cos_zero, mul_one] at h
  rw [integral_id_thetaWaitingTimeLaw, ← integral_complex_ofReal]
  exact h

/-! ## Positive definiteness on the real axis -/

/-- The real-frequency phase slope `Φ'(τ) = ∫₀^∞ s(t) cos(τt) dt`. -/
def thetaWaitingPhaseSlope (τ : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), thetaRenewalReflectionProfile t * Real.cos (τ * t)

theorem integrableOn_reflectionProfile_mul_cos (τ : ℝ) :
    IntegrableOn (fun t => thetaRenewalReflectionProfile t * Real.cos (τ * t)) (Ioi 0) := by
  refine integrableOn_thetaRenewalReflectionProfile.mono' ((continuous_thetaRenewalReflectionProfile.mul
    (by fun_prop : Continuous fun t : ℝ => Real.cos (τ * t))).aestronglyMeasurable) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (thetaRenewalReflectionProfile_pos (le_of_lt ht))]
  exact mul_le_of_le_one_right (thetaRenewalReflectionProfile_pos (le_of_lt ht)).le
    (Real.abs_cos_le_one _)

theorem hasDerivAt_thetaWaitingPhase_ofReal (τ : ℝ) :
    HasDerivAt thetaWaitingPhase (thetaWaitingPhaseSlope τ : ℂ) τ := by
  have h := hasDerivAt_thetaWaitingPhase (z := τ) (by simp)
  convert h using 1
  rw [thetaWaitingPhaseSlope, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  push_cast
  ring_nf

/-- `‖Σ c_j e^{iθ_j}‖² = Σ_j Σ_k c_j c̄_k e^{i(θ_j - θ_k)}`. -/
theorem sq_norm_sum_mul_exp {n : ℕ} (c : Fin n → ℂ) (θ : Fin n → ℝ) :
    ((‖∑ j, c j * Complex.exp (θ j * I)‖ ^ 2 : ℝ) : ℂ) =
      ∑ j, ∑ k, c j * (starRingEnd ℂ) (c k) * Complex.exp (((θ j - θ k : ℝ) : ℂ) * I) := by
  rw [Complex.sq_norm, ← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
    show (((θ j - θ k : ℝ)) : ℂ) * I = θ j * I + θ k * -I by push_cast; ring, Complex.exp_add]
  ring

/-- The cosine kernel is a sum of two squares: `Σ c_j c̄_k cos((τ_j - τ_k)t) =
(‖Σ c_j e^{iτ_j t}‖² + ‖Σ c_j e^{-iτ_j t}‖²)/2`. -/
theorem sum_sum_mul_conj_mul_cos {n : ℕ} (c : Fin n → ℂ) (τ : Fin n → ℝ) (t : ℝ) :
    ∑ j, ∑ k, c j * (starRingEnd ℂ) (c k) * (Real.cos ((τ j - τ k) * t) : ℂ) =
      (((‖∑ j, c j * Complex.exp ((τ j * t : ℝ) * I)‖ ^ 2 +
        ‖∑ j, c j * Complex.exp ((-(τ j * t) : ℝ) * I)‖ ^ 2) / 2 : ℝ) : ℂ) := by
  have h1 := sq_norm_sum_mul_exp c fun j => τ j * t
  have h2 := sq_norm_sum_mul_exp c fun j => -(τ j * t)
  push_cast at h1 h2 ⊢
  rw [h1, h2, ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.cos]
  ring_nf

/-- **Positive definiteness (14).** On the real axis `Φ'` is a positive-definite function:
`Σ_j Σ_k c_j c̄_k Φ'(τ_j - τ_k) = ∫₀^∞ s(t) (‖Σ c_j e^{iτ_j t}‖² + ‖Σ c_j e^{-iτ_j t}‖²)/2 dt ≥ 0`. -/
theorem sum_sum_mul_conj_mul_thetaWaitingPhaseSlope {n : ℕ} (c : Fin n → ℂ) (τ : Fin n → ℝ) :
    ∑ j, ∑ k, c j * (starRingEnd ℂ) (c k) * (thetaWaitingPhaseSlope (τ j - τ k) : ℂ) =
      ((∫ t in Ioi (0 : ℝ), thetaRenewalReflectionProfile t *
        ((‖∑ j, c j * Complex.exp ((τ j * t : ℝ) * I)‖ ^ 2 +
          ‖∑ j, c j * Complex.exp ((-(τ j * t) : ℝ) * I)‖ ^ 2) / 2)) : ℝ) := by
  have hint : ∀ j k, Integrable (fun t : ℝ => c j * (starRingEnd ℂ) (c k) *
      ((thetaRenewalReflectionProfile t * Real.cos ((τ j - τ k) * t) : ℝ) : ℂ))
      (volume.restrict (Ioi 0)) := fun j k =>
    ((integrableOn_reflectionProfile_mul_cos (τ j - τ k)).ofReal).const_mul _
  rw [← integral_complex_ofReal]
  have hpt : ∀ t : ℝ, (((thetaRenewalReflectionProfile t *
      ((‖∑ j, c j * Complex.exp ((τ j * t : ℝ) * I)‖ ^ 2 +
        ‖∑ j, c j * Complex.exp ((-(τ j * t) : ℝ) * I)‖ ^ 2) / 2)) : ℝ) : ℂ) =
      ∑ j, ∑ k, c j * (starRingEnd ℂ) (c k) *
        ((thetaRenewalReflectionProfile t * Real.cos ((τ j - τ k) * t) : ℝ) : ℂ) := by
    intro t
    rw [Complex.ofReal_mul, ← sum_sum_mul_conj_mul_cos, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast; ring
  simp_rw [hpt]
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hint j k]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ fun k _ => hint j k]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, integral_complex_ofReal, thetaWaitingPhaseSlope]

theorem sum_sum_mul_conj_mul_thetaWaitingPhaseSlope_nonneg {n : ℕ} (c : Fin n → ℂ)
    (τ : Fin n → ℝ) :
    0 ≤ (∑ j, ∑ k, c j * (starRingEnd ℂ) (c k) * (thetaWaitingPhaseSlope (τ j - τ k) : ℂ)).re ∧
      (∑ j, ∑ k, c j * (starRingEnd ℂ) (c k) *
        (thetaWaitingPhaseSlope (τ j - τ k) : ℂ)).im = 0 := by
  rw [sum_sum_mul_conj_mul_thetaWaitingPhaseSlope, Complex.ofReal_re, Complex.ofReal_im]
  refine ⟨setIntegral_nonneg measurableSet_Ioi fun t ht => mul_nonneg
    (thetaRenewalReflectionProfile_pos (le_of_lt ht)).le (by positivity), rfl⟩

/-- `Φ'` on the real axis is the Fourier (cosine) transform of the even density `s(|t|)/2`. -/
theorem thetaWaitingPhaseSlope_eq_integral_abs (τ : ℝ) :
    thetaWaitingPhaseSlope τ =
      ∫ t : ℝ, thetaRenewalReflectionProfile |t| / 2 * Real.cos (τ * t) := by
  have h := integral_comp_abs (f := fun t => thetaRenewalReflectionProfile t / 2 * Real.cos (τ * t))
  have hcos : ∀ t : ℝ, Real.cos (τ * |t|) = Real.cos (τ * t) := fun t => by
    rcases abs_cases t with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [h1]
    · rw [h1, mul_neg, Real.cos_neg]
  simp only [hcos] at h
  rw [h, thetaWaitingPhaseSlope, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  ring

theorem integrable_thetaRenewalReflectionProfile_abs :
    Integrable fun t : ℝ => thetaRenewalReflectionProfile |t| := by
  have hF : Integrable ((Ioi (0 : ℝ)).indicator thetaRenewalReflectionProfile) :=
    (integrable_indicator_iff measurableSet_Ioi).mpr integrableOn_thetaRenewalReflectionProfile
  refine (hF.add hF.comp_neg).congr ?_
  have hne : ∀ᵐ t : ℝ, t ≠ 0 := ae_iff.mpr (by simp)
  filter_upwards [hne] with t ht
  rcases lt_or_gt_of_ne ht with h | h
  · rw [Pi.add_apply, Set.indicator_of_notMem (by simpa using h.le),
      Set.indicator_of_mem (by simpa using h), abs_of_neg h, zero_add]
  · rw [Pi.add_apply, Set.indicator_of_mem (by simpa using h),
      Set.indicator_of_notMem (by simpa using h.le), abs_of_pos h, add_zero]

/-- `Φ'(τ)` is the Fourier transform of the finite nonnegative even density `s(|t|)/2`. -/
theorem thetaWaitingPhaseSlope_eq_fourier (τ : ℝ) :
    (thetaWaitingPhaseSlope τ : ℂ) = ∫ t : ℝ,
      ((thetaRenewalReflectionProfile |t| / 2 : ℝ) : ℂ) * Complex.exp ((τ * t : ℝ) * I) := by
  have hg := integrable_thetaRenewalReflectionProfile_abs.div_const 2
  have hmeas : AEStronglyMeasurable (fun t : ℝ => thetaRenewalReflectionProfile |t| / 2) volume :=
    hg.aestronglyMeasurable
  have hcos : Integrable fun t : ℝ => thetaRenewalReflectionProfile |t| / 2 * Real.cos (τ * t) := by
    refine hg.mono' (hmeas.mul (by fun_prop : Continuous fun t : ℝ =>
      Real.cos (τ * t)).aestronglyMeasurable) (Eventually.of_forall fun t => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)).trans_eq
      (abs_of_nonneg (div_nonneg (thetaRenewalReflectionProfile_pos (abs_nonneg t)).le
        zero_le_two))
  have hsin : Integrable fun t : ℝ => thetaRenewalReflectionProfile |t| / 2 * Real.sin (τ * t) := by
    refine hg.mono' (hmeas.mul (by fun_prop : Continuous fun t : ℝ =>
      Real.sin (τ * t)).aestronglyMeasurable) (Eventually.of_forall fun t => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)).trans_eq
      (abs_of_nonneg (div_nonneg (thetaRenewalReflectionProfile_pos (abs_nonneg t)).le
        zero_le_two))
  have hodd : ∫ t : ℝ, thetaRenewalReflectionProfile |t| / 2 * Real.sin (τ * t) = 0 := by
    have h := integral_neg_eq_self (fun t : ℝ =>
      thetaRenewalReflectionProfile |t| / 2 * Real.sin (τ * t)) volume
    simp only [abs_neg, mul_neg, Real.sin_neg, integral_neg] at h
    linarith
  have e : ∀ t : ℝ, ((thetaRenewalReflectionProfile |t| / 2 : ℝ) : ℂ) *
      Complex.exp ((τ * t : ℝ) * I) =
      ((thetaRenewalReflectionProfile |t| / 2 * Real.cos (τ * t) : ℝ) : ℂ) +
        ((thetaRenewalReflectionProfile |t| / 2 * Real.sin (τ * t) : ℝ) : ℂ) * I := by
    intro t
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast
    ring
  have hA : Integrable (fun t : ℝ =>
      ((thetaRenewalReflectionProfile |t| / 2 * Real.cos (τ * t) : ℝ) : ℂ)) := hcos.ofReal
  have hB : Integrable (fun t : ℝ =>
      ((thetaRenewalReflectionProfile |t| / 2 * Real.sin (τ * t) : ℝ) : ℂ) * I) :=
    (hsin.ofReal (𝕜 := ℂ)).mul_const I
  simp_rw [e]
  rw [integral_add hA hB, integral_mul_const,
    integral_complex_ofReal, integral_complex_ofReal, hodd, thetaWaitingPhaseSlope_eq_integral_abs]
  simp

end RHTower
