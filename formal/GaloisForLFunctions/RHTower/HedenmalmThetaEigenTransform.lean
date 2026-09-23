import GaloisForLFunctions.RHTower.HedenmalmThetaEigenODE

/-!
# The theta eigenfunction and its removable quotient

The time-side eigenfunction of the Hedenmalm equation is exponentially localized exactly at a zero
of `XiC`: on the left half-line the causal source-pointed inverse decays like `exp x` and on the
right half-line the anti-causal one decays like `exp (-x)`, and at a zero the two coincide, so the
single solution has both decays.

Integrating the eigenfunction equation against the free mode over the whole line then costs no
boundary terms, and the transform satisfies the pole-free identity

  `(alpha + z) * F(alpha, z) = -XiC z`.

Away from the reflected zero this is the Fourier-side removable quotient `i Xi(z)/(z + alpha)`
already carried by the corpus, so the time-side eigenfunction and the entire quotient used in the
Weil polarization are the same object seen through the transform.
-/

open Complex Real MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section


theorem abs_thetaCuspFullSource_le_expConstant (x : ℝ) :
    |thetaCuspFullSource x| ≤ thetaCuspDerivativeExpConstant 0 * Real.exp (-|x|) := by
  have h := abs_iteratedDeriv_thetaCuspFullSource_le_exp_neg_abs 0 x
  rwa [iteratedDeriv_zero] at h

theorem norm_hedenmalmVolterraIntegrand_eq (α : ℂ) (x t : ℝ) :
    ‖hedenmalmVolterraIntegrand α x t‖ =
      |thetaCuspFullSource t| * Real.exp (α.im * (x - t)) := by
  rw [hedenmalmVolterraIntegrand, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
  congr 1
  simp

/-- On the left half-line the causal source-pointed inverse decays exponentially. -/
theorem norm_hedenmalmCausalVolterra_le_of_nonpos {α : ℂ} (hα : |α.im| < 1) {x : ℝ} (hx : x ≤ 0) :
    ‖hedenmalmCausalVolterra α x‖ ≤
      thetaCuspDerivativeExpConstant 0 / (1 - α.im) * Real.exp x := by
  have hb : α.im < 1 := (abs_lt.mp hα).2
  have hpos : (0 : ℝ) < 1 - α.im := by linarith
  set C : ℝ := thetaCuspDerivativeExpConstant 0 with hC
  have hCnn : 0 ≤ C := thetaCuspDerivativeExpConstant_nonneg 0
  have hmaj : IntegrableOn
      (fun t : ℝ => C * Real.exp (α.im * x) * Real.exp ((1 - α.im) * t)) (Iic x) :=
    ((integrableOn_exp_mul_Iic hpos x).const_mul _)
  have hbound : ∀ t ∈ Iic x, ‖hedenmalmVolterraIntegrand α x t‖ ≤
      C * Real.exp (α.im * x) * Real.exp ((1 - α.im) * t) := by
    intro t ht
    rw [norm_hedenmalmVolterraIntegrand_eq]
    have htx : t ≤ x := ht
    have ht0 : t ≤ 0 := le_trans htx hx
    have hk : |thetaCuspFullSource t| ≤ C * Real.exp t := by
      have h := abs_thetaCuspFullSource_le_expConstant t
      rwa [abs_of_nonpos ht0, neg_neg] at h
    have hexp : t + α.im * (x - t) = α.im * x + (1 - α.im) * t := by ring
    calc |thetaCuspFullSource t| * Real.exp (α.im * (x - t))
        ≤ (C * Real.exp t) * Real.exp (α.im * (x - t)) :=
          mul_le_mul_of_nonneg_right hk (Real.exp_pos _).le
      _ = C * Real.exp (α.im * x) * Real.exp ((1 - α.im) * t) := by
          rw [mul_assoc, ← Real.exp_add, hexp, Real.exp_add, ← mul_assoc]
  calc ‖hedenmalmCausalVolterra α x‖
      = ‖∫ t in Iic x, hedenmalmVolterraIntegrand α x t‖ := by
        rw [hedenmalmCausalVolterra, norm_mul, norm_neg, Complex.norm_I, one_mul]
    _ ≤ ∫ t in Iic x, ‖hedenmalmVolterraIntegrand α x t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Iic x, C * Real.exp (α.im * x) * Real.exp ((1 - α.im) * t) :=
        setIntegral_mono_on
          (integrable_hedenmalmVolterraIntegrand hα x).norm.integrableOn hmaj measurableSet_Iic
          hbound
    _ = C * Real.exp (α.im * x) * (Real.exp ((1 - α.im) * x) / (1 - α.im)) := by
        rw [MeasureTheory.integral_const_mul, integral_exp_mul_Iic hpos]
    _ = C / (1 - α.im) * Real.exp x := by
        have hx2 : Real.exp (α.im * x) * Real.exp ((1 - α.im) * x) = Real.exp x := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [div_eq_mul_inv, div_eq_mul_inv]
        calc C * Real.exp (α.im * x) * (Real.exp ((1 - α.im) * x) * (1 - α.im)⁻¹)
            = C * (Real.exp (α.im * x) * Real.exp ((1 - α.im) * x)) * (1 - α.im)⁻¹ := by ring
          _ = C * Real.exp x * (1 - α.im)⁻¹ := by rw [hx2]
          _ = C * (1 - α.im)⁻¹ * Real.exp x := by ring


/-- On the right half-line the anti-causal source-pointed inverse decays exponentially. -/
theorem norm_hedenmalmAntiCausalVolterra_le_of_nonneg {α : ℂ} (hα : |α.im| < 1) {x : ℝ}
    (hx : 0 ≤ x) :
    ‖hedenmalmAntiCausalVolterra α x‖ ≤
      thetaCuspDerivativeExpConstant 0 / (1 + α.im) * Real.exp (-x) := by
  have hb : -1 < α.im := (abs_lt.mp hα).1
  have hpos : (0 : ℝ) < 1 + α.im := by linarith
  set C : ℝ := thetaCuspDerivativeExpConstant 0 with hC
  have hCnn : 0 ≤ C := thetaCuspDerivativeExpConstant_nonneg 0
  have hmaj : IntegrableOn
      (fun t : ℝ => C * Real.exp (α.im * x) * Real.exp (-(1 + α.im) * t)) (Ioi x) :=
    ((integrableOn_exp_mul_Ioi (by linarith : -(1 + α.im) < 0) x).const_mul _)
  have hbound : ∀ t ∈ Ioi x, ‖hedenmalmVolterraIntegrand α x t‖ ≤
      C * Real.exp (α.im * x) * Real.exp (-(1 + α.im) * t) := by
    intro t ht
    rw [norm_hedenmalmVolterraIntegrand_eq]
    have ht0 : 0 ≤ t := le_trans hx (le_of_lt ht)
    have hk : |thetaCuspFullSource t| ≤ C * Real.exp (-t) := by
      have h := abs_thetaCuspFullSource_le_expConstant t
      rwa [abs_of_nonneg ht0] at h
    have hexp : -t + α.im * (x - t) = α.im * x + -(1 + α.im) * t := by ring
    calc |thetaCuspFullSource t| * Real.exp (α.im * (x - t))
        ≤ (C * Real.exp (-t)) * Real.exp (α.im * (x - t)) :=
          mul_le_mul_of_nonneg_right hk (Real.exp_pos _).le
      _ = C * Real.exp (α.im * x) * Real.exp (-(1 + α.im) * t) := by
          rw [mul_assoc, ← Real.exp_add, hexp, Real.exp_add, ← mul_assoc]
  calc ‖hedenmalmAntiCausalVolterra α x‖
      = ‖∫ t in Ioi x, hedenmalmVolterraIntegrand α x t‖ := by
        rw [hedenmalmAntiCausalVolterra, MeasureTheory.integral_Ici_eq_integral_Ioi, norm_mul,
          Complex.norm_I, one_mul]
    _ ≤ ∫ t in Ioi x, ‖hedenmalmVolterraIntegrand α x t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi x, C * Real.exp (α.im * x) * Real.exp (-(1 + α.im) * t) :=
        setIntegral_mono_on
          (integrable_hedenmalmVolterraIntegrand hα x).norm.integrableOn hmaj measurableSet_Ioi
          hbound
    _ = C * Real.exp (α.im * x) * (-Real.exp (-(1 + α.im) * x) / -(1 + α.im)) := by
        rw [MeasureTheory.integral_const_mul,
          integral_exp_mul_Ioi (by linarith : -(1 + α.im) < 0)]
    _ = C / (1 + α.im) * Real.exp (-x) := by
        have hx2 : Real.exp (α.im * x) * Real.exp (-(1 + α.im) * x) = Real.exp (-x) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [neg_div_neg_eq, div_eq_mul_inv, div_eq_mul_inv]
        calc C * Real.exp (α.im * x) * (Real.exp (-(1 + α.im) * x) * (1 + α.im)⁻¹)
            = C * (Real.exp (α.im * x) * Real.exp (-(1 + α.im) * x)) * (1 + α.im)⁻¹ := by ring
          _ = C * Real.exp (-x) * (1 + α.im)⁻¹ := by rw [hx2]
          _ = C * (1 + α.im)⁻¹ * Real.exp (-x) := by ring

/-- **The theta eigenfunction is exponentially localized.**  At a zero of `XiC` the two
source-pointed inverses coincide, so the single solution inherits the causal decay on the left and
the anti-causal decay on the right. -/
theorem norm_hedenmalmCausalVolterra_le_of_XiC_eq_zero {α : ℂ} (hα : |α.im| < 1)
    (h0 : XiC α = 0) (x : ℝ) :
    ‖hedenmalmCausalVolterra α x‖ ≤
      thetaCuspDerivativeExpConstant 0 / (1 - |α.im|) * Real.exp (-|x|) := by
  have hCnn : 0 ≤ thetaCuspDerivativeExpConstant 0 := thetaCuspDerivativeExpConstant_nonneg 0
  have habs : |α.im| < 1 := hα
  have hden : (0 : ℝ) < 1 - |α.im| := by linarith
  rcases le_or_gt x 0 with hx | hx
  · have h := norm_hedenmalmCausalVolterra_le_of_nonpos hα hx
    have hle : thetaCuspDerivativeExpConstant 0 / (1 - α.im) ≤
        thetaCuspDerivativeExpConstant 0 / (1 - |α.im|) := by
      apply div_le_div_of_nonneg_left hCnn hden
      have := neg_abs_le α.im
      have := le_abs_self α.im
      linarith
    calc ‖hedenmalmCausalVolterra α x‖
        ≤ thetaCuspDerivativeExpConstant 0 / (1 - α.im) * Real.exp x := h
      _ ≤ thetaCuspDerivativeExpConstant 0 / (1 - |α.im|) * Real.exp x := by
          exact mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
      _ = thetaCuspDerivativeExpConstant 0 / (1 - |α.im|) * Real.exp (-|x|) := by
          rw [abs_of_nonpos hx, neg_neg]
  · have heq := (hedenmalmCausalVolterra_eq_antiCausal_iff hα).mpr h0 x
    have h := norm_hedenmalmAntiCausalVolterra_le_of_nonneg hα (le_of_lt hx)
    have hle : thetaCuspDerivativeExpConstant 0 / (1 + α.im) ≤
        thetaCuspDerivativeExpConstant 0 / (1 - |α.im|) := by
      apply div_le_div_of_nonneg_left hCnn hden
      have := neg_abs_le α.im
      linarith
    calc ‖hedenmalmCausalVolterra α x‖
        = ‖hedenmalmAntiCausalVolterra α x‖ := by rw [heq]
      _ ≤ thetaCuspDerivativeExpConstant 0 / (1 + α.im) * Real.exp (-x) := h
      _ ≤ thetaCuspDerivativeExpConstant 0 / (1 - |α.im|) * Real.exp (-x) := by
          exact mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
      _ = thetaCuspDerivativeExpConstant 0 / (1 - |α.im|) * Real.exp (-|x|) := by
          rw [abs_of_pos hx]


/-- The Fourier--Laplace transform of the time-side theta eigenfunction. -/
def hedenmalmThetaEigenTransform (α z : ℂ) : ℂ :=
  ∫ x : ℝ, hedenmalmCausalVolterra α x * Complex.exp (-I * z * (x : ℂ))

theorem norm_hedenmalmThetaEigen_mul_exp (α z : ℂ) (x : ℝ) :
    ‖hedenmalmCausalVolterra α x * Complex.exp (-I * z * (x : ℂ))‖ =
      ‖hedenmalmCausalVolterra α x‖ * Real.exp (z.im * x) := by
  rw [norm_mul, Complex.norm_exp]
  congr 2
  simp

theorem continuous_hedenmalmCausalVolterra {α : ℂ} (hα : |α.im| < 1) :
    Continuous (hedenmalmCausalVolterra α) :=
  continuous_iff_continuousAt.mpr fun x =>
    (hasDerivAt_hedenmalmCausalVolterra hα x).continuousAt

theorem norm_hedenmalmThetaEigen_mul_exp_le {α : ℂ} (hα : |α.im| < 1) (h0 : XiC α = 0)
    (z : ℂ) (x : ℝ) :
    ‖hedenmalmCausalVolterra α x * Complex.exp (-I * z * (x : ℂ))‖ ≤
      thetaCuspDerivativeExpConstant 0 / (1 - |α.im|) *
        Real.exp (-(1 - |z.im|) * |x|) := by
  have hCnn : 0 ≤ thetaCuspDerivativeExpConstant 0 := thetaCuspDerivativeExpConstant_nonneg 0
  have hden : (0 : ℝ) < 1 - |α.im| := by linarith [hα]
  have hK : (0 : ℝ) ≤ thetaCuspDerivativeExpConstant 0 / (1 - |α.im|) := by positivity
  rw [norm_hedenmalmThetaEigen_mul_exp]
  have hu := norm_hedenmalmCausalVolterra_le_of_XiC_eq_zero hα h0 x
  have hexp : z.im * x ≤ |z.im| * |x| := by
    calc z.im * x ≤ |z.im * x| := le_abs_self _
      _ = |z.im| * |x| := abs_mul _ _
  calc ‖hedenmalmCausalVolterra α x‖ * Real.exp (z.im * x)
      ≤ (thetaCuspDerivativeExpConstant 0 / (1 - |α.im|) * Real.exp (-|x|)) *
          Real.exp (|z.im| * |x|) := by
        exact mul_le_mul hu (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le (by positivity)
    _ = thetaCuspDerivativeExpConstant 0 / (1 - |α.im|) * Real.exp (-(1 - |z.im|) * |x|) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring

theorem integrable_hedenmalmThetaEigen_mul_exp {α : ℂ} (hα : |α.im| < 1) (h0 : XiC α = 0)
    {z : ℂ} (hz : |z.im| < 1) :
    Integrable (fun x : ℝ => hedenmalmCausalVolterra α x * Complex.exp (-I * z * (x : ℂ))) := by
  have hc : (0 : ℝ) < 1 - |z.im| := by linarith [hz]
  have hbase : Integrable (fun x : ℝ => Real.exp (-(1 - |z.im|) * |x|)) := by
    simpa using integrable_abs_pow_mul_exp_neg_mul_abs 0 hc
  refine Integrable.mono'
    (hbase.const_mul (thetaCuspDerivativeExpConstant 0 / (1 - |α.im|))) ?_ ?_
  · exact ((continuous_hedenmalmCausalVolterra hα).mul
      (by fun_prop : Continuous fun x : ℝ => Complex.exp (-I * z * (x : ℂ)))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x => norm_hedenmalmThetaEigen_mul_exp_le hα h0 z x

theorem tendsto_hedenmalmThetaEigen_mul_exp_atTop {α : ℂ} (hα : |α.im| < 1) (h0 : XiC α = 0)
    {z : ℂ} (hz : |z.im| < 1) :
    Filter.Tendsto (fun x : ℝ => hedenmalmCausalVolterra α x * Complex.exp (-I * z * (x : ℂ)))
      atTop (nhds 0) := by
  have hc : (0 : ℝ) < 1 - |z.im| := by linarith [hz]
  refine squeeze_zero_norm (fun x => norm_hedenmalmThetaEigen_mul_exp_le hα h0 z x) ?_
  have habs : Filter.Tendsto (fun x : ℝ => -(1 - |z.im|) * |x|) atTop atBot := by
    have h1 : Filter.Tendsto (fun x : ℝ => (1 - |z.im|) * |x|) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hc tendsto_abs_atTop_atTop
    simpa only [neg_mul, Function.comp_def] using Filter.tendsto_neg_atTop_atBot.comp h1
  simpa using (Real.tendsto_exp_atBot.comp habs).const_mul
    (thetaCuspDerivativeExpConstant 0 / (1 - |α.im|))

theorem tendsto_hedenmalmThetaEigen_mul_exp_atBot {α : ℂ} (hα : |α.im| < 1) (h0 : XiC α = 0)
    {z : ℂ} (hz : |z.im| < 1) :
    Filter.Tendsto (fun x : ℝ => hedenmalmCausalVolterra α x * Complex.exp (-I * z * (x : ℂ)))
      atBot (nhds 0) := by
  have hc : (0 : ℝ) < 1 - |z.im| := by linarith [hz]
  refine squeeze_zero_norm (fun x => norm_hedenmalmThetaEigen_mul_exp_le hα h0 z x) ?_
  have habs : Filter.Tendsto (fun x : ℝ => -(1 - |z.im|) * |x|) atBot atBot := by
    have h1 : Filter.Tendsto (fun x : ℝ => (1 - |z.im|) * |x|) atBot atTop :=
      Filter.Tendsto.const_mul_atTop hc tendsto_abs_atBot_atTop
    simpa only [neg_mul, Function.comp_def] using Filter.tendsto_neg_atTop_atBot.comp h1
  simpa using (Real.tendsto_exp_atBot.comp habs).const_mul
    (thetaCuspDerivativeExpConstant 0 / (1 - |α.im|))


theorem hasDerivAt_hedenmalmThetaEigen_mul_exp {α : ℂ} (hα : |α.im| < 1) (z : ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => hedenmalmCausalVolterra α y * Complex.exp (-I * z * (y : ℂ)))
      ((-I * (α + z) * hedenmalmCausalVolterra α x - I * (thetaCuspFullSource x : ℂ)) *
        Complex.exp (-I * z * (x : ℂ))) x := by
  have hu := hasDerivAt_hedenmalmCausalVolterra hα x
  have hE : HasDerivAt (fun y : ℝ => Complex.exp (-I * z * (y : ℂ)))
      (-I * z * Complex.exp (-I * z * (x : ℂ))) x := by
    have h0 : HasDerivAt (fun w : ℂ => -I * z * w) (-I * z) (x : ℂ) := by
      simpa using (hasDerivAt_id ((x : ℝ) : ℂ)).const_mul (-I * z)
    have h2 := (h0.cexp).comp_ofReal
    refine h2.congr_deriv ?_
    ring
  refine (hu.mul hE).congr_deriv ?_
  ring

/-- **(18): the transform of the time-side eigenfunction is the removable quotient.**  Integrating
the eigenfunction equation against the free mode over the whole line, with no boundary terms because
the eigenfunction is exponentially localized, gives the pole-free identity. -/
theorem mul_hedenmalmThetaEigenTransform {α : ℂ} (hα : |α.im| < 1) (h0 : XiC α = 0)
    {z : ℂ} (hz : |z.im| < 1) :
    (α + z) * hedenmalmThetaEigenTransform α z = -XiC z := by
  have hIu : Integrable
      (fun x : ℝ => hedenmalmCausalVolterra α x * Complex.exp (-I * z * (x : ℂ))) :=
    integrable_hedenmalmThetaEigen_mul_exp hα h0 hz
  have hIk : Integrable
      (fun x : ℝ => (thetaCuspFullSource x : ℂ) * Complex.exp (-I * z * (x : ℂ))) :=
    (integrable_thetaCuspFourierLaplaceIntegrand hz).congr
      (Filter.Eventually.of_forall fun x => by
        rw [thetaCuspFourierLaplaceIntegrand]
        ring)
  have hFL : thetaCuspFourierLaplace z =
      ∫ x : ℝ, (thetaCuspFullSource x : ℂ) * Complex.exp (-I * z * (x : ℂ)) := by
    rw [thetaCuspFourierLaplace]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    rw [thetaCuspFourierLaplaceIntegrand]
    ring
  have h1 := hIu.const_mul (-I * (α + z))
  have h2 := hIk.const_mul I
  have hderivInt : Integrable (fun x : ℝ =>
      (-I * (α + z) * hedenmalmCausalVolterra α x - I * (thetaCuspFullSource x : ℂ)) *
        Complex.exp (-I * z * (x : ℂ))) :=
    (h1.sub h2).congr (Filter.Eventually.of_forall fun x => by
      simp only [Pi.sub_apply]
      ring)
  have hzero := MeasureTheory.integral_of_hasDerivAt_of_tendsto
    (fun x => hasDerivAt_hedenmalmThetaEigen_mul_exp hα z x) hderivInt
    (tendsto_hedenmalmThetaEigen_mul_exp_atBot hα h0 hz)
    (tendsto_hedenmalmThetaEigen_mul_exp_atTop hα h0 hz)
  rw [sub_zero] at hzero
  have hsplit : (∫ x : ℝ,
      (-I * (α + z) * hedenmalmCausalVolterra α x - I * (thetaCuspFullSource x : ℂ)) *
        Complex.exp (-I * z * (x : ℂ))) =
      -I * (α + z) * hedenmalmThetaEigenTransform α z -
        I * ∫ x : ℝ, (thetaCuspFullSource x : ℂ) * Complex.exp (-I * z * (x : ℂ)) := by
    rw [hedenmalmThetaEigenTransform,
      ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul,
      ← MeasureTheory.integral_sub h1 h2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  rw [hsplit, ← hFL] at hzero
  have hmem : z ∈ thetaCuspFourierLaplaceStrip := by
    rw [thetaCuspFourierLaplaceStrip]
    have := abs_lt.mp hz
    exact ⟨this.1, this.2⟩
  rw [thetaCuspFourierLaplace_eq_XiC_on_strip hmem] at hzero
  have hI : I * I = -1 := Complex.I_mul_I
  linear_combination I * hzero +
    ((α + z) * hedenmalmThetaEigenTransform α z + XiC z) * hI

/-- The transform of the time-side eigenfunction is exactly the Fourier-side removable quotient
`i Xi(z)/(z + alpha)` based at the reflected zero. -/
theorem hedenmalmThetaEigenTransform_eq_xiThetaEigenFourier {α : ℂ} (hα : |α.im| < 1)
    (h0 : XiC α = 0) {z : ℂ} (hz : |z.im| < 1) (hne : z ≠ -α) :
    hedenmalmThetaEigenTransform α z = I * xiThetaEigenFourier (-α) z := by
  have hzero : XiC (-α) = 0 := by rw [XiC_even, h0]
  have hsum : α + z ≠ 0 := fun hcon => hne (by linear_combination hcon)
  have hkey := mul_hedenmalmThetaEigenTransform hα h0 hz
  rw [xiThetaEigenFourier_eq_div hzero hne]
  have hden : (-α - z) ≠ 0 := fun hcon => hsum (by linear_combination -hcon)
  have hI2 : I ^ (2 : ℕ) = -1 := Complex.I_sq
  field_simp
  linear_combination -hkey + XiC z * hI2

end

end RHTower
