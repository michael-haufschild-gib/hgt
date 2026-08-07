import GaloisForLFunctions.RHTower.HedenmalmThetaKernelEnergy

/-!
# Decay of the source mode at a zero of the completed transform

The source-pointed mode is `u_z(x) = -i e^{-izx} I_z(x)`, `I_z(x) = ∫_{-∞}^x k(y) e^{izy} dy`.
On the left the crude exponential bound on the source already gives
`‖I_z(x)‖ ≤ C e^{(1-Im z)x}/(1-Im z)`, and at a zero of the completed transform the left tail may be
traded for the right one, giving `‖I_z(x)‖ ≤ C e^{-(1+Im z)x}/(1+Im z)`.  Multiplying by
`‖e^{-izx}‖ = e^{(Im z)x}` both bounds collapse to one two-sided estimate

`‖u_z(x)‖ ≤ C e^{-|x|}/(1-|Im z|)`,

which is the decay the quantile flux identity needs at its endpoints.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmThetaSource

open HedenmalmQuantile HedenmalmPrimeTranslation

/-! ### Two elementary exponential integrals -/

theorem integral_Iic_exp_mul {a x : ℝ} (ha : 0 < a) :
    (∫ y in Iic x, Real.exp (a * y)) = Real.exp (a * x) / a := by
  have hderiv : ∀ y ∈ Iio x,
      HasDerivAt (fun t : ℝ => Real.exp (a * t) / a) (Real.exp (a * y)) y := by
    intro y _
    have h : HasDerivAt (fun t : ℝ => Real.exp (a * t)) (Real.exp (a * y) * a) y := by
      simpa using ((hasDerivAt_id y).const_mul a).exp
    refine (h.div_const a).congr_deriv ?_
    field_simp
  have hcont : ContinuousWithinAt (fun t : ℝ => Real.exp (a * t) / a) (Iic x) x := by
    refine Continuous.continuousWithinAt ?_
    fun_prop
  have htend : Tendsto (fun t : ℝ => Real.exp (a * t) / a) atBot (𝓝 0) := by
    have hlin : Tendsto (fun t : ℝ => a * t) atBot atBot :=
      Filter.Tendsto.const_mul_atBot ha tendsto_id
    simpa using (Real.tendsto_exp_atBot.comp hlin).div_const a
  have h := MeasureTheory.integral_Iic_of_hasDerivAt_of_tendsto hcont hderiv
    (integrableOn_exp_mul_Iic ha x) htend
  simpa using h

theorem integral_Ioi_exp_neg_mul {b x : ℝ} (hb : 0 < b) :
    (∫ y in Ioi x, Real.exp (-b * y)) = Real.exp (-b * x) / b := by
  have hpt : ∀ y : ℝ, Real.exp (-b * y)
      = Real.exp (-b * x) * Real.exp (-b * (y - x)) := by
    intro y
    rw [← Real.exp_add]
    congr 1
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun y _ => hpt y),
    MeasureTheory.integral_const_mul, integral_Ioi_exp_neg_shift hb, mul_one_div]

/-! ### The two one-sided bounds on the source primitive -/

theorem norm_k_sourceChar_le (z : ℂ) (y : ℝ) :
    ‖(thetaSource.k y : ℂ) * sourceChar z y‖
      ≤ thetaBound * Real.exp (-|y|) * Real.exp (-z.im * y) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (thetaCuspFullSource_pos y).le, norm_sourceChar]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  exact le_trans (le_abs_self _) (abs_thetaCuspFullSource_le y)

/-- **The left bound.**  On the negative half-line the source primitive decays like
`e^{(1-Im z)x}`. -/
theorem norm_sourceModeI_le_left {z : ℂ} (hz : |z.im| < 1) {x : ℝ} (hx : x ≤ 0) :
    ‖sourceModeI thetaSource z x‖
      ≤ thetaBound * Real.exp ((1 - z.im) * x) / (1 - z.im) := by
  have hzim : z.im < 1 := lt_of_le_of_lt (le_abs_self _) hz
  have hapos : (0 : ℝ) < 1 - z.im := by linarith
  have hCnn := thetaBound_nonneg
  have hint : IntegrableOn (fun y : ℝ => (thetaSource.k y : ℂ) * sourceChar z y) (Iic x) volume :=
    (integrable_k_sourceChar thetaSource (hasShiftedTail_thetaSource hz)).integrableOn
  have hdom : IntegrableOn (fun y : ℝ => thetaBound * Real.exp ((1 - z.im) * y)) (Iic x) volume :=
    (integrableOn_exp_mul_Iic hapos x).const_mul thetaBound
  have hbound : ∀ y ∈ Iic x, ‖(thetaSource.k y : ℂ) * sourceChar z y‖
      ≤ thetaBound * Real.exp ((1 - z.im) * y) := by
    intro y hy
    have hy0 : y ≤ 0 := le_trans hy hx
    have habs : Real.exp (-|y|) = Real.exp y := by
      rw [abs_of_nonpos hy0, neg_neg]
    calc ‖(thetaSource.k y : ℂ) * sourceChar z y‖
        ≤ thetaBound * Real.exp (-|y|) * Real.exp (-z.im * y) := norm_k_sourceChar_le z y
      _ = thetaBound * Real.exp ((1 - z.im) * y) := by
          rw [habs, mul_assoc, ← Real.exp_add]
          congr 2
          ring
  calc ‖sourceModeI thetaSource z x‖
      ≤ ∫ y in Iic x, ‖(thetaSource.k y : ℂ) * sourceChar z y‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ y in Iic x, thetaBound * Real.exp ((1 - z.im) * y) :=
        setIntegral_mono_on hint.norm hdom measurableSet_Iic hbound
    _ = thetaBound * Real.exp ((1 - z.im) * x) / (1 - z.im) := by
        rw [MeasureTheory.integral_const_mul, integral_Iic_exp_mul hapos, mul_div_assoc]

/-- **The right bound.**  At a zero of the completed transform the primitive is the negative of the
right tail, so on the positive half-line it decays like `e^{-(1+Im z)x}`. -/
theorem norm_sourceModeI_le_right {z : ℂ} (hz : |z.im| < 1) (hzero : xiC thetaSource z = 0)
    {x : ℝ} (hx : 0 ≤ x) :
    ‖sourceModeI thetaSource z x‖
      ≤ thetaBound * Real.exp (-(1 + z.im) * x) / (1 + z.im) := by
  have hzim : -1 < z.im := by
    have h := neg_abs_le z.im
    linarith
  have hbpos : (0 : ℝ) < 1 + z.im := by linarith
  have hCnn := thetaBound_nonneg
  have hk := integrable_k_sourceChar thetaSource (hasShiftedTail_thetaSource hz)
  have hsplit := HedenmalmFredholmRange.setIntegral_Iic_add_Ioi hk x
  rw [xiC] at hzero
  rw [hzero] at hsplit
  have hI : sourceModeI thetaSource z x
      = -∫ y in Ioi x, (thetaSource.k y : ℂ) * sourceChar z y := by
    rw [sourceModeI]
    linear_combination hsplit
  have hdom : IntegrableOn (fun y : ℝ => thetaBound * Real.exp (-(1 + z.im) * y)) (Ioi x)
      volume := (exp_neg_integrableOn_Ioi x hbpos).const_mul thetaBound
  have hbound : ∀ y ∈ Ioi x, ‖(thetaSource.k y : ℂ) * sourceChar z y‖
      ≤ thetaBound * Real.exp (-(1 + z.im) * y) := by
    intro y hy
    have hy0 : 0 ≤ y := le_trans hx (le_of_lt hy)
    have habs : Real.exp (-|y|) = Real.exp (-y) := by rw [abs_of_nonneg hy0]
    calc ‖(thetaSource.k y : ℂ) * sourceChar z y‖
        ≤ thetaBound * Real.exp (-|y|) * Real.exp (-z.im * y) := norm_k_sourceChar_le z y
      _ = thetaBound * Real.exp (-(1 + z.im) * y) := by
          rw [habs, mul_assoc, ← Real.exp_add]
          congr 2
          ring
  rw [hI, norm_neg]
  calc ‖∫ y in Ioi x, (thetaSource.k y : ℂ) * sourceChar z y‖
      ≤ ∫ y in Ioi x, ‖(thetaSource.k y : ℂ) * sourceChar z y‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ y in Ioi x, thetaBound * Real.exp (-(1 + z.im) * y) :=
        setIntegral_mono_on hk.integrableOn.norm hdom measurableSet_Ioi hbound
    _ = thetaBound * Real.exp (-(1 + z.im) * x) / (1 + z.im) := by
        rw [MeasureTheory.integral_const_mul, integral_Ioi_exp_neg_mul hbpos, mul_div_assoc]

/-! ### The two-sided bound on the source mode -/

theorem norm_exp_neg_I_mul (z : ℂ) (x : ℝ) :
    ‖Complex.exp (-(Complex.I * z) * (x : ℂ))‖ = Real.exp (z.im * x) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- **The source mode decays exponentially at both ends at a zero of the completed transform.** -/
theorem norm_sourceModeU_le {z : ℂ} (hz : |z.im| < 1) (hzero : xiC thetaSource z = 0) (x : ℝ) :
    ‖sourceModeU thetaSource z x‖
      ≤ thetaBound / (1 - |z.im|) * Real.exp (-|x|) := by
  have hCnn := thetaBound_nonneg
  have hgap : (0 : ℝ) < 1 - |z.im| := by linarith
  have hnorm : ‖sourceModeU thetaSource z x‖
      = Real.exp (z.im * x) * ‖sourceModeI thetaSource z x‖ := by
    rw [sourceModeU, norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul,
      norm_exp_neg_I_mul]
  rcases le_total x 0 with hx | hx
  · have hzim : z.im < 1 := lt_of_le_of_lt (le_abs_self _) hz
    have hapos : (0 : ℝ) < 1 - z.im := by linarith
    have hle := norm_sourceModeI_le_left hz hx
    have habs : Real.exp (-|x|) = Real.exp x := by rw [abs_of_nonpos hx, neg_neg]
    have hstep : Real.exp (z.im * x) * ‖sourceModeI thetaSource z x‖
        ≤ Real.exp (z.im * x) * (thetaBound * Real.exp ((1 - z.im) * x) / (1 - z.im)) :=
      mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le
    have hcollapse : Real.exp (z.im * x) * (thetaBound * Real.exp ((1 - z.im) * x) / (1 - z.im))
        = thetaBound / (1 - z.im) * Real.exp x := by
      rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc, ← Real.exp_add]
      ring_nf
      rw [show z.im * x + (1 - z.im) * x = x by ring]
      ring
    have hmono : thetaBound / (1 - z.im) ≤ thetaBound / (1 - |z.im|) := by
      refine div_le_div_of_nonneg_left hCnn hgap ?_
      have := neg_abs_le z.im
      linarith [le_abs_self z.im]
    rw [hnorm, habs]
    calc Real.exp (z.im * x) * ‖sourceModeI thetaSource z x‖
        ≤ Real.exp (z.im * x) * (thetaBound * Real.exp ((1 - z.im) * x) / (1 - z.im)) := hstep
      _ = thetaBound / (1 - z.im) * Real.exp x := hcollapse
      _ ≤ thetaBound / (1 - |z.im|) * Real.exp x :=
          mul_le_mul_of_nonneg_right hmono (Real.exp_pos _).le
  · have hzim : -1 < z.im := by
      have h := neg_abs_le z.im
      linarith
    have hbpos : (0 : ℝ) < 1 + z.im := by linarith
    have hle := norm_sourceModeI_le_right hz hzero hx
    have habs : Real.exp (-|x|) = Real.exp (-x) := by rw [abs_of_nonneg hx]
    have hstep : Real.exp (z.im * x) * ‖sourceModeI thetaSource z x‖
        ≤ Real.exp (z.im * x) * (thetaBound * Real.exp (-(1 + z.im) * x) / (1 + z.im)) :=
      mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le
    have hcollapse : Real.exp (z.im * x) * (thetaBound * Real.exp (-(1 + z.im) * x) / (1 + z.im))
        = thetaBound / (1 + z.im) * Real.exp (-x) := by
      rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc, ← Real.exp_add]
      ring_nf
      rw [show z.im * x + -(1 + z.im) * x = -x by ring]
      ring
    have hmono : thetaBound / (1 + z.im) ≤ thetaBound / (1 - |z.im|) := by
      refine div_le_div_of_nonneg_left hCnn hgap ?_
      have := neg_abs_le z.im
      linarith
    rw [hnorm, habs]
    calc Real.exp (z.im * x) * ‖sourceModeI thetaSource z x‖
        ≤ Real.exp (z.im * x) * (thetaBound * Real.exp (-(1 + z.im) * x) / (1 + z.im)) := hstep
      _ = thetaBound / (1 + z.im) * Real.exp (-x) := hcollapse
      _ ≤ thetaBound / (1 - |z.im|) * Real.exp (-x) :=
          mul_le_mul_of_nonneg_right hmono (Real.exp_pos _).le

end HedenmalmThetaSource

end

end RHTower
