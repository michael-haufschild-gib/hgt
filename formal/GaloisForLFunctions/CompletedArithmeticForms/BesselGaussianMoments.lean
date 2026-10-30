import GaloisForLFunctions.CompletedArithmeticForms.BesselBarrierPayment

/-!
# Literal Schläfli concentration and normalization

The differentiated order recurrence evaluates the positive first moment
`∫ t sinh(t) exp(-a cosh(t)) = K₀(a)/a`. It pays the second moment and
the quadratic cosine error, fixing the imaginary-order normalization at
large argument without an asymptotic premise.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.CompletedArithmeticForms

open HTGeometry

theorem integrableOn_besselOrderKernelDeriv {a : ℝ} (ha : 0 < a) (ν : ℂ) :
    IntegrableOn (besselOrderKernelDeriv a ν) (Ioi 0) := by
  have h := (integrable_mul_exp_neg_mul_sq
    (div_pos ha (by norm_num : (0 : ℝ) < 8))).norm.const_mul
      (Real.exp (2 * ‖ν‖ ^ 2 / a))
  have hb : IntegrableOn (fun t : ℝ => Real.exp (2 * ‖ν‖ ^ 2 / a) *
      (|t| * Real.exp (-(a / 8) * t ^ 2))) (Ioi 0) := by
    apply h.integrableOn.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  apply hb.mono'
  · unfold besselOrderKernelDeriv
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact norm_besselOrderKernelDeriv_le ha ht.le le_rfl

/-- Order reflection makes the literal differentiated kernel odd in its order. -/
theorem integral_besselOrderKernelDeriv_neg (a : ℝ) (ν : ℂ) :
    (∫ t in Ioi (0 : ℝ), besselOrderKernelDeriv a (-ν) t) =
      -(∫ t in Ioi (0 : ℝ), besselOrderKernelDeriv a ν t) := by
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards with t
  simp only [besselOrderKernelDeriv, neg_mul, Complex.sinh_neg, mul_neg]

/-- Differentiating the exact order recurrence pays the first moment at order one. -/
theorem integral_besselOrderKernelDeriv_one {a : ℝ} (ha : 0 < a) :
    (∫ t in Ioi (0 : ℝ), besselOrderKernelDeriv a 1 t) =
      modifiedBesselKOrder a 0 / (a : ℂ) := by
  let D (ν : ℂ) := ∫ t in Ioi (0 : ℝ), besselOrderKernelDeriv a ν t
  have hl : HasDerivAt (fun z : ℂ => modifiedBesselKOrder a (z + 1)) (D 1) 0 := by
    simpa only [zero_add, mul_one] using
      (hasDerivAt_modifiedBesselKOrder ha (0 + 1)).comp 0 ((hasDerivAt_id 0).add_const 1)
  have hm : HasDerivAt (fun z : ℂ => modifiedBesselKOrder a (z - 1)) (D (-1)) 0 := by
    simpa only [zero_sub, mul_one] using
      (hasDerivAt_modifiedBesselKOrder ha (0 - 1)).comp 0 ((hasDerivAt_id 0).sub_const 1)
  have hr := hm.add ((((hasDerivAt_id (0 : ℂ)).const_mul 2).div_const (a : ℂ)).mul
    (hasDerivAt_modifiedBesselKOrder ha 0))
  have heq : (fun z : ℂ => modifiedBesselKOrder a (z + 1)) =
      fun z : ℂ => modifiedBesselKOrder a (z - 1) + (2 * z / a) * modifiedBesselKOrder a z :=
    funext (modifiedBesselKOrder_add_one ha)
  rw [heq] at hl
  have he := hl.unique hr
  have hn : D (-1) = -D 1 := integral_besselOrderKernelDeriv_neg a 1
  dsimp only [id_eq] at he
  rw [hn] at he
  change D 1 = _
  linear_combination he / 2

theorem integrableOn_bessel_first_moment {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => Real.exp (-a * Real.cosh t) * (t * Real.sinh t)) (Ioi 0) := by
  have h := (integrableOn_besselOrderKernelDeriv ha 1).re
  convert h using 1
  ext t
  simp only [besselOrderKernelDeriv, one_mul, ← Complex.ofReal_sinh,
    ← Complex.ofReal_cosh, ← Complex.ofReal_mul, ← Complex.ofReal_neg,
    ← Complex.ofReal_exp, Complex.ofReal_re]

/-- The positive first moment is exactly the zero-order source divided by its argument. -/
theorem integral_bessel_first_moment {a : ℝ} (ha : 0 < a) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-a * Real.cosh t) * (t * Real.sinh t)) =
      (modifiedBesselKOrder a 0).re / a := by
  have h := congrArg Complex.re (integral_besselOrderKernelDeriv_one ha)
  rw [← integral_re (integrableOn_besselOrderKernelDeriv ha 1)] at h
  simpa only [besselOrderKernelDeriv, one_mul, ← Complex.ofReal_sinh,
    ← Complex.ofReal_cosh, ← Complex.ofReal_mul, ← Complex.ofReal_neg,
    ← Complex.ofReal_exp, Complex.ofReal_re, Complex.div_ofReal_re] using h

theorem integrableOn_bessel_second_moment {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => Real.exp (-a * Real.cosh t) * t ^ 2) (Ioi 0) := by
  apply (integrableOn_bessel_first_moment ha).mono'
  · fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    have h := mul_le_mul_of_nonneg_left (Real.self_le_sinh_iff.mpr ht.le) ht.le
    simpa only [pow_two] using h

/-- The literal Schläfli probability density has second moment at most `1/a`. -/
theorem integral_bessel_second_moment_le {a : ℝ} (ha : 0 < a) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-a * Real.cosh t) * t ^ 2) ≤
      (modifiedBesselKOrder a 0).re / a := by
  rw [← integral_bessel_first_moment ha]
  refine setIntegral_mono_on (integrableOn_bessel_second_moment ha)
    (integrableOn_bessel_first_moment ha) measurableSet_Ioi fun t ht => ?_
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  have h := mul_le_mul_of_nonneg_left (Real.self_le_sinh_iff.mpr ht.le) ht.le
  simpa only [pow_two] using h

private theorem cosine_defect_le (y : ℝ) : 1 - Real.cos y ≤ y ^ 2 / 2 := by
  have hs : Real.sin (y / 2) ^ 2 ≤ (y / 2) ^ 2 := by
    simpa only [sq_abs] using
      pow_le_pow_left₀ (abs_nonneg _) (Real.abs_sin_le_abs (x := y / 2)) 2
  have hc := Real.sin_sq_add_cos_sq (y / 2)
  have hd := Real.cos_two_mul (y / 2)
  rw [show 2 * (y / 2) = y by ring] at hd
  nlinarith only [hs, hc, hd]

theorem modifiedBesselKOrder_imaginary_re_integral {a : ℝ} (ha : 0 < a) (τ : ℝ) :
    (modifiedBesselKOrder a ((τ : ℂ) * I)).re =
      ∫ t in Ioi (0 : ℝ), Real.exp (-a * Real.cosh t) * Real.cos (τ * t) := by
  rw [modifiedBesselKOrder, ← integral_re (integrableOn_besselOrderKernel ha _)]
  apply integral_congr_ae
  filter_upwards with t
  rw [besselOrderKernel_eq_ofReal_mul, Complex.re_ofReal_mul]
  have he : (τ : ℂ) * I * (t : ℂ) = ((τ * t : ℝ) : ℂ) * I := by push_cast; ring
  rw [he, Complex.cosh_mul_I]
  simp only [Complex.cos_ofReal_re]

/-- A literal quadratic cosine payment gives the fixed-order asymptotic normalization. -/
theorem bessel_imaginary_ratio_bounds {a : ℝ} (ha : 0 < a) (τ : ℝ) :
    1 - τ ^ 2 / (2 * a) ≤
      (modifiedBesselKOrder a ((τ : ℂ) * I)).re / (modifiedBesselKOrder a 0).re ∧
    (modifiedBesselKOrder a ((τ : ℂ) * I)).re / (modifiedBesselKOrder a 0).re ≤ 1 := by
  let w : ℝ → ℝ := fun t => Real.exp (-a * Real.cosh t)
  have hw : IntegrableOn w (Ioi 0) := by
    simpa only [realBesselOrderKernel, zero_mul, Real.cosh_zero, mul_one] using
      integrableOn_realBesselOrderKernel ha 0
  have hf : IntegrableOn (fun t => w t * Real.cos (τ * t)) (Ioi 0) := by
    have h := (integrableOn_besselOrderKernel ha ((τ : ℂ) * I)).re
    convert h using 1
    ext t
    rw [besselOrderKernel_eq_ofReal_mul, Complex.re_ofReal_mul]
    have he : (τ : ℂ) * I * (t : ℂ) = ((τ * t : ℝ) : ℂ) * I := by push_cast; ring
    rw [he, Complex.cosh_mul_I]
    simp only [Complex.cos_ofReal_re]
  have hg : (∫ t in Ioi (0 : ℝ), w t) = (modifiedBesselKOrder a 0).re := by
    simpa only [Complex.ofReal_zero, zero_mul, Real.cos_zero, mul_one]
      using (modifiedBesselKOrder_imaginary_re_integral ha 0).symm
  have hgp : 0 < (modifiedBesselKOrder a 0).re := by
    simpa only [Complex.ofReal_zero, zero_mul] using
      modifiedBesselKOrder_re_pos_on_band ha (by simpa using ha.le : |(0 : ℝ)| ≤ a)
  have hu : (modifiedBesselKOrder a ((τ : ℂ) * I)).re ≤ (modifiedBesselKOrder a 0).re := by
    rw [modifiedBesselKOrder_imaginary_re_integral ha, ← hg]
    exact setIntegral_mono_on hf hw measurableSet_Ioi fun t _ =>
      mul_le_of_le_one_right (Real.exp_pos _).le (Real.cos_le_one _)
  have hd : (modifiedBesselKOrder a 0).re -
      (modifiedBesselKOrder a ((τ : ℂ) * I)).re ≤
        τ ^ 2 / 2 * ((modifiedBesselKOrder a 0).re / a) := by
    rw [modifiedBesselKOrder_imaginary_re_integral ha, ← hg, ← integral_sub hw hf]
    calc
      _ ≤ ∫ t in Ioi (0 : ℝ), τ ^ 2 / 2 * (w t * t ^ 2) := by
        refine setIntegral_mono_on (hw.sub hf)
          ((integrableOn_bessel_second_moment ha).const_mul _) measurableSet_Ioi fun t _ => ?_
        have h := mul_le_mul_of_nonneg_left (cosine_defect_le (τ * t)) (Real.exp_pos _).le
        dsimp only [w] at *
        nlinarith only [h]
      _ = τ ^ 2 / 2 * (∫ t in Ioi (0 : ℝ), w t * t ^ 2) := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (integral_bessel_second_moment_le ha) (by positivity)
  refine ⟨(le_div_iff₀ hgp).mpr ?_, (div_le_iff₀ hgp).mpr (by simpa using hu)⟩
  calc
    _ = (modifiedBesselKOrder a 0).re -
        τ ^ 2 / 2 * ((modifiedBesselKOrder a 0).re / a) := by ring
    _ ≤ _ := by linarith only [hd]

/-- The imaginary-order source divided by the zero-order source tends to one. -/
theorem tendsto_bessel_imaginary_ratio_one (τ : ℝ) :
    Tendsto (fun a : ℝ => (modifiedBesselKOrder a ((τ : ℂ) * I)).re /
      (modifiedBesselKOrder a 0).re) atTop (𝓝 1) := by
  have h := (tendsto_inv_atTop_zero : Tendsto (fun a : ℝ => a⁻¹) atTop (𝓝 0)).const_mul
    (τ ^ 2 / 2)
  have hl : Tendsto (fun a : ℝ => 1 - τ ^ 2 / (2 * a)) atTop (𝓝 1) := by
    convert tendsto_const_nhds.sub h using 1 <;> simp only [mul_zero, sub_zero]
    ext a
    ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha using
      (bessel_imaginary_ratio_bounds ha τ).1
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha using
      (bessel_imaginary_ratio_bounds ha τ).2

#print axioms integral_bessel_first_moment
#print axioms integral_bessel_second_moment_le
#print axioms bessel_imaginary_ratio_bounds
#print axioms tendsto_bessel_imaginary_ratio_one

end GaloisForLFunctions.CompletedArithmeticForms
