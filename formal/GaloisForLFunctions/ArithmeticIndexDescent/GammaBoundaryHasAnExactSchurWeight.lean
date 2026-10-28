import GaloisForLFunctions.RHTower.GammaHardyPhaseRateLevyKhintchine
import GaloisForLFunctions.HTGeometry.CarlemanSchurWeight
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilGammaBoundaryPairing

/-!
# An exact positive Schur weight for the arithmetic Gamma boundary

The exponential change of variable sends the weighted Gamma row to the
Carleman row. Its arctangent primitive fixes the boundary normalization.
Weighted Cauchy–Schwarz and Tonelli then sharpen the norm of the existing
Gamma boundary operator to pi/2, without changing its source carrier.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open RHTower

namespace GaloisForLFunctions.ArithmeticIndexDescent

/-- The positive boundary weight in exponential coordinates. -/
def gammaBoundarySchurWeight (t : ℝ) : ℝ :=
  Real.exp (t / 2) / Real.sqrt (Real.exp (2 * t) - 1)

theorem gammaBoundarySchurWeight_pos {t : ℝ} (ht : 0 < t) :
    0 < gammaBoundarySchurWeight t := by
  apply div_pos (Real.exp_pos _)
  apply Real.sqrt_pos.mpr
  exact sub_pos.mpr (Real.one_lt_exp_iff.mpr (by linarith only [ht]))

theorem gammaBoundarySchurWeight_eq (t : ℝ) :
    gammaBoundarySchurWeight t =
      Real.exp (-t / 2) / Real.sqrt (1 - Real.exp (-2 * t)) := by
  have he : Real.exp (2 * t) * Real.exp (-2 * t) = 1 := by
    rw [← Real.exp_add, show 2 * t + -2 * t = 0 by ring, Real.exp_zero]
  have hsq : Real.exp t ^ 2 = Real.exp (2 * t) := by
    rw [pow_two, ← Real.exp_add, two_mul]
  have hrad : Real.exp (2 * t) - 1 =
      Real.exp t ^ 2 * (1 - Real.exp (-2 * t)) := by
    rw [hsq]
    nlinarith only [he]
  have hroot : Real.sqrt (Real.exp (2 * t) - 1) =
      Real.exp t * Real.sqrt (1 - Real.exp (-2 * t)) := by
    rw [hrad, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Real.exp_pos t).le]
  have hnum : Real.exp (t / 2) = Real.exp t * Real.exp (-t / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [gammaBoundarySchurWeight, hroot, hnum, mul_div_mul_left _ _ (Real.exp_ne_zero t)]

/-- The Carleman primitive pulled back by the exponential boundary coordinate. -/
def gammaBoundarySchurPrimitive (s t : ℝ) : ℝ :=
  (Real.exp (-s / 2) / 2) *
    HTGeometry.carlemanSchurPrimitive (1 - Real.exp (-2 * s)) (Real.exp (2 * t) - 1)

theorem continuous_gammaBoundarySchurPrimitive (s : ℝ) :
    Continuous (gammaBoundarySchurPrimitive s) := by
  unfold gammaBoundarySchurPrimitive HTGeometry.carlemanSchurPrimitive
  fun_prop

theorem hasDerivAt_gammaBoundarySchurPrimitive {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    HasDerivAt (gammaBoundarySchurPrimitive s)
      (archLevyDensity (s + t) * gammaBoundarySchurWeight t) t := by
  have ha : 0 < 1 - Real.exp (-2 * s) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith only [hs]))
  have hX : 0 < Real.exp (2 * t) - 1 :=
    sub_pos.mpr (Real.one_lt_exp_iff.mpr (by linarith only [ht]))
  have hroot : 0 < Real.sqrt (Real.exp (2 * t) - 1) := Real.sqrt_pos.mpr hX
  have hden : 0 < 1 - Real.exp (-2 * (s + t)) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith only [hs, ht]))
  have hx : HasDerivAt (fun u : ℝ => Real.exp (2 * u) - 1)
      (Real.exp (2 * t) * 2) t := by
    simpa only [mul_one, id_eq] using (((hasDerivAt_id t).const_mul 2).exp).sub_const 1
  have h := ((HTGeometry.hasDerivAt_carlemanSchurPrimitive ha hX).comp t hx).const_mul
    (Real.exp (-s / 2) / 2)
  refine h.congr_deriv ?_
  have he : Real.exp (2 * t) * Real.exp (-2 * (s + t)) = Real.exp (-2 * s) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have heq : 1 - Real.exp (-2 * s) + (Real.exp (2 * t) - 1) =
      Real.exp (2 * t) * (1 - Real.exp (-2 * (s + t))) := by
    nlinarith only [he]
  rw [archLevyDensity, gammaBoundarySchurWeight, div_mul_div_comm, ← Real.exp_add,
    show -(s + t) / 2 + t / 2 = -s / 2 by ring, heq]
  field_simp [Real.exp_ne_zero (2 * t), hroot.ne', hden.ne']

theorem tendsto_gammaBoundarySchurPrimitive {s : ℝ} (hs : 0 < s) :
    Tendsto (gammaBoundarySchurPrimitive s) atTop
      (𝓝 ((Real.pi / 2) * gammaBoundarySchurWeight s)) := by
  have ha : 0 < 1 - Real.exp (-2 * s) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith only [hs]))
  have hlin : Tendsto (fun t : ℝ => 2 * t) atTop atTop := by
    simpa only [mul_comm, id_eq] using
      (tendsto_id.atTop_mul_const (by norm_num : (0 : ℝ) < 2))
  have hexp : Tendsto (fun t : ℝ => Real.exp (2 * t)) atTop atTop :=
    Real.tendsto_exp_atTop.comp hlin
  have hx : Tendsto (fun t : ℝ => Real.exp (2 * t) - 1) atTop atTop :=
    tendsto_atTop_add_const_right _ (-1) hexp
  have h := ((HTGeometry.tendsto_carlemanSchurPrimitive ha).comp hx).const_mul
    (Real.exp (-s / 2) / 2)
  have hc : Real.exp (-s / 2) / 2 *
      (2 / Real.sqrt (1 - Real.exp (-2 * s)) * (Real.pi / 2)) =
      (Real.pi / 2) * gammaBoundarySchurWeight s := by
    rw [gammaBoundarySchurWeight_eq]
    ring
  change Tendsto (gammaBoundarySchurPrimitive s) atTop (𝓝
    (Real.exp (-s / 2) / 2 *
      (2 / Real.sqrt (1 - Real.exp (-2 * s)) * (Real.pi / 2)))) at h
  rwa [hc] at h

/-- The exact weighted Gamma row is absolutely integrable. -/
theorem integrableOn_gammaBoundarySchurRow {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun t => archLevyDensity (s + t) * gammaBoundarySchurWeight t)
      (Ioi (0 : ℝ)) := by
  apply integrableOn_Ioi_deriv_of_nonneg
    (g := gammaBoundarySchurPrimitive s)
    (l := (Real.pi / 2) * gammaBoundarySchurWeight s)
    (continuous_gammaBoundarySchurPrimitive s).continuousWithinAt
    (fun t ht => hasDerivAt_gammaBoundarySchurPrimitive hs ht) _
    (tendsto_gammaBoundarySchurPrimitive hs)
  intro t ht
  exact mul_nonneg (archLevyDensity_pos (add_pos hs ht)).le
    (gammaBoundarySchurWeight_pos ht).le

/-- The actual Gamma Hankel kernel has Schur constant pi/2 in its exact positive weight. -/
theorem integral_gammaBoundarySchurRow {s : ℝ} (hs : 0 < s) :
    (∫ t in Ioi (0 : ℝ), archLevyDensity (s + t) * gammaBoundarySchurWeight t) =
      (Real.pi / 2) * gammaBoundarySchurWeight s := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto
    (continuous_gammaBoundarySchurPrimitive s).continuousWithinAt
    (fun t ht => hasDerivAt_gammaBoundarySchurPrimitive hs ht)
    (integrableOn_gammaBoundarySchurRow hs) (tendsto_gammaBoundarySchurPrimitive hs)
  rw [h, gammaBoundarySchurPrimitive, HTGeometry.carlemanSchurPrimitive]
  simp only [mul_zero, Real.exp_zero, sub_self, Real.sqrt_zero,
    zero_div, Real.arctan_zero, sub_zero]

/-- The exact Schur row in the nonnegative extended integral. -/
theorem lintegral_gammaBoundarySchurRow {s : ℝ} (hs : 0 < s) :
    (∫⁻ t in Ioi (0 : ℝ),
      ENNReal.ofReal (archLevyDensity (s + t) * gammaBoundarySchurWeight t)) =
        ENNReal.ofReal ((Real.pi / 2) * gammaBoundarySchurWeight s) := by
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun t => archLevyDensity (s + t) * gammaBoundarySchurWeight t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (archLevyDensity_pos (add_pos hs ht)).le
      (gammaBoundarySchurWeight_pos ht).le
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_gammaBoundarySchurRow hs) hnn,
    integral_gammaBoundarySchurRow hs]

/-- Cauchy–Schwarz against the exact Gamma boundary weight. -/
theorem sq_lintegral_gammaBoundary_le {F : ℝ → ℝ≥0∞} (hF : Measurable F)
    {s : ℝ} (hs : 0 < s) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (archLevyDensity (s + t)) * F t) ^ 2 ≤
      ENNReal.ofReal ((Real.pi / 2) * gammaBoundarySchurWeight s) *
        ∫⁻ t in Ioi (0 : ℝ),
          ENNReal.ofReal (archLevyDensity (s + t) / gammaBoundarySchurWeight t) * F t ^ 2 := by
  have hw : Measurable gammaBoundarySchurWeight := by
    unfold gammaBoundarySchurWeight
    fun_prop
  have hk : Measurable (fun t : ℝ =>
      ENNReal.ofReal (archLevyDensity (s + t) * gammaBoundarySchurWeight t)) :=
    ENNReal.measurable_ofReal.comp
      ((measurable_archLevyDensity.comp (measurable_const.add measurable_id)).mul hw)
  have hg : Measurable fun t => F t * ENNReal.ofReal (1 / gammaBoundarySchurWeight t) :=
    hF.mul (ENNReal.measurable_ofReal.comp (measurable_const.div hw))
  have h := HTGeometry.lintegral_weighted_sq_le (volume.restrict (Ioi (0 : ℝ))) hk hg
  have hl : (∫⁻ t in Ioi (0 : ℝ),
      ENNReal.ofReal (archLevyDensity (s + t) * gammaBoundarySchurWeight t) *
        (F t * ENNReal.ofReal (1 / gammaBoundarySchurWeight t))) =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (archLevyDensity (s + t)) * F t := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have hwpos := gammaBoundarySchurWeight_pos ht
    have hkpos := archLevyDensity_pos (add_pos hs ht)
    have he : ENNReal.ofReal (archLevyDensity (s + t) * gammaBoundarySchurWeight t) *
        ENNReal.ofReal (1 / gammaBoundarySchurWeight t) =
        ENNReal.ofReal (archLevyDensity (s + t)) := by
      rw [← ENNReal.ofReal_mul (mul_nonneg hkpos.le hwpos.le)]
      congr 1
      field_simp
    calc
      _ = (ENNReal.ofReal (archLevyDensity (s + t) * gammaBoundarySchurWeight t) *
          ENNReal.ofReal (1 / gammaBoundarySchurWeight t)) * F t := by ring
      _ = _ := by rw [he]
  have hr : (∫⁻ t in Ioi (0 : ℝ),
      ENNReal.ofReal (archLevyDensity (s + t) * gammaBoundarySchurWeight t) *
        (F t * ENNReal.ofReal (1 / gammaBoundarySchurWeight t)) ^ 2) =
      ∫⁻ t in Ioi (0 : ℝ),
        ENNReal.ofReal (archLevyDensity (s + t) / gammaBoundarySchurWeight t) * F t ^ 2 := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have hwpos := gammaBoundarySchurWeight_pos ht
    have hkpos := archLevyDensity_pos (add_pos hs ht)
    have he : ENNReal.ofReal (archLevyDensity (s + t) * gammaBoundarySchurWeight t) *
        ENNReal.ofReal (1 / gammaBoundarySchurWeight t) ^ 2 =
        ENNReal.ofReal (archLevyDensity (s + t) / gammaBoundarySchurWeight t) := by
      rw [← ENNReal.ofReal_pow (by positivity),
        ← ENNReal.ofReal_mul (mul_nonneg hkpos.le hwpos.le)]
      congr 1
      field_simp
    calc
      _ = (ENNReal.ofReal (archLevyDensity (s + t) * gammaBoundarySchurWeight t) *
          ENNReal.ofReal (1 / gammaBoundarySchurWeight t) ^ 2) * F t ^ 2 := by ring
      _ = _ := by rw [he]
  rw [hl, hr, lintegral_gammaBoundarySchurRow hs] at h
  exact h

/-- The weighted row and its symmetric column give the squared Gamma norm bound (pi/2)^2. -/
theorem lintegral_gammaBoundary_sq_le {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ s in Ioi (0 : ℝ),
      (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (archLevyDensity (s + t)) * F t) ^ 2) ≤
      ENNReal.ofReal ((Real.pi / 2) ^ 2) * ∫⁻ t in Ioi (0 : ℝ), F t ^ 2 := by
  let G : ℝ → ℝ → ℝ≥0∞ := fun s t =>
    ENNReal.ofReal ((Real.pi / 2) * gammaBoundarySchurWeight s) *
      (ENNReal.ofReal (archLevyDensity (s + t) / gammaBoundarySchurWeight t) * F t ^ 2)
  have hw : Measurable gammaBoundarySchurWeight := by
    unfold gammaBoundarySchurWeight
    fun_prop
  have hm : Measurable (Function.uncurry G) := by
    apply Measurable.mul
    · exact ENNReal.measurable_ofReal.comp (measurable_const.mul (hw.comp measurable_fst))
    · exact (ENNReal.measurable_ofReal.comp
        ((measurable_archLevyDensity.comp (measurable_fst.add measurable_snd)).div
          (hw.comp measurable_snd))).mul ((hF.comp measurable_snd).pow_const 2)
  have hstep : ∀ s ∈ Ioi (0 : ℝ),
      (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (archLevyDensity (s + t)) * F t) ^ 2 ≤
        ∫⁻ t in Ioi (0 : ℝ), G s t := by
    intro s hs
    dsimp only [G]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact sq_lintegral_gammaBoundary_le hF hs
  have hinner : ∀ t ∈ Ioi (0 : ℝ),
      (∫⁻ s in Ioi (0 : ℝ), G s t) = ENNReal.ofReal ((Real.pi / 2) ^ 2) * F t ^ 2 := by
    intro t ht
    have hwt := gammaBoundarySchurWeight_pos ht
    have hfac : ∀ s ∈ Ioi (0 : ℝ), G s t =
        (ENNReal.ofReal ((Real.pi / 2) / gammaBoundarySchurWeight t) * F t ^ 2) *
          ENNReal.ofReal (archLevyDensity (t + s) * gammaBoundarySchurWeight s) := by
      intro s hs
      have hws := gammaBoundarySchurWeight_pos hs
      have hk := archLevyDensity_pos (add_pos hs ht)
      have he : ((Real.pi / 2) * gammaBoundarySchurWeight s) *
          (archLevyDensity (s + t) / gammaBoundarySchurWeight t) =
          ((Real.pi / 2) / gammaBoundarySchurWeight t) *
            (archLevyDensity (t + s) * gammaBoundarySchurWeight s) := by
        rw [add_comm t s]
        ring
      dsimp only [G]
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), he,
        ENNReal.ofReal_mul (by positivity)]
      ring
    have hrow : Measurable (fun s : ℝ =>
        ENNReal.ofReal (archLevyDensity (t + s) * gammaBoundarySchurWeight s)) :=
      ENNReal.measurable_ofReal.comp
        ((measurable_archLevyDensity.comp (measurable_const.add measurable_id)).mul hw)
    rw [setLIntegral_congr_fun measurableSet_Ioi hfac, lintegral_const_mul _ hrow,
      lintegral_gammaBoundarySchurRow ht]
    have he : ENNReal.ofReal ((Real.pi / 2) / gammaBoundarySchurWeight t) *
        ENNReal.ofReal ((Real.pi / 2) * gammaBoundarySchurWeight t) =
        ENNReal.ofReal ((Real.pi / 2) ^ 2) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
    calc
      _ = (ENNReal.ofReal ((Real.pi / 2) / gammaBoundarySchurWeight t) *
          ENNReal.ofReal ((Real.pi / 2) * gammaBoundarySchurWeight t)) * F t ^ 2 := by ring
      _ = _ := by rw [he]
  calc
    _ ≤ ∫⁻ s in Ioi (0 : ℝ), ∫⁻ t in Ioi (0 : ℝ), G s t :=
      setLIntegral_mono' measurableSet_Ioi hstep
    _ = ∫⁻ t in Ioi (0 : ℝ), ∫⁻ s in Ioi (0 : ℝ), G s t :=
      lintegral_lintegral_swap hm.aemeasurable
    _ = ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal ((Real.pi / 2) ^ 2) * F t ^ 2 :=
      setLIntegral_congr_fun measurableSet_Ioi hinner
    _ = _ := lintegral_const_mul _ (hF.pow_const 2)

/-- The sharpened Schur estimate bounds the literal Gamma action in the existing half-line norm. -/
theorem eLpNorm_ccmGammaBoundaryAction_le_pi_half {f : ℝ → ℂ} (hf : Measurable f) :
    eLpNorm (ccmGammaBoundaryAction f) 2 (volume.restrict (Ioi 0)) ≤
      ENNReal.ofReal (Real.pi / 2) * eLpNorm f 2 (volume.restrict (Ioi 0)) := by
  have hρ (t : ℝ) : ccmGammaTranslationDensity t = archLevyDensity t := by
    simp only [ccmGammaTranslationDensity, archLevyDensity, neg_div, neg_mul]
  have hpoint {s : ℝ} (hs : 0 < s) :
      ‖ccmGammaBoundaryAction f s‖ₑ ≤
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (archLevyDensity (s + t)) * ‖f t‖ₑ := by
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [enorm_mul, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
      hρ, abs_of_pos (archLevyDensity_pos (add_pos hs ht))]
  have hsq : (∫⁻ s in Ioi (0 : ℝ), ‖ccmGammaBoundaryAction f s‖ₑ ^ 2) ≤
      ENNReal.ofReal ((Real.pi / 2) ^ 2) * ∫⁻ t in Ioi (0 : ℝ), ‖f t‖ₑ ^ 2 := by
    refine (setLIntegral_mono' measurableSet_Ioi
      (fun s hs => pow_le_pow_left' (hpoint hs) 2)).trans ?_
    exact lintegral_gammaBoundary_sq_le hf.enorm
  rw [HTGeometry.SchurKernel.eLpNorm_two_eq, HTGeometry.SchurKernel.eLpNorm_two_eq]
  refine (ENNReal.rpow_le_rpow hsq (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans_eq ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ENNReal.ofReal_pow (by positivity), ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- The actual existing Gamma boundary operator has norm at most pi/2. -/
theorem norm_ccmGammaBoundaryCLM_le_pi_half : ‖ccmGammaBoundaryCLM‖ ≤ Real.pi / 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  rw [Lp.norm_def, eLpNorm_congr_ae (ccmGammaBoundaryCLM_coeFn f), Lp.norm_def]
  refine (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (Lp.eLpNorm_ne_top f))
    (eLpNorm_ccmGammaBoundaryAction_le_pi_half (Lp.stronglyMeasurable f).measurable)).trans_eq ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.integral_gammaBoundarySchurRow

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.norm_ccmGammaBoundaryCLM_le_pi_half

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.lintegral_gammaBoundary_sq_le
