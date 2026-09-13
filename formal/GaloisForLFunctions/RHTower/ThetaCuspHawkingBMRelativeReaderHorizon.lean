import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceReflectionTransport
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceSpatialODE
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalFundamentalFrequencies
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceHorizonModeLimits

/-!
The original reflected physical reader at one unchanged physical frequency.
The Gauss factors share their leading normalization, but have an exact nonzero
first relative coefficient. The original radial Green current retains the
corresponding horizon coefficient. No complete-action extinction is asserted.
-/

open Complex Set Filter Topology
namespace RHTower.D4BMRelativeReaderHorizon
open D4BMLaplaceRadial D4BMJointSource D4BMJointWave D4BMPhysicalModeAction
open D4BMGlobalAngularResponse D4BMModularCore
noncomputable section
set_option autoImplicit false

private theorem center_ne_zero (q : XiZeroCopy) : center q ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  exact xi_divisor_support_im_ne_zero q.1
    (by simpa [D4BMGlobalAngularResponse.center] using hi)

private theorem one_add_frequency_ne_zero (q : XiZeroCopy) (side : Bool) :
    1 + physicalFundamentalFrequency q side ≠ 0 := by
  intro h
  exact (physicalFundamentalFrequency_strip q side).1
    (by simpa only [Complex.add_im, Complex.one_im, zero_add, Complex.zero_im]
      using congrArg Complex.im h)

private theorem gauss_product (r : XiZeroCopy) (w : ℂ) :
    gaussA w (physicalRadialFrequency r) * gaussB w (physicalRadialFrequency r) =
      (w * (w + 1) + D4BMLiteralCusp.scalarQ (physicalAngularParameter r)) / 4 := by
  have hi : I ^ 4 = 1 := by
    calc
      I ^ 4 = (I ^ 2) ^ 2 := by ring
      _ = 1 := by rw [Complex.I_sq]; norm_num
  dsimp [gaussA, gaussB, physicalRadialFrequency, D4BMLiteralCusp.scalarQ]
  ring_nf
  simp only [hi, one_mul]

private theorem gauss_first_zero (r : XiZeroCopy) (w : ℂ) (hw : w.im ≠ 0) :
    (1 + w) * gaussFirst w (physicalRadialFrequency r) false 0 =
      (w * (w + 1) + D4BMLiteralCusp.scalarQ (physicalAngularParameter r)) / 4 := by
  have h := horizonFactor_equation_continued
    (chi := physicalRadialFrequency r) (z := 0) hw (by simp)
  simpa only [gaussJet, zero_mul, mul_zero, sub_zero, zero_add,
    gaussFactor_zero, mul_one, gaussC, sub_eq_zero, gauss_product] using h

/-- The exact first relative coefficient follows from the original Gauss equation. -/
theorem gauss_first_difference (q : XiZeroCopy) (side : Bool) :
    gaussFirst (physicalFundamentalFrequency q side) (physicalRadialFrequency q) false 0 -
      gaussFirst (physicalFundamentalFrequency q side)
        (physicalRadialFrequency (xiZeroCopyReflectEquiv q)) false 0 =
      center q / (8 * (1 + physicalFundamentalFrequency q side)) := by
  have hq := gauss_first_zero q _ (physicalFundamentalFrequency_strip q side).1
  have hr := gauss_first_zero (xiZeroCopyReflectEquiv q) _
    (physicalFundamentalFrequency_strip q side).1
  have he := D4BMSourceReflectionTransport.physical_reader_eigenvalue_defect q
  apply (eq_div_iff (mul_ne_zero (by norm_num) (one_add_frequency_ne_zero q side))).2
  linear_combination 8 * hq - 8 * hr + 2 * he

/-- The relative coefficient never vanishes, including at occurrences on the line. -/
theorem gauss_first_difference_ne_zero (q : XiZeroCopy) (side : Bool) :
    gaussFirst (physicalFundamentalFrequency q side) (physicalRadialFrequency q) false 0 -
      gaussFirst (physicalFundamentalFrequency q side)
        (physicalRadialFrequency (xiZeroCopyReflectEquiv q)) false 0 ≠ 0 := by
  rw [gauss_first_difference]
  exact div_ne_zero (center_ne_zero q)
    (mul_ne_zero (by norm_num) (one_add_frequency_ne_zero q side))

/-- Analytic radial difference: the zeroth coefficients cancel, the first do not. -/
theorem relative_gauss_hasDerivAt_zero (q : XiZeroCopy) (side : Bool) :
    HasDerivAt (fun z : ℂ =>
      gaussFactor (physicalFundamentalFrequency q side) (physicalRadialFrequency q) false z -
        gaussFactor (physicalFundamentalFrequency q side)
          (physicalRadialFrequency (xiZeroCopyReflectEquiv q)) false z)
      (center q / (8 * (1 + physicalFundamentalFrequency q side))) 0 := by
  rw [← gauss_first_difference]
  exact (gaussFactor_derivatives_continued false (by simp : ‖(0 : ℂ)‖ₑ < 1)).1.sub
    (gaussFactor_derivatives_continued false (by simp : ‖(0 : ℂ)‖ₑ < 1)).1

/-- The original radial Green boundary current, with both readers at the same clock. -/
def radialGreen (q : XiZeroCopy) (side : Bool) (t : ℝ) : ℂ :=
  let w := physicalFundamentalFrequency q side
  let r := xiZeroCopyReflectEquiv q
  tortoiseMode false w (physicalRadialFrequency r) t *
      tortoiseModeFirst false w (physicalRadialFrequency q) t -
    tortoiseMode false w (physicalRadialFrequency q) t *
      tortoiseModeFirst false w (physicalRadialFrequency r) t

private def gaussGreen (q : XiZeroCopy) (side : Bool) (z : ℂ) : ℂ :=
  let w := physicalFundamentalFrequency q side
  let r := xiZeroCopyReflectEquiv q
  gaussFactor w (physicalRadialFrequency r) false z *
      gaussFirst w (physicalRadialFrequency q) false z -
    gaussFactor w (physicalRadialFrequency q) false z *
      gaussFirst w (physicalRadialFrequency r) false z

/-- Every differentiated dressing term is retained before cancellation. -/
theorem radialGreen_eq (q : XiZeroCopy) (side : Bool) (t : ℝ) :
    radialGreen q side t =
      2 * (radialUnit t : ℂ) * ((horizonCoordinate t : ℂ) *
        power (physicalFundamentalFrequency q side / 2) (horizonCoordinate t) ^ 2) *
        gaussGreen q side (horizonCoordinate t) := by
  dsimp [radialGreen, gaussGreen, tortoiseMode, tortoiseModeFirst, radialMode,
    radialModeFirst, horizon, horizonFirst, dress, dressFirst, coordinateFirst]
  push_cast
  ring

private theorem gaussGreen_continuousAt_zero (q : XiZeroCopy) (side : Bool) :
    ContinuousAt (gaussGreen q side) 0 := by
  have hq := gaussFactor_derivatives_continued
    (w := physicalFundamentalFrequency q side) (chi := physicalRadialFrequency q)
    false (by simp : ‖(0 : ℂ)‖ₑ < 1)
  have hr := gaussFactor_derivatives_continued
    (w := physicalFundamentalFrequency q side)
    (chi := physicalRadialFrequency (xiZeroCopyReflectEquiv q))
    false (by simp : ‖(0 : ℂ)‖ₑ < 1)
  exact (hr.1.continuousAt.mul hq.2.continuousAt).sub
    (hq.1.continuousAt.mul hr.2.continuousAt)

private theorem gaussGreen_zero (q : XiZeroCopy) (side : Bool) :
    gaussGreen q side 0 = center q / (8 * (1 + physicalFundamentalFrequency q side)) := by
  simp only [gaussGreen, gaussFactor_zero, one_mul]
  exact gauss_first_difference q side

private theorem gauss_along_horizon (r : XiZeroCopy) (w : ℂ) :
    Tendsto (fun t => gaussFactor w (physicalRadialFrequency r) false (horizonCoordinate t))
      atBot (𝓝 1) := by
  have h := (gaussFactor_derivatives_continued (w := w) (chi := physicalRadialFrequency r)
    false (by simp : ‖(0 : ℂ)‖ₑ < 1)).1.continuousAt.tendsto
  simpa only [gaussFactor_zero, Function.comp_def] using h.comp
    horizonCoordinate_tendsto_horizon.ofReal

private theorem unit_horizon : Tendsto radialUnit atBot (𝓝 (1 : ℝ)) := by
  have ht : Tendsto (fun x : ℝ => 2 * x) atBot atBot :=
    (tendsto_const_mul_atBot_of_pos (by norm_num : (0 : ℝ) < 2)).mpr tendsto_id
  have he := Real.tendsto_exp_atBot.comp ht
  have hf : radialUnit = fun x => (1 - Real.exp (2*x)) / (1 + Real.exp (2*x)) := by
    funext x
    apply (eq_div_iff (ne_of_gt (by positivity : 0 < 1 + Real.exp (2*x)))).mpr
    have hh := radialUnit_one_sub x
    nlinarith
  rw [hf]
  convert
    (tendsto_const_nhds.sub he).div (tendsto_const_nhds.add he)
    (by norm_num : (1 + 0 : ℝ) ≠ 0) using 1
  · ext x
    rfl
  · norm_num

/-- The boundary current has an exact, source-derived, nonzero horizon coefficient. -/
theorem normalized_radialGreen_tendsto (q : XiZeroCopy) (side : Bool) :
    Tendsto (fun t => radialGreen q side t /
      ((horizonCoordinate t : ℂ) *
        power (physicalFundamentalFrequency q side / 2) (horizonCoordinate t) ^ 2))
      atBot (𝓝 (center q / (4 * (1 + physicalFundamentalFrequency q side)))) := by
  have hg := (gaussGreen_continuousAt_zero q side).tendsto.comp
    horizonCoordinate_tendsto_horizon.ofReal
  rw [gaussGreen_zero] at hg
  have he := (unit_horizon.ofReal.const_mul (2 : ℂ)).mul hg
  simp only [Complex.ofReal_one, Function.comp_def] at he
  have hc : 2 * (1 : ℂ) * (center q / (8 * (1 + physicalFundamentalFrequency q side))) =
      center q / (4 * (1 + physicalFundamentalFrequency q side)) := by
    field_simp
    ring
  rw [hc] at he
  apply he.congr'
  filter_upwards [eventually_lt_atBot (0 : ℝ)] with t ht
  have hz := (horizonCoordinate_interior t ht).1
  have hn : (horizonCoordinate t : ℂ) *
      power (physicalFundamentalFrequency q side / 2) (horizonCoordinate t) ^ 2 ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hz.ne')
      (pow_ne_zero _ (power_ne_zero _ hz))
  rw [radialGreen_eq]
  apply (eq_div_iff hn).2
  ring

/-- Nonzero coefficient for the original Green boundary term, without RH. -/
theorem radialGreen_horizon_coefficient_ne_zero (q : XiZeroCopy) (side : Bool) :
    center q / (4 * (1 + physicalFundamentalFrequency q side)) ≠ 0 :=
  div_ne_zero (center_ne_zero q)
    (mul_ne_zero (by norm_num) (one_add_frequency_ne_zero q side))

private theorem frequency_real_interval (q : XiZeroCopy) (side : Bool) :
    -2 < (physicalFundamentalFrequency q side).re ∧
      (physicalFundamentalFrequency q side).re < -1 := by
  have hr := xi_divisor_support_re_mem_open_unit q.1
  rw [physicalFundamentalFrequency_eq]
  cases side <;> norm_num [Complex.sub_re, Complex.add_re, Complex.neg_re, Complex.div_ofNat_re]
  all_goals constructor <;> linarith [hr.1, hr.2]

private theorem power_along_horizon {a : ℂ} (ha : 0 < a.re) :
    Tendsto (fun t => power a (horizonCoordinate t)) atBot (𝓝 0) := by
  have hn : a ≠ 0 := fun h => (ne_of_gt ha) (by rw [h]; rfl)
  have hc := (Complex.continuousAt_cpow_const_of_re_pos
    (z := 0) (Or.inl (by simp)) ha).tendsto
  simpa only [Complex.zero_cpow hn, power, Function.comp_def] using
    hc.comp horizonCoordinate_tendsto_horizon.ofReal

private theorem horizon_scale_eq (q : XiZeroCopy) (side : Bool) {z : ℝ} (hz : 0 < z) :
    (z : ℂ) * power (physicalFundamentalFrequency q side / 2) z ^ 2 =
      power (physicalFundamentalFrequency q side + 1) z := by
  have hn := Complex.ofReal_ne_zero.mpr hz.ne'
  dsimp only [power]
  rw [Complex.cpow_add _ _ hn, Complex.cpow_one]
  have he : (z : ℂ) ^ physicalFundamentalFrequency q side =
      ((z : ℂ) ^ (physicalFundamentalFrequency q side / 2)) ^ 2 := by
    rw [pow_two, ← Complex.cpow_add _ _ hn]
    congr 1
    ring
  rw [he]
  ring

/-- The original unrenormalized boundary current has no finite horizon limit. -/
theorem radialGreen_no_finite_horizon_limit (q : XiZeroCopy) (side : Bool) (a : ℂ) :
    ¬ Tendsto (radialGreen q side) atBot (𝓝 a) := by
  intro h
  have hr : 0 < (-(physicalFundamentalFrequency q side + 1)).re := by
    simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
    linarith [(frequency_real_interval q side).2]
  have hh := h.mul (power_along_horizon hr)
  simp only [mul_zero] at hh
  have he : Tendsto (fun t => radialGreen q side t /
      ((horizonCoordinate t : ℂ) *
        power (physicalFundamentalFrequency q side / 2) (horizonCoordinate t) ^ 2))
      atBot (𝓝 0) := by
    apply hh.congr'
    filter_upwards [eventually_lt_atBot (0 : ℝ)] with t ht
    rw [horizon_scale_eq q side (horizonCoordinate_interior t ht).1]
    simp only [power, Complex.cpow_neg, div_eq_mul_inv]
  exact radialGreen_horizon_coefficient_ne_zero q side
    (tendsto_nhds_unique (normalized_radialGreen_tendsto q side) he)

private def boundaryCoefficient (q : XiZeroCopy) (side : Bool) (z : ℝ) : ℂ :=
  2 * power (1/2) (1-z) * gaussGreen q side z

private theorem boundaryCoefficient_zero (q : XiZeroCopy) (side : Bool) :
    boundaryCoefficient q side 0 = center q / (4 * (1 + physicalFundamentalFrequency q side)) := by
  simp only [boundaryCoefficient, sub_zero, power, Complex.ofReal_one, Complex.one_cpow,
    Complex.ofReal_zero, gaussGreen_zero]
  field_simp
  ring

private theorem boundaryCoefficient_differentiableAt_zero (q : XiZeroCopy) (side : Bool) :
    DifferentiableAt ℝ (boundaryCoefficient q side) 0 := by
  have hq := gaussFactor_derivatives_continued
    (w := physicalFundamentalFrequency q side) (chi := physicalRadialFrequency q)
    false (by simp : ‖(0 : ℂ)‖ₑ < 1)
  have hr := gaussFactor_derivatives_continued
    (w := physicalFundamentalFrequency q side)
    (chi := physicalRadialFrequency (xiZeroCopyReflectEquiv q))
    false (by simp : ‖(0 : ℂ)‖ₑ < 1)
  have hg := (hr.1.mul hq.2).sub (hq.1.mul hr.2)
  have hp := (power_derivatives (1/2) (by norm_num : (0 : ℝ) < 1 - id 0)).1.scomp 0
    ((hasDerivAt_id (0 : ℝ)).const_sub 1)
  exact (hp.const_mul (2 : ℂ)).differentiableAt.mul hg.comp_ofReal.differentiableAt

private theorem radialGreen_boundaryCoefficient (q : XiZeroCopy) (side : Bool)
    (t : ℝ) (ht : t < 0) :
    radialGreen q side t =
      power (physicalFundamentalFrequency q side + 1) (horizonCoordinate t) *
        boundaryCoefficient q side (horizonCoordinate t) := by
  have hz := horizonCoordinate_interior t ht
  have hs : Real.sqrt (1 - horizonCoordinate t) = radialUnit t := by
    rw [horizonCoordinate, sub_sub_cancel, Real.sqrt_sq (radialUnit_bounds t ht).1.le]
  rw [radialGreen_eq, horizon_scale_eq q side hz.1, boundaryCoefficient,
    power_half_eq_sqrt (sub_nonneg.mpr hz.2.le), hs]
  ring

/-- Subtracting the exact source-derived leading current leaves a decaying remainder. -/
theorem radialGreen_sub_source_counterterm_tendsto_zero (q : XiZeroCopy) (side : Bool) :
    Tendsto (fun t => radialGreen q side t -
      power (physicalFundamentalFrequency q side + 1) (horizonCoordinate t) *
        (center q / (4 * (1 + physicalFundamentalFrequency q side)))) atBot (𝓝 0) := by
  have hs := (boundaryCoefficient_differentiableAt_zero q side).hasDerivAt.tendsto_slope_zero_right
  have hz : Tendsto horizonCoordinate atBot (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨horizonCoordinate_tendsto_horizon, ?_⟩
    filter_upwards [eventually_lt_atBot (0 : ℝ)] with t ht
    exact (horizonCoordinate_interior t ht).1
  have hh := hs.comp hz
  simp only [zero_add, Complex.real_smul, Complex.ofReal_inv,
    Function.comp_def, boundaryCoefficient_zero] at hh
  have hp : 0 < (physicalFundamentalFrequency q side + 2).re := by
    change 0 < (physicalFundamentalFrequency q side).re + 2
    linarith [(frequency_real_interval q side).1]
  have he := (power_along_horizon hp).mul hh
  simp only [zero_mul] at he
  apply he.congr'
  filter_upwards [eventually_lt_atBot (0 : ℝ)] with t ht
  have hn := Complex.ofReal_ne_zero.mpr (horizonCoordinate_interior t ht).1.ne'
  rw [radialGreen_boundaryCoefficient q side t ht]
  have he : power (physicalFundamentalFrequency q side + 2) (horizonCoordinate t) =
      power (physicalFundamentalFrequency q side + 1) (horizonCoordinate t) *
        (horizonCoordinate t : ℂ) := by
    dsimp only [power]
    rw [show physicalFundamentalFrequency q side + 2 =
      (physicalFundamentalFrequency q side + 1) + 1 by ring,
      Complex.cpow_add _ _ hn, Complex.cpow_one]
  rw [he]
  field_simp

/-- Among leading-power subtractions, a finite boundary value forces exactly the source coefficient. -/
theorem radialGreen_finite_subtraction_iff (q : XiZeroCopy) (side : Bool) (c : ℂ) :
    (∃ a : ℂ, Tendsto (fun t => radialGreen q side t -
      power (physicalFundamentalFrequency q side + 1) (horizonCoordinate t) * c)
      atBot (𝓝 a)) ↔ c = center q / (4 * (1 + physicalFundamentalFrequency q side)) := by
  constructor
  · rintro ⟨a, ha⟩
    have hr : 0 < (-(physicalFundamentalFrequency q side + 1)).re := by
      simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
      linarith [(frequency_real_interval q side).2]
    have hh := ha.mul (power_along_horizon hr)
    simp only [mul_zero] at hh
    have he : Tendsto (fun t => radialGreen q side t /
        ((horizonCoordinate t : ℂ) *
          power (physicalFundamentalFrequency q side / 2) (horizonCoordinate t) ^ 2) - c)
        atBot (𝓝 0) := by
      apply hh.congr'
      filter_upwards [eventually_lt_atBot (0 : ℝ)] with t ht
      have hz := (horizonCoordinate_interior t ht).1
      have hn := power_ne_zero (physicalFundamentalFrequency q side + 1) hz
      rw [horizon_scale_eq q side hz]
      change (_ - power (physicalFundamentalFrequency q side + 1) (horizonCoordinate t) * c) *
        power (-(physicalFundamentalFrequency q side + 1)) (horizonCoordinate t) = _
      rw [show power (-(physicalFundamentalFrequency q side + 1)) (horizonCoordinate t) =
        (power (physicalFundamentalFrequency q side + 1) (horizonCoordinate t))⁻¹
        from Complex.cpow_neg _ _]
      field_simp
    exact (sub_eq_zero.mp (tendsto_nhds_unique
      ((normalized_radialGreen_tendsto q side).sub_const c) he)).symm
  · intro hc
    rw [hc]
    exact ⟨0, radialGreen_sub_source_counterterm_tendsto_zero q side⟩

/-- The current uses actual derivatives of both original radial fields, including at the physical frequencies. -/
theorem radialGreen_actual (q : XiZeroCopy) (side : Bool) (t : ℝ) (ht : t < 0) :
    radialGreen q side t =
      tortoiseMode false (physicalFundamentalFrequency q side)
          (physicalRadialFrequency (xiZeroCopyReflectEquiv q)) t *
        deriv (tortoiseMode false (physicalFundamentalFrequency q side) (physicalRadialFrequency q)) t -
      tortoiseMode false (physicalFundamentalFrequency q side) (physicalRadialFrequency q) t *
        deriv (tortoiseMode false (physicalFundamentalFrequency q side)
          (physicalRadialFrequency (xiZeroCopyReflectEquiv q))) t := by
  have hd (r : XiZeroCopy) :
      HasDerivAt (tortoiseMode false (physicalFundamentalFrequency q side) (physicalRadialFrequency r))
        (tortoiseModeFirst false (physicalFundamentalFrequency q side) (physicalRadialFrequency r) t) t := by
    have hh := (horizon_derivatives_continued
      (w := physicalFundamentalFrequency q side) (chi := physicalRadialFrequency r)
      (horizonCoordinate_interior t ht)).1.scomp t (horizonCoordinate_hasDerivAt t)
    change HasDerivAt
      (fun x => horizon (physicalFundamentalFrequency q side) (physicalRadialFrequency r)
        (horizonCoordinate x))
      ((coordinateFirst t : ℂ) *
        horizonFirst (physicalFundamentalFrequency q side) (physicalRadialFrequency r)
          (horizonCoordinate t)) t
    convert hh using 1 <;> rfl
  rw [(hd q).deriv, (hd (xiZeroCopyReflectEquiv q)).deriv]
  rfl

/-- Original static point at time zero; only the radial coordinate tends to the horizon. -/
def horizonPoint (t : ℝ) (z : D4BMHorizon.Point) : Fin 4 → ℝ :=
  ![0, tortoiseRadius t, z 0, z 1]

/-- Exact normalization of the actual full left stream, retaining its coexact angular reader. -/
theorem normalized_stream_eq (r : XiZeroCopy) (w : ℂ) (j : Fin 2)
    (z : D4BMHorizon.Point) (t : ℝ) (ht : t < 0) :
    physicalLeftModeStream r w false j (horizonPoint t z) /
      ((tortoiseRadius t : ℂ) * power (w/2) (horizonCoordinate t)) =
      gaussFactor w (physicalRadialFrequency r) false (horizonCoordinate t) *
        D4BMLiteralCusp.vector (physicalAngularParameter r) j z := by
  have hr : (tortoiseRadius t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (ne_of_gt (lt_trans (by norm_num) (tortoiseRadius_exterior t ht)))
  have hp := power_ne_zero (w/2) (horizonCoordinate_interior t ht).1
  have ha : D4BMMetricReconstruction.angularPoint (horizonPoint t z) = z := by
    ext k
    fin_cases k <;> rfl
  simp only [physicalLeftModeStream, horizonPoint, Matrix.cons_val_zero,
    Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul,
    Matrix.cons_val_one, radiusLift, tortoise_original_inverse t ht]
  change _ * D4BMLiteralCusp.vector (physicalAngularParameter r) j
    (D4BMMetricReconstruction.angularPoint (horizonPoint t z)) / _ = _
  rw [ha]
  simp only [tortoiseMode, radialMode, Bool.false_eq_true, if_false, horizon, dress]
  field_simp

/-- Same-clock radial normalization leaves the full angular reader as the horizon trace. -/
theorem normalized_stream_tendsto (r : XiZeroCopy) (w : ℂ) (j : Fin 2)
    (z : D4BMHorizon.Point) :
    Tendsto (fun t => physicalLeftModeStream r w false j (horizonPoint t z) /
      ((tortoiseRadius t : ℂ) * power (w/2) (horizonCoordinate t))) atBot
      (𝓝 (D4BMLiteralCusp.vector (physicalAngularParameter r) j z)) := by
  have he := (gauss_along_horizon r w).mul_const
    (D4BMLiteralCusp.vector (physicalAngularParameter r) j z)
  simp only [one_mul] at he
  apply he.congr'
  filter_upwards [eventually_lt_atBot (0 : ℝ)] with t ht
  exact (normalized_stream_eq r w j z t ht).symm

/-- The leading full reflected-reader difference is an angular contribution, not zero. -/
theorem normalized_stream_difference_tendsto (q : XiZeroCopy) (side : Bool) (j : Fin 2)
    (z : D4BMHorizon.Point) :
    Tendsto (fun t =>
      (physicalLeftModeStream (xiZeroCopyReflectEquiv q)
          (physicalFundamentalFrequency q side) false j (horizonPoint t z) -
        physicalLeftModeStream q (physicalFundamentalFrequency q side) false j (horizonPoint t z)) /
        ((tortoiseRadius t : ℂ) *
          power (physicalFundamentalFrequency q side / 2) (horizonCoordinate t))) atBot
      (𝓝 (D4BMLiteralCusp.vector (physicalAngularParameter (xiZeroCopyReflectEquiv q)) j z -
        D4BMLiteralCusp.vector (physicalAngularParameter q) j z)) := by
  simpa only [sub_div] using
    (normalized_stream_tendsto (xiZeroCopyReflectEquiv q) (physicalFundamentalFrequency q side) j z).sub
      (normalized_stream_tendsto q (physicalFundamentalFrequency q side) j z)

end
end RHTower.D4BMRelativeReaderHorizon
