import GaloisForLFunctions.RHTower.BurnolReflectedPrimitive
import GaloisForLFunctions.RHTower.BurnolReflectedDividedShift

/-!
# The reflected boundary term

The shifted primitive `B(T) = ∫_0^T f₀^∨ + 1/2` tends to zero at rate `1/(T-1)` and has right
derivative `f₀^∨`.  Integrating by parts against `y^{ρ-1}` therefore gives

`T^{1-ρ} ∫_0^T f₀^∨(y) y^{ρ-1} dy = B(T) + (ρ-1) T^{1-ρ} ∫_T^∞ B(y) y^{ρ-2} dy`,

whose second term is bounded by `|ρ-1| (1-σ)^{-1} sup_{y ≥ T} |B(y)|`.  Both pieces vanish, so the
boundary term of the reflected potential vanishes.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-- The shifted reflected primitive. -/
def burnolReflectedShiftedMass (T : ℝ) : ℝ := burnolReflectedTruncMass T + 1 / 2

theorem abs_burnolReflectedShiftedMass_le {T : ℝ} (hT : 2 ≤ T) :
    |burnolReflectedShiftedMass T| ≤ 1 / (T - 1) :=
  abs_burnolReflectedTruncMass_add_half_le hT

theorem hasDerivWithinAt_burnolReflectedShiftedMass {a : ℝ} (ha : 0 ≤ a) :
    HasDerivWithinAt burnolReflectedShiftedMass (burnolReflectedSourceRC a) (Ici a) a := by
  have h := (hasDerivWithinAt_burnolReflectedTruncMass ha).add_const (1 / 2 : ℝ)
  exact h

theorem continuous_burnolReflectedShiftedMass_aux {T : ℝ} (hT : 0 ≤ T) :
    burnolReflectedShiftedMass T = (∫ t in (0 : ℝ)..T, burnolReflectedSourceRC t) + 1 / 2 := by
  rw [burnolReflectedShiftedMass, burnolReflectedTruncMass_eq_integral hT]

theorem continuousOn_burnolReflectedShiftedMass {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ContinuousOn burnolReflectedShiftedMass (Icc a b) := by
  have hcont : ContinuousOn (fun T : ℝ => ∫ t in (0 : ℝ)..T, burnolReflectedSourceRC t)
      (Icc a b) := by
    have h := intervalIntegral.continuousOn_primitive_interval'
      (intervalIntegrable_burnolReflectedSourceRC (le_trans ha hab))
      (by rw [Set.uIcc_of_le (le_trans ha hab)]; exact ⟨le_rfl, le_trans ha hab⟩)
    rw [Set.uIcc_of_le (le_trans ha hab)] at h
    exact h.mono (fun x hx => ⟨le_trans ha hx.1, hx.2⟩)
  refine ContinuousOn.congr
    (f := fun T : ℝ => (∫ t in (0 : ℝ)..T, burnolReflectedSourceRC t) + 1 / 2)
    (hcont.add continuousOn_const) fun x hx => ?_
  exact continuous_burnolReflectedShiftedMass_aux (le_trans ha hx.1)

theorem continuousOn_burnolReflectedShiftedMassIoi {T : ℝ} (hT : 0 < T) :
    ContinuousOn burnolReflectedShiftedMass (Ioi T) := by
  intro x hx
  have hx0 : T < x := hx
  have hmem : Icc (T / 2) (x + 1) ∈ 𝓝 x :=
    Icc_mem_nhds (by linarith) (by linarith)
  exact ((continuousOn_burnolReflectedShiftedMass (a := T / 2) (b := x + 1) (by linarith)
    (by linarith)).continuousAt hmem).continuousWithinAt

/-- A uniform bound on the shifted primitive. -/
theorem abs_burnolReflectedShiftedMass_le_seven (T : ℝ) (hT : 0 ≤ T) :
    |burnolReflectedShiftedMass T| ≤ 7 := by
  rcases le_or_gt 2 T with h | h
  · refine le_trans (abs_burnolReflectedShiftedMass_le h) ?_
    rw [div_le_iff₀ (by linarith)]
    linarith
  · have hb : ∀ x ∈ Set.uIoc (0 : ℝ) T, ‖burnolReflectedSourceRC x‖ ≤ 3 := by
      intro x hx
      rw [Set.uIoc_of_le hT] at hx
      rw [Real.norm_eq_abs]
      refine le_trans (abs_burnolReflectedSourceRC_le hx.1.le) ?_
      linarith [hx.2]
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hT] at hbound
    rw [continuous_burnolReflectedShiftedMass_aux hT]
    have : |(∫ t in (0 : ℝ)..T, burnolReflectedSourceRC t) + 1 / 2| ≤
        |∫ t in (0 : ℝ)..T, burnolReflectedSourceRC t| + 1 / 2 := by
      refine le_trans (abs_add_le _ _) ?_
      norm_num
    linarith

theorem tendsto_burnolReflectedShiftedMass :
    Tendsto burnolReflectedShiftedMass atTop (𝓝 0) := by
  have hdom : Tendsto (fun T : ℝ => 1 / (T - 1)) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds (tendsto_atTop_add_const_right _ (-1) tendsto_id)
  have hsq : Tendsto (fun T : ℝ => |burnolReflectedShiftedMass T|) atTop (𝓝 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall fun _ => abs_nonneg _) ?_ hdom
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with T hT
    exact abs_burnolReflectedShiftedMass_le hT
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [Real.norm_eq_abs] using hsq


/-! ## Integration by parts against the shifted primitive -/

/-- The right-continuous reflected kernel. -/
def burnolReflectedKernelRC (ρ : ℂ) (y : ℝ) : ℂ :=
  ((burnolReflectedSourceRC y : ℝ) : ℂ) * (y : ℂ) ^ (ρ - 1)

/-- The moment kernel of the shifted primitive. -/
def burnolReflectedShiftedKernel (ρ : ℂ) (y : ℝ) : ℂ :=
  ((burnolReflectedShiftedMass y : ℝ) : ℂ) * (y : ℂ) ^ (ρ - 2)

theorem burnolReflectedKernelRC_ae (ρ : ℂ) :
    burnolReflectedKernelRC ρ =ᵐ[volume.restrict (Ioi (0 : ℝ))] burnolReflectedKernel ρ := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi, burnolReflectedSourceRC_ae] with y hy hrc
  rw [burnolReflectedKernelRC, burnolReflectedKernel,
    burnolReflectedRawSource_eq_real (mem_Ioi.mp hy), hrc,
    show -((1 : ℂ) - ρ) = ρ - 1 by ring]

theorem norm_burnolReflectedShiftedKernel_le {ρ : ℂ} {y : ℝ} (hy : 0 < y) :
    ‖burnolReflectedShiftedKernel ρ y‖ ≤ 7 * y ^ (ρ.re - 2) := by
  rw [burnolReflectedShiftedKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos hy]
  have hre : (ρ - 2).re = ρ.re - 2 := by
    rw [Complex.sub_re]
    norm_num
  rw [hre]
  have hb := abs_burnolReflectedShiftedMass_le_seven y hy.le
  have hp : (0 : ℝ) < y ^ (ρ.re - 2) := Real.rpow_pos_of_pos hy _
  nlinarith [hb, hp, abs_nonneg (burnolReflectedShiftedMass y)]

theorem norm_burnolReflectedShiftedKernel_le' {ρ : ℂ} {T y : ℝ} (hT : 2 ≤ T) (hy : T ≤ y) :
    ‖burnolReflectedShiftedKernel ρ y‖ ≤ (1 / (T - 1)) * y ^ (ρ.re - 2) := by
  have hy0 : (0 : ℝ) < y := by linarith
  have hy2 : (2 : ℝ) ≤ y := le_trans hT hy
  rw [burnolReflectedShiftedKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos hy0]
  have hre : (ρ - 2).re = ρ.re - 2 := by rw [Complex.sub_re]; norm_num
  rw [hre]
  have hb := abs_burnolReflectedShiftedMass_le hy2
  have hmono : 1 / (y - 1) ≤ 1 / (T - 1) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    linarith
  have hp : (0 : ℝ) < y ^ (ρ.re - 2) := Real.rpow_pos_of_pos hy0 _
  nlinarith [hb, hmono, hp, abs_nonneg (burnolReflectedShiftedMass y)]

theorem integrableOn_burnolReflectedShiftedKernel {ρ : ℂ} (hρ1 : ρ.re < 1) {T : ℝ} (hT : 0 < T) :
    IntegrableOn (burnolReflectedShiftedKernel ρ) (Ioi T) := by
  have hmeas : AEStronglyMeasurable (burnolReflectedShiftedKernel ρ)
      (volume.restrict (Ioi T)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.mul ?_ ?_
    · exact (Complex.continuous_ofReal.comp_continuousOn
        (continuousOn_burnolReflectedShiftedMassIoi hT))
    · intro y hy
      exact ((hasDerivAt_burnolRealCpow (lt_trans hT hy) (ρ - 2)).continuousAt).continuousWithinAt
  refine MeasureTheory.Integrable.mono' (g := fun y : ℝ => 7 * y ^ (ρ.re - 2))
    ((integrableOn_Ioi_rpow_of_lt (a := ρ.re - 2) (by linarith) hT).const_mul 7) hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact norm_burnolReflectedShiftedKernel_le (lt_trans hT hy)


theorem hasDerivWithinAt_burnolReflectedByParts {ρ : ℂ} {y : ℝ} (hy : 0 < y) :
    HasDerivWithinAt
      (fun x : ℝ => ((burnolReflectedShiftedMass x : ℝ) : ℂ) * (x : ℂ) ^ (ρ - 1))
      (burnolReflectedKernelRC ρ y + (ρ - 1) * burnolReflectedShiftedKernel ρ y) (Ici y) y := by
  have hB : HasDerivWithinAt (fun x : ℝ => ((burnolReflectedShiftedMass x : ℝ) : ℂ))
      ((burnolReflectedSourceRC y : ℝ) : ℂ) (Ici y) y :=
    (hasDerivWithinAt_burnolReflectedShiftedMass hy.le).ofReal_comp
  have hpow : HasDerivWithinAt (fun x : ℝ => (x : ℂ) ^ (ρ - 1))
      ((ρ - 1) * (y : ℂ) ^ (ρ - 1 - 1)) (Ici y) y :=
    (hasDerivAt_burnolRealCpow hy (ρ - 1)).hasDerivWithinAt
  refine (hB.mul hpow).congr_deriv ?_
  rw [burnolReflectedKernelRC, burnolReflectedShiftedKernel, show ρ - 1 - 1 = ρ - 2 by ring]
  ring

theorem integrableOn_burnolReflectedKernelRC {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) :
    IntegrableOn (burnolReflectedKernelRC ρ) (Ioi (0 : ℝ)) :=
  (integrableOn_burnolReflectedKernel hρ0 hρ1).congr_fun_ae (burnolReflectedKernelRC_ae ρ).symm

theorem intervalIntegrable_burnolReflectedKernelRC {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    {T T' : ℝ} (hT : 0 < T) (hTT : T ≤ T') :
    IntervalIntegrable (burnolReflectedKernelRC ρ) volume T T' := by
  rw [intervalIntegrable_iff, Set.uIoc_of_le hTT]
  exact (integrableOn_burnolReflectedKernelRC hρ0 hρ1).mono_set
    (fun y hy => mem_Ioi.mpr (lt_trans hT hy.1))

theorem intervalIntegrable_burnolReflectedShiftedKernel {ρ : ℂ} (hρ1 : ρ.re < 1)
    {T T' : ℝ} (hT : 0 < T) (hTT : T ≤ T') :
    IntervalIntegrable (burnolReflectedShiftedKernel ρ) volume T T' := by
  rw [intervalIntegrable_iff, Set.uIoc_of_le hTT]
  exact (integrableOn_burnolReflectedShiftedKernel hρ1 hT).mono_set
    (fun y hy => mem_Ioi.mpr hy.1)

/-- **Integration by parts against the shifted primitive.** -/
theorem integral_burnolReflectedKernelRC_byParts {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    {T T' : ℝ} (hT : 0 < T) (hTT : T ≤ T') :
    (∫ y in T..T', burnolReflectedKernelRC ρ y) =
      ((burnolReflectedShiftedMass T' : ℝ) : ℂ) * (T' : ℂ) ^ (ρ - 1)
        - ((burnolReflectedShiftedMass T : ℝ) : ℂ) * (T : ℂ) ^ (ρ - 1)
        - (ρ - 1) * ∫ y in T..T', burnolReflectedShiftedKernel ρ y := by
  have hcont : ContinuousOn
      (fun x : ℝ => ((burnolReflectedShiftedMass x : ℝ) : ℂ) * (x : ℂ) ^ (ρ - 1))
      (Icc T T') := by
    refine ContinuousOn.mul ?_ ?_
    · refine Complex.continuous_ofReal.comp_continuousOn ?_
      exact (continuousOn_burnolReflectedShiftedMass (a := T) (b := T') hT.le hTT)
    · intro y hy
      have hc := (hasDerivAt_burnolRealCpow (lt_of_lt_of_le hT hy.1) (ρ - 1)).continuousAt
      exact hc.continuousWithinAt
  have hderiv : ∀ x ∈ Ioo T T', HasDerivWithinAt
      (fun x : ℝ => ((burnolReflectedShiftedMass x : ℝ) : ℂ) * (x : ℂ) ^ (ρ - 1))
      (burnolReflectedKernelRC ρ x + (ρ - 1) * burnolReflectedShiftedKernel ρ x) (Ioi x) x :=
    fun x hx => (hasDerivWithinAt_burnolReflectedByParts (lt_trans hT hx.1)).mono
      Ioi_subset_Ici_self
  have hint : IntervalIntegrable
      (fun y : ℝ => burnolReflectedKernelRC ρ y + (ρ - 1) * burnolReflectedShiftedKernel ρ y)
      volume T T' :=
    (intervalIntegrable_burnolReflectedKernelRC hρ0 hρ1 hT hTT).add
      ((intervalIntegrable_burnolReflectedShiftedKernel hρ1 hT hTT).const_mul _)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hTT hcont hderiv hint
  rw [intervalIntegral.integral_add (intervalIntegrable_burnolReflectedKernelRC hρ0 hρ1 hT hTT)
    ((intervalIntegrable_burnolReflectedShiftedKernel hρ1 hT hTT).const_mul _),
    intervalIntegral.integral_const_mul] at hftc
  linear_combination hftc


/-! ## The boundary term vanishes -/

theorem integral_burnolReflectedKernelRC_Ioi {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    {T : ℝ} (hT : 0 < T) :
    (∫ y in Ioi T, burnolReflectedKernelRC ρ y) =
      -(((burnolReflectedShiftedMass T : ℝ) : ℂ) * (T : ℂ) ^ (ρ - 1))
        - (ρ - 1) * ∫ y in Ioi T, burnolReflectedShiftedKernel ρ y := by
  have hL : Tendsto (fun T' : ℝ => ∫ y in T..T', burnolReflectedKernelRC ρ y) atTop
      (𝓝 (∫ y in Ioi T, burnolReflectedKernelRC ρ y)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi T
      ((integrableOn_burnolReflectedKernelRC hρ0 hρ1).mono_set
        (fun y hy => mem_Ioi.mpr (lt_trans hT hy))) tendsto_id
  have hS : Tendsto (fun T' : ℝ => ∫ y in T..T', burnolReflectedShiftedKernel ρ y) atTop
      (𝓝 (∫ y in Ioi T, burnolReflectedShiftedKernel ρ y)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi T
      (integrableOn_burnolReflectedShiftedKernel hρ1 hT) tendsto_id
  have hB : Tendsto
      (fun T' : ℝ => ((burnolReflectedShiftedMass T' : ℝ) : ℂ) * (T' : ℂ) ^ (ρ - 1)) atTop
      (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hdom : Tendsto (fun T' : ℝ => 7 * T' ^ (ρ.re - 1)) atTop (𝓝 0) := by
      have h := (_root_.tendsto_rpow_neg_atTop (by linarith : (0:ℝ) < 1 - ρ.re)).const_mul (7 : ℝ)
      simpa [show -(1 - ρ.re) = ρ.re - 1 by ring] using h
    refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ hdom
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T' hT'
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos hT']
    have hre : (ρ - 1).re = ρ.re - 1 := by rw [Complex.sub_re]; norm_num
    rw [hre]
    have hb := abs_burnolReflectedShiftedMass_le_seven T' hT'.le
    have hp : (0 : ℝ) < T' ^ (ρ.re - 1) := Real.rpow_pos_of_pos hT' _
    nlinarith [hb, hp, abs_nonneg (burnolReflectedShiftedMass T')]
  have hconst : Tendsto
      (fun _ : ℝ => ((burnolReflectedShiftedMass T : ℝ) : ℂ) * ((T : ℝ) : ℂ) ^ (ρ - 1)) atTop
      (𝓝 (((burnolReflectedShiftedMass T : ℝ) : ℂ) * ((T : ℝ) : ℂ) ^ (ρ - 1))) :=
    tendsto_const_nhds
  have hR := (hB.sub hconst).sub (hS.const_mul (ρ - 1))
  refine tendsto_nhds_unique (hL.congr' ?_) (by simpa using hR)
  filter_upwards [eventually_ge_atTop T] with T' hT'
  exact integral_burnolReflectedKernelRC_byParts hρ0 hρ1 hT hT'

/-- **The reflected boundary term vanishes.** -/
theorem tendsto_burnolReflectedBoundary {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    (hxi : xi ρ = 0) :
    Tendsto (fun T : ℝ => (T : ℂ) ^ (1 - ρ) *
      ∫ y in Ioc (0 : ℝ) T, burnolReflectedKernel ρ y) atTop (𝓝 0) := by
  have hform : ∀ T : ℝ, 2 ≤ T → (T : ℂ) ^ (1 - ρ) *
      (∫ y in Ioc (0 : ℝ) T, burnolReflectedKernel ρ y) =
      ((burnolReflectedShiftedMass T : ℝ) : ℂ) +
        (ρ - 1) * ((T : ℂ) ^ (1 - ρ) * ∫ y in Ioi T, burnolReflectedShiftedKernel ρ y) := by
    intro T hT2
    have hT : 0 < T := by linarith
    have hTne : ((T : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
    have hRC : (∫ y in Ioi T, burnolReflectedKernel ρ y) =
        ∫ y in Ioi T, burnolReflectedKernelRC ρ y := by
      refine (setIntegral_congr_ae measurableSet_Ioi ?_).symm
      have hmono : volume.restrict (Ioi T) ≤ volume.restrict (Ioi (0 : ℝ)) :=
        Measure.restrict_mono (fun x hx => mem_Ioi.mpr (lt_trans hT hx)) le_rfl
      exact (ae_restrict_iff' measurableSet_Ioi).mp
        (((burnolReflectedKernelRC_ae ρ).filter_mono (ae_mono hmono)))
    rw [xiDivisor_integral_burnolReflectedKernel_Ioc hρ0 hρ1 hxi hT, hRC,
      integral_burnolReflectedKernelRC_Ioi hρ0 hρ1 hT]
    have hcancel : ((T : ℝ) : ℂ) ^ (1 - ρ) * ((T : ℝ) : ℂ) ^ (ρ - 1) = 1 := by
      rw [← Complex.cpow_add _ _ hTne, show (1 - ρ) + (ρ - 1) = (0 : ℂ) by ring,
        Complex.cpow_zero]
    calc ((T : ℝ) : ℂ) ^ (1 - ρ) *
          -(-(((burnolReflectedShiftedMass T : ℝ) : ℂ) * ((T : ℝ) : ℂ) ^ (ρ - 1)) -
            (ρ - 1) * ∫ y in Ioi T, burnolReflectedShiftedKernel ρ y)
        = (((T : ℝ) : ℂ) ^ (1 - ρ) * ((T : ℝ) : ℂ) ^ (ρ - 1)) *
            ((burnolReflectedShiftedMass T : ℝ) : ℂ) +
            (ρ - 1) * (((T : ℝ) : ℂ) ^ (1 - ρ) *
              ∫ y in Ioi T, burnolReflectedShiftedKernel ρ y) := by ring
      _ = _ := by rw [hcancel, one_mul]
  have hb : Tendsto (fun T : ℝ => ((burnolReflectedShiftedMass T : ℝ) : ℂ)) atTop (𝓝 0) := by
    have h := (Complex.continuous_ofReal.tendsto _).comp tendsto_burnolReflectedShiftedMass
    simpa [Function.comp_def] using h
  have hrem : Tendsto (fun T : ℝ => (ρ - 1) * ((T : ℂ) ^ (1 - ρ) *
      ∫ y in Ioi T, burnolReflectedShiftedKernel ρ y)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hdom : Tendsto (fun T : ℝ => ‖ρ - 1‖ * (7 / (1 - ρ.re)) * (1 / (T - 1))) atTop
        (𝓝 0) := by
      have h : Tendsto (fun T : ℝ => 1 / (T - 1)) atTop (𝓝 0) :=
        Filter.Tendsto.div_atTop tendsto_const_nhds
          (tendsto_atTop_add_const_right _ (-1) tendsto_id)
      simpa using h.const_mul (‖ρ - 1‖ * (7 / (1 - ρ.re)))
    refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ hdom
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with T hT2
    have hT : 0 < T := by linarith
    have hbnd : ‖∫ y in Ioi T, burnolReflectedShiftedKernel ρ y‖ ≤
        (1 / (T - 1)) * (T ^ (ρ.re - 1) / (1 - ρ.re)) := by
      have hcmp := MeasureTheory.norm_integral_le_of_norm_le
        ((integrableOn_Ioi_rpow_of_lt (a := ρ.re - 2) (by linarith) hT).const_mul (1 / (T - 1)))
        (by
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
          exact norm_burnolReflectedShiftedKernel_le' hT2 (le_of_lt hy))
      rw [MeasureTheory.integral_const_mul,
        integral_Ioi_rpow_of_lt (by linarith : ρ.re - 2 < -1) hT] at hcmp
      refine le_trans hcmp (le_of_eq ?_)
      rw [show ρ.re - 2 + 1 = ρ.re - 1 by ring]
      have hne : (1 : ℝ) - ρ.re ≠ 0 := by linarith
      have hne' : ρ.re - 1 ≠ 0 := by intro hc; apply hne; linarith
      field_simp
      ring
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hT]
    have hre : (1 - ρ).re = 1 - ρ.re := by rw [Complex.sub_re, Complex.one_re]
    rw [hre]
    have hpow : (0 : ℝ) < T ^ (1 - ρ.re) := Real.rpow_pos_of_pos hT _
    have hprod : T ^ (1 - ρ.re) * ((1 / (T - 1)) * (T ^ (ρ.re - 1) / (1 - ρ.re))) =
        (1 / (1 - ρ.re)) * (1 / (T - 1)) := by
      rw [show T ^ (1 - ρ.re) * ((1 / (T - 1)) * (T ^ (ρ.re - 1) / (1 - ρ.re))) =
          (T ^ (1 - ρ.re) * T ^ (ρ.re - 1)) * (1 / (T - 1)) / (1 - ρ.re) by ring,
        ← Real.rpow_add hT, show 1 - ρ.re + (ρ.re - 1) = 0 by ring, Real.rpow_zero]
      ring
    have hstep := mul_le_mul_of_nonneg_left hbnd hpow.le
    have hTinv : (0 : ℝ) ≤ 1 / (T - 1) := by
      have : (0 : ℝ) < T - 1 := by linarith
      positivity
    have hfinal : T ^ (1 - ρ.re) * ‖∫ y in Ioi T, burnolReflectedShiftedKernel ρ y‖ ≤
        (7 / (1 - ρ.re)) * (1 / (T - 1)) := by
      refine le_trans hstep ?_
      rw [hprod]
      have h1 : (1 : ℝ) / (1 - ρ.re) ≤ 7 / (1 - ρ.re) := by
        rw [div_le_div_iff₀ (by linarith) (by linarith)]
        linarith
      nlinarith [h1, hTinv]
    have hn := norm_nonneg (ρ - 1)
    nlinarith [hfinal, hn]

  have hsum := hb.add hrem
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with T hT
  exact (hform T hT).symm


/-! ## Sharp tail bounds -/

theorem norm_integral_burnolReflectedShiftedKernel_le {ρ : ℂ} (hρ1 : ρ.re < 1) {T : ℝ}
    (hT2 : 2 ≤ T) :
    ‖∫ y in Ioi T, burnolReflectedShiftedKernel ρ y‖ ≤
      (1 / (T - 1)) * (T ^ (ρ.re - 1) / (1 - ρ.re)) := by
  have hT : (0 : ℝ) < T := by linarith
  have hcmp := MeasureTheory.norm_integral_le_of_norm_le
    ((integrableOn_Ioi_rpow_of_lt (a := ρ.re - 2) (by linarith) hT).const_mul (1 / (T - 1)))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact norm_burnolReflectedShiftedKernel_le' hT2 (le_of_lt hy))
  rw [MeasureTheory.integral_const_mul,
    integral_Ioi_rpow_of_lt (by linarith : ρ.re - 2 < -1) hT] at hcmp
  refine le_trans hcmp (le_of_eq ?_)
  rw [show ρ.re - 2 + 1 = ρ.re - 1 by ring]
  have hne : (1 : ℝ) - ρ.re ≠ 0 := by linarith
  have hne' : ρ.re - 1 ≠ 0 := by intro hc; apply hne; linarith
  field_simp
  ring

theorem norm_integral_burnolReflectedKernelRC_Ioi_le {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    {T : ℝ} (hT2 : 2 ≤ T) :
    ‖∫ y in Ioi T, burnolReflectedKernelRC ρ y‖ ≤
      (1 + ‖ρ - 1‖ / (1 - ρ.re)) * (T ^ (ρ.re - 1) / (T - 1)) := by
  have hT : (0 : ℝ) < T := by linarith
  have hT1 : (0 : ℝ) < T - 1 := by linarith
  have hpow : (0 : ℝ) < T ^ (ρ.re - 1) := Real.rpow_pos_of_pos hT _
  rw [integral_burnolReflectedKernelRC_Ioi hρ0 hρ1 hT]
  refine le_trans (norm_sub_le _ _) ?_
  have hb1 : ‖((burnolReflectedShiftedMass T : ℝ) : ℂ) * ((T : ℝ) : ℂ) ^ (ρ - 1)‖ ≤
      (1 / (T - 1)) * T ^ (ρ.re - 1) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos hT]
    have hre : (ρ - 1).re = ρ.re - 1 := by rw [Complex.sub_re]; norm_num
    rw [hre]
    have hb := abs_burnolReflectedShiftedMass_le hT2
    nlinarith [hb, hpow, abs_nonneg (burnolReflectedShiftedMass T)]
  have hb2 : ‖(ρ - 1) * ∫ y in Ioi T, burnolReflectedShiftedKernel ρ y‖ ≤
      ‖ρ - 1‖ * ((1 / (T - 1)) * (T ^ (ρ.re - 1) / (1 - ρ.re))) := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (norm_integral_burnolReflectedShiftedKernel_le hρ1 hT2) (norm_nonneg _)
  rw [norm_neg]
  have hid : (1 + ‖ρ - 1‖ / (1 - ρ.re)) * (T ^ (ρ.re - 1) / (T - 1)) =
      (1 / (T - 1)) * T ^ (ρ.re - 1) +
        ‖ρ - 1‖ * ((1 / (T - 1)) * (T ^ (ρ.re - 1) / (1 - ρ.re))) := by
    have hne : (1 : ℝ) - ρ.re ≠ 0 := by linarith
    field_simp
  rw [hid]
  linarith [hb1, hb2]

end RHTower
