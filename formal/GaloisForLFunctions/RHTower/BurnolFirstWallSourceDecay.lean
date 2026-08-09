import GaloisForLFunctions.RHTower.BurnolFirstWallZeroDividedSource

/-!
# The bounded primitive of the coboundary and the quadratic decay of the divided shift

The two-scale coboundary `p(t) = fract t - fract 2t` is one-periodic with mean zero, so its
primitive `P(t) = ∫_0^t p` is one-periodic and bounded by `1`.  Because `Int.fract` is
right-continuous everywhere, `P` has a right derivative `p` at every point, which is exactly what
the fundamental theorem of calculus needs.

Integration by parts against `y^{-ρ-1}` therefore converts the tail moment of `p` into a boundary
term plus an absolutely convergent moment of the bounded primitive:

`∫_t^∞ p(y) y^{-ρ-1} dy = -P(t) t^{-ρ-1} + (ρ+1) ∫_t^∞ P(y) y^{-ρ-2} dy`.

Both terms are `O(t^{-σ-1})`, so the forward divided shift `g_ρ(t) = t^{ρ-1} ∫_t^∞ p y^{-ρ-1} dy`
decays quadratically.
-/

open Complex Real MeasureTheory Set Filter Topology intervalIntegral

noncomputable section

namespace RHTower

/-! ## Right-continuity of the coboundary -/

theorem burnolEventually_floor_eq_Ici (a : ℝ) : ∀ᶠ y in 𝓝[≥] a, (⌊y⌋ : ℝ) = (⌊a⌋ : ℝ) := by
  have hmem : Ioo ((⌊a⌋ : ℝ) - 1) ((⌊a⌋ : ℝ) + 1) ∈ 𝓝 a :=
    Ioo_mem_nhds (by linarith [Int.floor_le a]) (by linarith [Int.lt_floor_add_one a])
  filter_upwards [nhdsWithin_le_nhds hmem, self_mem_nhdsWithin] with y hy hy2
  have h1 : (⌊a⌋ : ℝ) ≤ y := le_trans (Int.floor_le a) hy2
  have h2 : y < (⌊a⌋ : ℝ) + 1 := hy.2
  rw [Int.floor_eq_iff.mpr ⟨h1, h2⟩]

theorem burnolTendsto_const_mul_nhdsWithin_Ici {c : ℝ} (hc : 0 < c) (a : ℝ) :
    Tendsto (fun y : ℝ => c * y) (𝓝[≥] a) (𝓝[≥] (c * a)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · exact ((continuous_const.mul continuous_id).tendsto a).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact mul_le_mul_of_nonneg_left hy hc.le

theorem burnolEventually_floor_mul_eq_Ici {c : ℝ} (hc : 0 < c) (a : ℝ) :
    ∀ᶠ y in 𝓝[≥] a, (⌊c * y⌋ : ℝ) = (⌊c * a⌋ : ℝ) :=
  (burnolTendsto_const_mul_nhdsWithin_Ici hc a).eventually (burnolEventually_floor_eq_Ici (c * a))

/-- **The coboundary is right-continuous everywhere.**  Both floors are locally constant to the
right, including at the jump points. -/
theorem continuousWithinAt_burnolFractPair_Ici (a : ℝ) :
    ContinuousWithinAt burnolFractPair (Ici a) a := by
  have hkey : burnolFractPair =ᶠ[𝓝[≥] a]
      fun y : ℝ => (y - (⌊a⌋ : ℝ)) - (2 * y - (⌊2 * a⌋ : ℝ)) := by
    filter_upwards [burnolEventually_floor_eq_Ici a,
      burnolEventually_floor_mul_eq_Ici (by norm_num : (0:ℝ) < 2) a] with y h1 h2
    rw [burnolFractPair, Int.fract, Int.fract, h1, h2]
  have hcont : ContinuousWithinAt
      (fun y : ℝ => (y - (⌊a⌋ : ℝ)) - (2 * y - (⌊2 * a⌋ : ℝ))) (Ici a) a := by
    fun_prop
  refine hcont.congr_of_eventuallyEq hkey ?_
  rw [burnolFractPair, Int.fract, Int.fract]

theorem measurable_burnolFractPair : Measurable burnolFractPair := by
  unfold burnolFractPair
  exact measurable_fract.sub (measurable_fract.comp (measurable_const_mul 2))

theorem intervalIntegrable_burnolFractPair (a b : ℝ) :
    IntervalIntegrable burnolFractPair volume a b := by
  constructor <;>
  · refine MeasureTheory.Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne
      measurable_burnolFractPair.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact abs_burnolFractPair_le_one x

/-! ## The bounded primitive -/

/-- The primitive of the two-scale coboundary. -/
def burnolFractPairPrimitive (t : ℝ) : ℝ := ∫ y in (0 : ℝ)..t, burnolFractPair y

theorem continuous_burnolFractPairPrimitive : Continuous burnolFractPairPrimitive :=
  intervalIntegral.continuous_primitive intervalIntegrable_burnolFractPair 0

/-- **The right derivative of the primitive is the coboundary, at every point.** -/
theorem hasDerivWithinAt_burnolFractPairPrimitive (a : ℝ) :
    HasDerivWithinAt burnolFractPairPrimitive (burnolFractPair a) (Ici a) a :=
  intervalIntegral.integral_hasDerivWithinAt_right (s := Ici a) (t := Ioi a)
    (intervalIntegrable_burnolFractPair 0 a)
    ⟨Ioi a, self_mem_nhdsWithin,
      measurable_burnolFractPair.aestronglyMeasurable.restrict⟩
    ((continuousWithinAt_burnolFractPair_Ici a).mono Ioi_subset_Ici_self)

theorem integral_fract_unit : (∫ y in (0 : ℝ)..1, Int.fract y) = 1 / 2 := by
  have hne : ∀ᵐ y : ℝ ∂volume, y ≠ 1 := by
    rw [MeasureTheory.ae_iff]
    simp
  have hcongr : (∫ y in (0 : ℝ)..1, Int.fract y) = ∫ y in (0 : ℝ)..1, y := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hne] with y hy1 hy
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hy
    exact Int.fract_eq_self.mpr ⟨le_of_lt hy.1, lt_of_le_of_ne hy.2 hy1⟩
  rw [hcongr, integral_id]
  norm_num

theorem integral_fract_two_unit : (∫ y in (0 : ℝ)..1, Int.fract (2 * y)) = 1 / 2 := by
  rw [intervalIntegral.integral_comp_mul_left (fun x : ℝ => Int.fract x) (by norm_num : (2:ℝ) ≠ 0)]
  have hper : Function.Periodic (fun x : ℝ => Int.fract x) 1 := fun x => Int.fract_add_one x
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun x : ℝ => Int.fract x) volume a b := by
    intro a b
    constructor <;>
    · refine MeasureTheory.Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne
        measurable_fract.aestronglyMeasurable ?_
      exact Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg x)]
        exact (Int.fract_lt_one x).le
  have hsplit : (∫ y in (0 : ℝ)..1, Int.fract y) + (∫ y in (1 : ℝ)..2, Int.fract y) =
      ∫ y in (0 : ℝ)..2, Int.fract y :=
    intervalIntegral.integral_add_adjacent_intervals (hint 0 1) (hint 1 2)
  have hshift : (∫ y in (1 : ℝ)..2, Int.fract y) = ∫ y in (0 : ℝ)..1, Int.fract y := by
    have h := hper.intervalIntegral_add_eq 1 0
    norm_num at h
    exact h
  rw [show (2 : ℝ) * 0 = 0 by ring, show (2 : ℝ) * 1 = 2 by ring, ← hsplit, hshift,
    integral_fract_unit]
  norm_num

/-- **The coboundary has mean zero.** -/
theorem integral_burnolFractPair_unit : (∫ y in (0 : ℝ)..1, burnolFractPair y) = 0 := by
  have hint1 : ∀ a b : ℝ, IntervalIntegrable (fun x : ℝ => Int.fract x) volume a b := by
    intro a b
    constructor <;>
    · refine MeasureTheory.Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne
        measurable_fract.aestronglyMeasurable ?_
      exact Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg x)]
        exact (Int.fract_lt_one x).le
  have hint2 : ∀ a b : ℝ, IntervalIntegrable (fun x : ℝ => Int.fract (2 * x)) volume a b := by
    intro a b
    constructor <;>
    · refine MeasureTheory.Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne
        (measurable_fract.comp (measurable_const_mul 2)).aestronglyMeasurable ?_
      exact Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
        exact (Int.fract_lt_one _).le
  have hsub : (∫ y in (0 : ℝ)..1, burnolFractPair y) =
      (∫ y in (0 : ℝ)..1, Int.fract y) - ∫ y in (0 : ℝ)..1, Int.fract (2 * y) := by
    rw [← intervalIntegral.integral_sub (hint1 0 1) (hint2 0 1)]
    rfl
  rw [hsub, integral_fract_unit, integral_fract_two_unit]
  ring

theorem burnolFractPairPrimitive_periodic : Function.Periodic burnolFractPairPrimitive 1 := by
  intro t
  have hsplit : burnolFractPairPrimitive t + (∫ y in t..(t + 1), burnolFractPair y) =
      burnolFractPairPrimitive (t + 1) :=
    intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_burnolFractPair 0 t)
      (intervalIntegrable_burnolFractPair t (t + 1))
  have hcell : (∫ y in t..(t + 1), burnolFractPair y) = 0 := by
    have h := burnolFractPair_periodic.intervalIntegral_add_eq t 0
    rw [zero_add] at h
    rw [h, integral_burnolFractPair_unit]
  rw [← hsplit, hcell, add_zero]

/-- **The primitive is bounded by one.**  It is periodic, and on a single cell the trivial bound
`|p| ≤ 1` applies. -/
theorem abs_burnolFractPairPrimitive_le_one (t : ℝ) : |burnolFractPairPrimitive t| ≤ 1 := by
  have hred : burnolFractPairPrimitive t = burnolFractPairPrimitive (Int.fract t) := by
    have h := burnolFractPairPrimitive_periodic.sub_int_mul_eq (x := t) ⌊t⌋
    rw [mul_one] at h
    rw [Int.fract, h]
  rw [hred, burnolFractPairPrimitive]
  have hbound : ‖∫ y in (0 : ℝ)..Int.fract t, burnolFractPair y‖ ≤ 1 * |Int.fract t - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun x _ => by
      rw [Real.norm_eq_abs]; exact abs_burnolFractPair_le_one x
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg (Int.fract_nonneg t), one_mul] at hbound
  exact le_trans hbound (Int.fract_lt_one t).le

/-! ## Integration by parts -/

/-- The moment kernel of the bounded primitive. -/
def burnolFractPairPrimitiveKernel (ρ : ℂ) (y : ℝ) : ℂ :=
  ((burnolFractPairPrimitive y : ℝ) : ℂ) * (y : ℂ) ^ (-(ρ + 2))

theorem hasDerivAt_burnolRealCpow {y : ℝ} (hy : 0 < y) (w : ℂ) :
    HasDerivAt (fun x : ℝ => (x : ℂ) ^ w) (w * (y : ℂ) ^ (w - 1)) y := by
  have hslit : ((y : ℝ) : ℂ) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using hy))
  have hb : HasDerivAt (fun x : ℂ => x ^ w) (w * ((y : ℝ) : ℂ) ^ (w - 1) * 1) ((y : ℝ) : ℂ) :=
    (hasDerivAt_id ((y : ℝ) : ℂ)).cpow_const hslit
  simpa using hb.comp_ofReal

theorem hasDerivWithinAt_burnolByPartsProduct {ρ : ℂ} {y : ℝ} (hy : 0 < y) :
    HasDerivWithinAt
      (fun x : ℝ => ((burnolFractPairPrimitive x : ℝ) : ℂ) * (x : ℂ) ^ (-(ρ + 1)))
      (burnolFractPairKernel ρ y - (ρ + 1) * burnolFractPairPrimitiveKernel ρ y) (Ici y) y := by
  have hP : HasDerivWithinAt (fun x : ℝ => ((burnolFractPairPrimitive x : ℝ) : ℂ))
      ((burnolFractPair y : ℝ) : ℂ) (Ici y) y :=
    (hasDerivWithinAt_burnolFractPairPrimitive y).ofReal_comp
  have hpow : HasDerivWithinAt (fun x : ℝ => (x : ℂ) ^ (-(ρ + 1)))
      (-(ρ + 1) * (y : ℂ) ^ (-(ρ + 1) - 1)) (Ici y) y :=
    (hasDerivAt_burnolRealCpow hy (-(ρ + 1))).hasDerivWithinAt
  have hmul := hP.mul hpow
  refine hmul.congr_deriv ?_
  rw [burnolFractPairKernel, burnolFractPairPrimitiveKernel,
    show -(ρ + 1) - 1 = -(ρ + 2) by ring]
  ring

theorem intervalIntegrable_burnolFractPairKernel {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    {t T : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    IntervalIntegrable (burnolFractPairKernel ρ) volume t T := by
  rw [intervalIntegrable_iff]
  refine (integrableOn_burnolFractPairKernel hρ0 hρ1).mono_set ?_
  rw [Set.uIoc_of_le htT]
  exact fun y hy => mem_Ioi.mpr (lt_trans ht hy.1)

theorem intervalIntegrable_burnolFractPairPrimitiveKernel {ρ : ℂ} {t T : ℝ} (ht : 0 < t)
    (htT : t ≤ T) : IntervalIntegrable (burnolFractPairPrimitiveKernel ρ) volume t T := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le htT]
  refine ContinuousOn.mul (Complex.continuous_ofReal.comp
    continuous_burnolFractPairPrimitive).continuousOn ?_
  intro y hy
  have hy0 : 0 < y := lt_of_lt_of_le ht hy.1
  exact ((hasDerivAt_burnolRealCpow hy0 (-(ρ + 2))).continuousAt).continuousWithinAt

/-- **Integration by parts on a finite window.** -/
theorem integral_burnolFractPairKernel_byParts {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    {t T : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    (∫ y in t..T, burnolFractPairKernel ρ y) =
      ((burnolFractPairPrimitive T : ℝ) : ℂ) * (T : ℂ) ^ (-(ρ + 1))
        - ((burnolFractPairPrimitive t : ℝ) : ℂ) * (t : ℂ) ^ (-(ρ + 1))
        + (ρ + 1) * ∫ y in t..T, burnolFractPairPrimitiveKernel ρ y := by
  have hint : IntervalIntegrable
      (fun y : ℝ => burnolFractPairKernel ρ y - (ρ + 1) * burnolFractPairPrimitiveKernel ρ y)
      volume t T :=
    (intervalIntegrable_burnolFractPairKernel hρ0 hρ1 ht htT).sub
      ((intervalIntegrable_burnolFractPairPrimitiveKernel ht htT).const_mul _)
  have hcont : ContinuousOn
      (fun x : ℝ => ((burnolFractPairPrimitive x : ℝ) : ℂ) * (x : ℂ) ^ (-(ρ + 1)))
      (Icc t T) := by
    refine ContinuousOn.mul (Complex.continuous_ofReal.comp
      continuous_burnolFractPairPrimitive).continuousOn ?_
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le ht hy.1
    exact ((hasDerivAt_burnolRealCpow hy0 (-(ρ + 1))).continuousAt).continuousWithinAt
  have hderiv : ∀ x ∈ Ioo t T, HasDerivWithinAt
      (fun x : ℝ => ((burnolFractPairPrimitive x : ℝ) : ℂ) * (x : ℂ) ^ (-(ρ + 1)))
      (burnolFractPairKernel ρ x - (ρ + 1) * burnolFractPairPrimitiveKernel ρ x) (Ioi x) x := by
    intro x hx
    exact (hasDerivWithinAt_burnolByPartsProduct (lt_trans ht hx.1)).mono Ioi_subset_Ici_self
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le htT hcont hderiv hint
  rw [intervalIntegral.integral_sub (intervalIntegrable_burnolFractPairKernel hρ0 hρ1 ht htT)
    ((intervalIntegrable_burnolFractPairPrimitiveKernel ht htT).const_mul _),
    intervalIntegral.integral_const_mul] at hftc
  linear_combination hftc

/-! ## The tail moment and the quadratic decay -/

theorem integrableOn_burnolFractPairPrimitiveKernel {ρ : ℂ} (hρ0 : 0 < ρ.re) {t : ℝ}
    (ht : 0 < t) : IntegrableOn (burnolFractPairPrimitiveKernel ρ) (Ioi t) := by
  have hmeas : AEStronglyMeasurable (burnolFractPairPrimitiveKernel ρ)
      (volume.restrict (Ioi t)) := by
    refine (ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi)
    refine ContinuousOn.mul (Complex.continuous_ofReal.comp
      continuous_burnolFractPairPrimitive).continuousOn ?_
    intro y hy
    exact ((hasDerivAt_burnolRealCpow (lt_trans ht hy) (-(ρ + 2))).continuousAt).continuousWithinAt
  refine Integrable.mono' (g := fun y : ℝ => y ^ (-(ρ.re + 2))) ?_ hmeas ?_
  · exact (integrableOn_Ioi_rpow_of_lt (by linarith) ht).congr_fun
      (fun _ _ => rfl) measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : 0 < y := lt_trans ht hy
    rw [burnolFractPairPrimitiveKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos hy0]
    have hre : (-(ρ + 2)).re = -(ρ.re + 2) := by
      rw [Complex.neg_re, Complex.add_re]
      norm_num
    rw [hre]
    have hP := abs_burnolFractPairPrimitive_le_one y
    have hpos : (0 : ℝ) < y ^ (-(ρ.re + 2)) := Real.rpow_pos_of_pos hy0 _
    nlinarith [hP, hpos, abs_nonneg (burnolFractPairPrimitive y)]

/-- **The tail moment of the coboundary.**  Integration by parts, in the limit. -/
theorem integral_burnolFractPairKernel_Ioi_eq {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    {t : ℝ} (ht : 0 < t) :
    (∫ y in Ioi t, burnolFractPairKernel ρ y) =
      -(((burnolFractPairPrimitive t : ℝ) : ℂ) * (t : ℂ) ^ (-(ρ + 1)))
        + (ρ + 1) * ∫ y in Ioi t, burnolFractPairPrimitiveKernel ρ y := by
  have hlhs : Tendsto (fun T : ℝ => ∫ y in t..T, burnolFractPairKernel ρ y) atTop
      (𝓝 (∫ y in Ioi t, burnolFractPairKernel ρ y)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi t
      (integrableOn_burnolFractPairKernel_Ioi hρ0 hρ1 ht) tendsto_id
  have hker : Tendsto (fun T : ℝ => ∫ y in t..T, burnolFractPairPrimitiveKernel ρ y) atTop
      (𝓝 (∫ y in Ioi t, burnolFractPairPrimitiveKernel ρ y)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi t
      (integrableOn_burnolFractPairPrimitiveKernel hρ0 ht) tendsto_id
  have hbdry : Tendsto
      (fun T : ℝ => ((burnolFractPairPrimitive T : ℝ) : ℂ) * (T : ℂ) ^ (-(ρ + 1))) atTop
      (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hdom : Tendsto (fun T : ℝ => T ^ (-(ρ.re + 1))) atTop (𝓝 0) :=
      _root_.tendsto_rpow_neg_atTop (by linarith)
    refine squeeze_zero' ?_ ?_ hdom
    · filter_upwards with T using norm_nonneg _
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_cpow_eq_rpow_re_of_pos hT]
      have hre : (-(ρ + 1)).re = -(ρ.re + 1) := by
        rw [Complex.neg_re, Complex.add_re]; norm_num
      rw [hre]
      have hP := abs_burnolFractPairPrimitive_le_one T
      have hpos : (0 : ℝ) < T ^ (-(ρ.re + 1)) := Real.rpow_pos_of_pos hT _
      nlinarith [hP, hpos, abs_nonneg (burnolFractPairPrimitive T)]
  have hrhs : Tendsto (fun T : ℝ =>
      ((burnolFractPairPrimitive T : ℝ) : ℂ) * (T : ℂ) ^ (-(ρ + 1))
        - ((burnolFractPairPrimitive t : ℝ) : ℂ) * (t : ℂ) ^ (-(ρ + 1))
        + (ρ + 1) * ∫ y in t..T, burnolFractPairPrimitiveKernel ρ y) atTop
      (𝓝 (0 - ((burnolFractPairPrimitive t : ℝ) : ℂ) * (t : ℂ) ^ (-(ρ + 1))
        + (ρ + 1) * ∫ y in Ioi t, burnolFractPairPrimitiveKernel ρ y)) :=
    (hbdry.sub tendsto_const_nhds).add (hker.const_mul _)
  have heq := tendsto_nhds_unique
    (hlhs.congr' (by
      filter_upwards [eventually_ge_atTop t] with T hT
      exact integral_burnolFractPairKernel_byParts hρ0 hρ1 ht hT)) hrhs
  rw [heq]
  ring

/-- **The tail moment is `O(t^{-σ-1})`.** -/
theorem norm_integral_burnolFractPairKernel_Ioi_le {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    {t : ℝ} (ht : 0 < t) :
    ‖∫ y in Ioi t, burnolFractPairKernel ρ y‖ ≤
      (1 + ‖ρ + 1‖ / (ρ.re + 1)) * t ^ (-(ρ.re + 1)) := by
  have hbdry : ‖((burnolFractPairPrimitive t : ℝ) : ℂ) * (t : ℂ) ^ (-(ρ + 1))‖ ≤
      t ^ (-(ρ.re + 1)) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos ht]
    have hre : (-(ρ + 1)).re = -(ρ.re + 1) := by
      rw [Complex.neg_re, Complex.add_re]; norm_num
    rw [hre]
    have hP := abs_burnolFractPairPrimitive_le_one t
    have hpos : (0 : ℝ) < t ^ (-(ρ.re + 1)) := Real.rpow_pos_of_pos ht _
    nlinarith [hP, hpos, abs_nonneg (burnolFractPairPrimitive t)]
  have hker : ‖∫ y in Ioi t, burnolFractPairPrimitiveKernel ρ y‖ ≤
      t ^ (-(ρ.re + 1)) / (ρ.re + 1) := by
    have hbound : ∀ᵐ y ∂(volume.restrict (Ioi t)),
        ‖burnolFractPairPrimitiveKernel ρ y‖ ≤ y ^ (-(ρ.re + 2)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      have hy0 : 0 < y := lt_trans ht hy
      rw [burnolFractPairPrimitiveKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_cpow_eq_rpow_re_of_pos hy0]
      have hre : (-(ρ + 2)).re = -(ρ.re + 2) := by
        rw [Complex.neg_re, Complex.add_re]; norm_num
      rw [hre]
      have hP := abs_burnolFractPairPrimitive_le_one y
      have hpos : (0 : ℝ) < y ^ (-(ρ.re + 2)) := Real.rpow_pos_of_pos hy0 _
      nlinarith [hP, hpos, abs_nonneg (burnolFractPairPrimitive y)]
    have hcmp := MeasureTheory.norm_integral_le_of_norm_le
      ((integrableOn_Ioi_rpow_of_lt (a := -(ρ.re + 2)) (by linarith) ht)) hbound
    rw [integral_Ioi_rpow_of_lt (by linarith : -(ρ.re + 2) < -1) ht] at hcmp
    have hval : -t ^ (-(ρ.re + 2) + 1) / (-(ρ.re + 2) + 1) = t ^ (-(ρ.re + 1)) / (ρ.re + 1) := by
      rw [show -(ρ.re + 2) + 1 = -(ρ.re + 1) by ring]
      field_simp
    rw [hval] at hcmp
    exact hcmp
  rw [integral_burnolFractPairKernel_Ioi_eq hρ0 hρ1 ht]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_neg]
  have hpos : (0 : ℝ) < ρ.re + 1 := by linarith
  have hstep : ‖ρ + 1‖ * ‖∫ y in Ioi t, burnolFractPairPrimitiveKernel ρ y‖ ≤
      ‖ρ + 1‖ * (t ^ (-(ρ.re + 1)) / (ρ.re + 1)) :=
    mul_le_mul_of_nonneg_left hker (norm_nonneg _)
  have hexp : (1 + ‖ρ + 1‖ / (ρ.re + 1)) * t ^ (-(ρ.re + 1)) =
      t ^ (-(ρ.re + 1)) + ‖ρ + 1‖ * (t ^ (-(ρ.re + 1)) / (ρ.re + 1)) := by
    field_simp
  have hb2 : ‖(ρ + 1) * ∫ y in Ioi t, burnolFractPairPrimitiveKernel ρ y‖ =
      ‖ρ + 1‖ * ‖∫ y in Ioi t, burnolFractPairPrimitiveKernel ρ y‖ := norm_mul _ _
  rw [hexp, hb2]
  linarith [hbdry, hstep]

/-- **Quadratic decay of the forward divided shift.**  The `t^{ρ-1}` prefactor exactly cancels the
`t^{-σ-1}` tail decay. -/
theorem norm_burnolZeroDividedSource_le {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) {t : ℝ}
    (ht : 0 < t) :
    ‖burnolZeroDividedSource ρ t‖ ≤ (1 + ‖ρ + 1‖ / (ρ.re + 1)) * t ^ (-2 : ℝ) := by
  rw [burnolZeroDividedSource_eq_tail ht, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
  have hre : (ρ - 1).re = ρ.re - 1 := by rw [Complex.sub_re, Complex.one_re]
  rw [hre]
  have hpre : (0 : ℝ) < t ^ (ρ.re - 1) := Real.rpow_pos_of_pos ht _
  have hstep := mul_le_mul_of_nonneg_left
    (norm_integral_burnolFractPairKernel_Ioi_le hρ0 hρ1 ht) hpre.le
  refine le_trans hstep (le_of_eq ?_)
  rw [show t ^ (ρ.re - 1) * ((1 + ‖ρ + 1‖ / (ρ.re + 1)) * t ^ (-(ρ.re + 1))) =
      (1 + ‖ρ + 1‖ / (ρ.re + 1)) * (t ^ (ρ.re - 1) * t ^ (-(ρ.re + 1))) by ring,
    ← Real.rpow_add ht]
  congr 2
  ring

end RHTower
