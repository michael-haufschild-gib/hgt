import GaloisForLFunctions.RHTower.BurnolFirstWallSourceDecay

/-!
# The improper mass of the raw Burnol source

The raw source `f₀(t) = p(t)/t` is bounded by one on the whole positive ray, but it is not
absolutely integrable at infinity.  Its improper mass is nevertheless exactly computable: the
dyadic substitution collapses the truncated integral to a single window,

`∫_0^R f₀ = -∫_R^{2R} fract(x)/x dx`,

whose leading term is the mean `1/2` of the fractional part and whose centred remainder is
controlled by the bounded periodic primitive `Q(x) = ∫_0^x (fract - 1/2)`, itself bounded by `1/8`.
Hence

`∫_0^∞ f₀ = -(log 2)/2`.
-/

open Complex Real MeasureTheory Set Filter Topology intervalIntegral

noncomputable section

namespace RHTower

/-! ## The raw source is bounded -/

/-- The fixed prime-two Burnol source on the positive ray. -/
def burnolRawSource (t : ℝ) : ℝ := burnolFractPair t / t

theorem measurable_burnolRawSource : Measurable burnolRawSource :=
  measurable_burnolFractPair.div measurable_id

theorem burnolFractPair_of_mem_Ico_half_one {t : ℝ} (h0 : 1 / 2 ≤ t) (h1 : t < 1) :
    burnolFractPair t = 1 - t := by
  have hf1 : Int.fract t = t := Int.fract_eq_self.mpr ⟨by linarith, h1⟩
  have hfl : ⌊2 * t⌋ = 1 := by
    refine Int.floor_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
  have hf2 : Int.fract (2 * t) = 2 * t - 1 := by
    rw [Int.fract, hfl]
    norm_num
  rw [burnolFractPair, hf1, hf2]
  ring

theorem abs_burnolFractPair_le_of_lt_one {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) :
    |burnolFractPair t| ≤ t := by
  rcases lt_or_ge t (1 / 2) with h | h
  · rw [burnolFractPair_of_lt_half h0 h, abs_neg, abs_of_nonneg h0]
  · rw [burnolFractPair_of_mem_Ico_half_one h h1, abs_of_nonneg (by linarith)]
    linarith

/-- **The raw source is bounded by one.**  Below `1` the numerator is at most `t`; above `1` it is
at most `1`. -/
theorem abs_burnolRawSource_le_one (t : ℝ) (ht : 0 ≤ t) : |burnolRawSource t| ≤ 1 := by
  rcases eq_or_lt_of_le ht with h | h
  · rw [burnolRawSource, ← h]
    norm_num
  rcases lt_or_ge t 1 with h1 | h1
  · rw [burnolRawSource, abs_div, abs_of_pos h, div_le_one h]
    exact abs_burnolFractPair_le_of_lt_one ht h1
  · rw [burnolRawSource, abs_div, abs_of_pos h, div_le_one h]
    exact le_trans (abs_burnolFractPair_le_one t) h1

/-- Bounded measurable functions are interval integrable on the nonnegative ray. -/
theorem burnolIntervalIntegrable_of_bounded_nonneg {f : ℝ → ℝ} (hm : Measurable f) {M : ℝ}
    (hM : ∀ x : ℝ, 0 ≤ x → |f x| ≤ M) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable f volume a b := by
  constructor <;>
  · refine MeasureTheory.Measure.integrableOn_of_bounded (M := M) measure_Ioc_lt_top.ne
      hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Real.norm_eq_abs]
    refine hM x (le_of_lt (lt_of_le_of_lt ?_ hx.1))
    first
    | exact ha
    | exact hb

theorem intervalIntegrable_burnolRawSource {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable burnolRawSource volume a b :=
  burnolIntervalIntegrable_of_bounded_nonneg measurable_burnolRawSource
    abs_burnolRawSource_le_one ha hb

/-- The unnormalized Mellin density of the fractional part. -/
def burnolFractDensity (x : ℝ) : ℝ := Int.fract x / x

theorem measurable_burnolFractDensity : Measurable burnolFractDensity :=
  measurable_fract.div measurable_id

theorem abs_burnolFractDensity_le_one {x : ℝ} (hx : 0 ≤ x) : |burnolFractDensity x| ≤ 1 := by
  rcases eq_or_lt_of_le hx with h | h
  · rw [burnolFractDensity, ← h]
    norm_num
  rw [burnolFractDensity, abs_div, abs_of_pos h, div_le_one h,
    abs_of_nonneg (Int.fract_nonneg x)]
  rcases lt_or_ge x 1 with h1 | h1
  · rw [Int.fract_eq_self.mpr ⟨hx, h1⟩]
  · exact le_trans (Int.fract_lt_one x).le h1

theorem intervalIntegrable_burnolFractDensity {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable burnolFractDensity volume a b :=
  burnolIntervalIntegrable_of_bounded_nonneg measurable_burnolFractDensity
    (fun _ hx => abs_burnolFractDensity_le_one hx) ha hb

/-- **The dyadic collapse.**  The truncated mass of the raw source is a single dyadic window of the
fractional-part density. -/
theorem integral_burnolRawSource_eq_neg_window {R : ℝ} (hR : 0 ≤ R) :
    (∫ t in (0 : ℝ)..R, burnolRawSource t) = -∫ x in R..(2 * R), burnolFractDensity x := by
  have hsub : (∫ t in (0 : ℝ)..R, burnolRawSource t) =
      (∫ t in (0 : ℝ)..R, burnolFractDensity t) -
        ∫ t in (0 : ℝ)..R, 2 * burnolFractDensity (2 * t) := by
    have hint2 : IntervalIntegrable (fun t : ℝ => 2 * burnolFractDensity (2 * t)) volume 0 R := by
      refine burnolIntervalIntegrable_of_bounded_nonneg
        ((measurable_burnolFractDensity.comp (measurable_const_mul 2)).const_mul 2)
        (M := 2) (fun x hx => ?_) le_rfl hR
      show |2 * burnolFractDensity (2 * x)| ≤ 2
      rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      have := abs_burnolFractDensity_le_one (x := 2 * x) (by linarith)
      linarith
    rw [← intervalIntegral.integral_sub (intervalIntegrable_burnolFractDensity le_rfl hR) hint2]
    refine intervalIntegral.integral_congr fun t _ => ?_
    by_cases ht : t = 0
    · rw [ht]
      simp [burnolRawSource, burnolFractDensity]
    · rw [burnolRawSource, burnolFractDensity, burnolFractDensity, burnolFractPair]
      field_simp
  have hscale : (∫ t in (0 : ℝ)..R, 2 * burnolFractDensity (2 * t)) =
      ∫ x in (0 : ℝ)..(2 * R), burnolFractDensity x := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left burnolFractDensity (by norm_num : (2:ℝ) ≠ 0),
      mul_zero, smul_eq_mul]
    ring
  have hadj : (∫ x in (0 : ℝ)..R, burnolFractDensity x) +
      (∫ x in R..(2 * R), burnolFractDensity x) = ∫ x in (0 : ℝ)..(2 * R), burnolFractDensity x :=
    intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_burnolFractDensity le_rfl hR)
      (intervalIntegrable_burnolFractDensity hR (by linarith))
  rw [hsub, hscale, ← hadj]
  ring

/-! ## The bounded periodic primitive of the centred sawtooth -/

/-- The centred sawtooth. -/
def burnolCenteredSawtooth (x : ℝ) : ℝ := Int.fract x - 1 / 2

theorem measurable_burnolCenteredSawtooth : Measurable burnolCenteredSawtooth :=
  measurable_fract.sub measurable_const

theorem abs_burnolCenteredSawtooth_le (x : ℝ) : |burnolCenteredSawtooth x| ≤ 1 / 2 := by
  rw [burnolCenteredSawtooth, abs_le]
  constructor <;> linarith [Int.fract_nonneg x, Int.fract_lt_one x]

theorem intervalIntegrable_burnolCenteredSawtooth (a b : ℝ) :
    IntervalIntegrable burnolCenteredSawtooth volume a b := by
  constructor <;>
  · refine MeasureTheory.Measure.integrableOn_of_bounded (M := 1 / 2) measure_Ioc_lt_top.ne
      measurable_burnolCenteredSawtooth.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact abs_burnolCenteredSawtooth_le x

theorem continuousWithinAt_burnolCenteredSawtooth_Ici (a : ℝ) :
    ContinuousWithinAt burnolCenteredSawtooth (Ici a) a := by
  have hkey : burnolCenteredSawtooth =ᶠ[𝓝[≥] a] fun y : ℝ => (y - (⌊a⌋ : ℝ)) - 1 / 2 := by
    filter_upwards [burnolEventually_floor_eq_Ici a] with y h1
    rw [burnolCenteredSawtooth, Int.fract, h1]
  have hcont : ContinuousWithinAt (fun y : ℝ => (y - (⌊a⌋ : ℝ)) - 1 / 2) (Ici a) a := by fun_prop
  refine hcont.congr_of_eventuallyEq hkey ?_
  rw [burnolCenteredSawtooth, Int.fract]

/-- The primitive of the centred sawtooth. -/
def burnolCenteredSawtoothPrimitive (x : ℝ) : ℝ := ∫ y in (0 : ℝ)..x, burnolCenteredSawtooth y

theorem continuous_burnolCenteredSawtoothPrimitive :
    Continuous burnolCenteredSawtoothPrimitive :=
  intervalIntegral.continuous_primitive intervalIntegrable_burnolCenteredSawtooth 0

theorem hasDerivWithinAt_burnolCenteredSawtoothPrimitive (a : ℝ) :
    HasDerivWithinAt burnolCenteredSawtoothPrimitive (burnolCenteredSawtooth a) (Ici a) a :=
  intervalIntegral.integral_hasDerivWithinAt_right (s := Ici a) (t := Ioi a)
    (intervalIntegrable_burnolCenteredSawtooth 0 a)
    ⟨Ioi a, self_mem_nhdsWithin,
      measurable_burnolCenteredSawtooth.aestronglyMeasurable.restrict⟩
    ((continuousWithinAt_burnolCenteredSawtooth_Ici a).mono Ioi_subset_Ici_self)

theorem burnolCenteredSawtooth_periodic : Function.Periodic burnolCenteredSawtooth 1 := by
  intro x
  rw [burnolCenteredSawtooth, burnolCenteredSawtooth, Int.fract_add_one]

theorem integral_burnolCenteredSawtooth_unit :
    (∫ y in (0 : ℝ)..1, burnolCenteredSawtooth y) = 0 := by
  have hsub : (∫ y in (0 : ℝ)..1, burnolCenteredSawtooth y) =
      (∫ y in (0 : ℝ)..1, Int.fract y) - ∫ y in (0 : ℝ)..(1 : ℝ), (1 / 2 : ℝ) := by
    have hint1 : IntervalIntegrable (fun x : ℝ => Int.fract x) volume 0 1 := by
      constructor <;>
      · refine MeasureTheory.Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne
          measurable_fract.aestronglyMeasurable ?_
        exact Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg x)]
          exact (Int.fract_lt_one x).le
    rw [← intervalIntegral.integral_sub hint1 intervalIntegrable_const]
    rfl
  rw [hsub, integral_fract_unit, intervalIntegral.integral_const]
  norm_num

theorem burnolCenteredSawtoothPrimitive_periodic :
    Function.Periodic burnolCenteredSawtoothPrimitive 1 := by
  intro t
  have hsplit : burnolCenteredSawtoothPrimitive t +
      (∫ y in t..(t + 1), burnolCenteredSawtooth y) = burnolCenteredSawtoothPrimitive (t + 1) :=
    intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_burnolCenteredSawtooth 0 t)
      (intervalIntegrable_burnolCenteredSawtooth t (t + 1))
  have hcell : (∫ y in t..(t + 1), burnolCenteredSawtooth y) = 0 := by
    have h := burnolCenteredSawtooth_periodic.intervalIntegral_add_eq t 0
    rw [zero_add] at h
    rw [h, integral_burnolCenteredSawtooth_unit]
  rw [← hsplit, hcell, add_zero]

theorem burnolCenteredSawtoothPrimitive_of_mem_Ico {s : ℝ} (h0 : 0 ≤ s) (h1 : s < 1) :
    burnolCenteredSawtoothPrimitive s = s ^ 2 / 2 - s / 2 := by
  have hne : ∀ᵐ y : ℝ ∂volume, y ≠ 1 := by
    rw [MeasureTheory.ae_iff]
    simp
  have hcongr : (∫ y in (0 : ℝ)..s, burnolCenteredSawtooth y) =
      ∫ y in (0 : ℝ)..s, (y - 1 / 2) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hne] with y hy1 hy
    rw [Set.uIoc_of_le h0] at hy
    rw [burnolCenteredSawtooth, Int.fract_eq_self.mpr ⟨hy.1.le, lt_of_le_of_lt hy.2 h1⟩]
  rw [burnolCenteredSawtoothPrimitive, hcongr,
    intervalIntegral.integral_sub (intervalIntegrable_id) intervalIntegrable_const,
    integral_id, intervalIntegral.integral_const]
  norm_num
  ring

/-- **The primitive is bounded by `1/8`.** -/
theorem abs_burnolCenteredSawtoothPrimitive_le (x : ℝ) :
    |burnolCenteredSawtoothPrimitive x| ≤ 1 / 8 := by
  have hred : burnolCenteredSawtoothPrimitive x =
      burnolCenteredSawtoothPrimitive (Int.fract x) := by
    have h := burnolCenteredSawtoothPrimitive_periodic.sub_int_mul_eq (x := x) ⌊x⌋
    rw [mul_one] at h
    rw [Int.fract, h]
  rw [hred, burnolCenteredSawtoothPrimitive_of_mem_Ico (Int.fract_nonneg x)
    (Int.fract_lt_one x)]
  set s := Int.fract x with hs
  have h0 : 0 ≤ s := Int.fract_nonneg x
  have h1 : s < 1 := Int.fract_lt_one x
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (s - 1 / 2), sq_nonneg s]


/-! ## The dyadic window limit -/

theorem intervalIntegrable_burnolCenteredSawtooth_div {R : ℝ} (hR : 0 < R) :
    IntervalIntegrable (fun x : ℝ => burnolCenteredSawtooth x / x) volume R (2 * R) := by
  constructor <;>
  · refine MeasureTheory.Measure.integrableOn_of_bounded (M := 1 / (2 * R))
      measure_Ioc_lt_top.ne
      (measurable_burnolCenteredSawtooth.div measurable_id).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hxR : R < x := by linarith [hx.1]
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (lt_trans hR hxR), div_le_div_iff₀
      (lt_trans hR hxR) (by linarith : (0:ℝ) < 2 * R)]
    have hs := abs_burnolCenteredSawtooth_le x
    nlinarith [hs, hR, hxR, abs_nonneg (burnolCenteredSawtooth x)]

/-- **The centred window remainder is `O(1/R)`.**  Integration by parts against the bounded
periodic primitive. -/
theorem abs_integral_burnolCenteredSawtooth_div_le {R : ℝ} (hR : 0 < R) :
    |∫ x in R..(2 * R), burnolCenteredSawtooth x / x| ≤ 1 / (2 * R) := by
  have hle : R ≤ 2 * R := by linarith
  have hquot : IntervalIntegrable
      (fun x : ℝ => burnolCenteredSawtoothPrimitive x / x ^ 2) volume R (2 * R) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hle]
    refine ContinuousOn.div continuous_burnolCenteredSawtoothPrimitive.continuousOn
      (continuous_pow 2).continuousOn ?_
    intro x hx
    have : 0 < x := lt_of_lt_of_le hR hx.1
    positivity
  have hderiv : ∀ x ∈ Ioo R (2 * R), HasDerivWithinAt
      (fun y : ℝ => burnolCenteredSawtoothPrimitive y / y)
      (burnolCenteredSawtooth x / x - burnolCenteredSawtoothPrimitive x / x ^ 2) (Ioi x) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_trans hR hx.1)
    have hQ := (hasDerivWithinAt_burnolCenteredSawtoothPrimitive x).mono
      (Ioi_subset_Ici_self (a := x))
    have hinv : HasDerivWithinAt (fun y : ℝ => y⁻¹) (-(x ^ 2)⁻¹) (Ioi x) x :=
      (hasDerivAt_inv hx0).hasDerivWithinAt
    have hmul := hQ.mul hinv
    refine hmul.congr_deriv ?_
    field_simp
    ring
  have hcont : ContinuousOn (fun y : ℝ => burnolCenteredSawtoothPrimitive y / y)
      (Icc R (2 * R)) := by
    refine ContinuousOn.div continuous_burnolCenteredSawtoothPrimitive.continuousOn
      continuousOn_id ?_
    intro x hx
    exact ne_of_gt (lt_of_lt_of_le hR hx.1)
  have hint : IntervalIntegrable
      (fun x : ℝ => burnolCenteredSawtooth x / x - burnolCenteredSawtoothPrimitive x / x ^ 2)
      volume R (2 * R) := (intervalIntegrable_burnolCenteredSawtooth_div hR).sub hquot
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hle hcont hderiv hint
  rw [intervalIntegral.integral_sub (intervalIntegrable_burnolCenteredSawtooth_div hR) hquot]
    at hftc
  have hb1 : |burnolCenteredSawtoothPrimitive (2 * R) / (2 * R)| ≤ 1 / (16 * R) := by
    rw [abs_div, abs_of_pos (by linarith : (0:ℝ) < 2 * R),
      div_le_div_iff₀ (by linarith : (0:ℝ) < 2 * R) (by linarith : (0:ℝ) < 16 * R)]
    nlinarith [abs_burnolCenteredSawtoothPrimitive_le (2 * R), hR]
  have hb2 : |burnolCenteredSawtoothPrimitive R / R| ≤ 1 / (8 * R) := by
    rw [abs_div, abs_of_pos hR, div_le_div_iff₀ hR (by linarith : (0:ℝ) < 8 * R)]
    nlinarith [abs_burnolCenteredSawtoothPrimitive_le R, hR]
  have hb3 : |∫ x in R..(2 * R), burnolCenteredSawtoothPrimitive x / x ^ 2| ≤ 1 / (8 * R) := by
    have hbound : ∀ x ∈ Set.uIoc R (2 * R),
        ‖burnolCenteredSawtoothPrimitive x / x ^ 2‖ ≤ 1 / (8 * R ^ 2) := by
      intro x hx
      rw [Set.uIoc_of_le hle] at hx
      have hxR : R < x := hx.1
      have hx0 : (0:ℝ) < x := lt_trans hR hxR
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hx0 2),
        div_le_div_iff₀ (pow_pos hx0 2)
          (mul_pos (by norm_num : (0:ℝ) < 8) (pow_pos hR 2))]
      nlinarith [abs_burnolCenteredSawtoothPrimitive_le x, hR, hxR, sq_nonneg (x - R)]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    rw [Real.norm_eq_abs, show |2 * R - R| = R by rw [show 2 * R - R = R by ring,
      abs_of_pos hR]] at h
    refine le_trans h (le_of_eq ?_)
    field_simp
  have hexpand : (∫ x in R..(2 * R), burnolCenteredSawtooth x / x) =
      burnolCenteredSawtoothPrimitive (2 * R) / (2 * R) - burnolCenteredSawtoothPrimitive R / R
        + ∫ x in R..(2 * R), burnolCenteredSawtoothPrimitive x / x ^ 2 := by
    linarith [hftc]
  rw [hexpand]
  have hsum : 1 / (16 * R) + 1 / (8 * R) + 1 / (8 * R) ≤ 1 / (2 * R) := by
    have hval : 1 / (16 * R) + 1 / (8 * R) + 1 / (8 * R) = 5 / (16 * R) := by
      field_simp
      ring
    rw [hval, div_le_div_iff₀ (by linarith) (by linarith)]
    linarith
  rw [abs_le] at hb1 hb2 hb3 ⊢
  constructor <;> linarith [hb1.1, hb1.2, hb2.1, hb2.2, hb3.1, hb3.2, hsum]

theorem integral_burnolFractDensity_window {R : ℝ} (hR : 0 < R) :
    (∫ x in R..(2 * R), burnolFractDensity x) =
      Real.log 2 / 2 + ∫ x in R..(2 * R), burnolCenteredSawtooth x / x := by
  have hle : R ≤ 2 * R := by linarith
  have hhalf : IntervalIntegrable (fun x : ℝ => (1 / 2 : ℝ) / x) volume R (2 * R) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hle]
    refine ContinuousOn.div continuousOn_const continuousOn_id ?_
    intro x hx
    exact ne_of_gt (lt_of_lt_of_le hR hx.1)
  have hsplit : (∫ x in R..(2 * R), burnolFractDensity x) =
      (∫ x in R..(2 * R), (1 / 2 : ℝ) / x) +
        ∫ x in R..(2 * R), burnolCenteredSawtooth x / x := by
    rw [← intervalIntegral.integral_add hhalf (intervalIntegrable_burnolCenteredSawtooth_div hR)]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le hle] at hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le hR hx.1)
    rw [burnolFractDensity, burnolCenteredSawtooth]
    field_simp
    ring
  have hlog : (∫ x in R..(2 * R), (1 / 2 : ℝ) / x) = Real.log 2 / 2 := by
    have hnot : (0 : ℝ) ∉ Set.uIcc R (2 * R) := by
      rw [Set.uIcc_of_le hle]
      intro hc
      exact absurd hc.1 (not_le.mpr hR)
    rw [show (fun x : ℝ => (1 / 2 : ℝ) / x) = fun x : ℝ => (1 / 2 : ℝ) * (1 / x) by
      funext x; ring, intervalIntegral.integral_const_mul, integral_one_div hnot,
      show 2 * R / R = 2 by field_simp]
    ring
  rw [hsplit, hlog]

/-- **The improper mass of the raw source.**  Truncated at `R`, it converges to `-(log 2)/2`. -/
theorem tendsto_integral_burnolRawSource :
    Tendsto (fun R : ℝ => ∫ t in (0 : ℝ)..R, burnolRawSource t) atTop
      (𝓝 (-(Real.log 2) / 2)) := by
  have hrep : ∀ᶠ R : ℝ in atTop, (∫ t in (0 : ℝ)..R, burnolRawSource t) =
      -(Real.log 2) / 2 - ∫ x in R..(2 * R), burnolCenteredSawtooth x / x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    rw [integral_burnolRawSource_eq_neg_window hR.le, integral_burnolFractDensity_window hR]
    ring
  have herr : Tendsto (fun R : ℝ => ∫ x in R..(2 * R), burnolCenteredSawtooth x / x) atTop
      (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    have hdom : Tendsto (fun R : ℝ => 1 / (2 * R)) atTop (𝓝 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds
        (Filter.Tendsto.const_mul_atTop (by norm_num : (0:ℝ) < 2) tendsto_id)
    refine squeeze_zero' ?_ ?_ hdom
    · filter_upwards with R using abs_nonneg _
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
      exact abs_integral_burnolCenteredSawtooth_div_le hR
  have hmain : Tendsto (fun R : ℝ =>
      -(Real.log 2) / 2 - ∫ x in R..(2 * R), burnolCenteredSawtooth x / x) atTop
      (𝓝 (-(Real.log 2) / 2 - 0)) := tendsto_const_nhds.sub herr
  rw [sub_zero] at hmain
  exact hmain.congr' (hrep.mono fun R h => h.symm)

end RHTower
