import GaloisForLFunctions.RHTower.HedenmalmSourceMoments
import GaloisForLFunctions.RHTower.HedenmalmThetaKernelEnergy

/-!
# The slice moment of the quantile speed

The pinned kernel slice paired against the quantile speed reproduces the quantile itself:

```text
∫₀¹ q(t) (1_{s ≤ t} - t) dt = -Q(s).
```

Both sides move by `-(Q s - Q s')` between two parameters, because the difference of two slices is
the indicator of the interval between them and `Q' = q`; the additive constant is fixed by
integrating in `s`, where the slice averages to zero and the first quantile moment vanishes.

Integrability is the only delicate point: `q` itself is not integrable on the unit interval.  The
slice however satisfies `|1_{s ≤ t} - t| ≤ t(1-t) / min s (1-s)`, and `q(t) t(1-t)` is dominated by
half the sum of the finite kernel energy `q(t)² t(1-t)` and `t(1-t)`.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmThetaSource

open HedenmalmQuantile HedenmalmHilbertSchmidt

/-- **The slice is dominated by the interval weight.**  Away from the endpoints the pinned kernel
slice is bounded by `t(1-t)` divided by the distance of `s` from the boundary. -/
theorem abs_pinnedKernelSlice_le_weight {s t : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    |pinnedKernelSlice t s| ≤ t * (1 - t) / min s (1 - s) := by
  obtain ⟨hs0, hs1⟩ := hs
  obtain ⟨ht0, ht1⟩ := ht
  have hm : 0 < min s (1 - s) := lt_min hs0 (by linarith)
  rw [le_div_iff₀ hm, pinnedKernelSlice]
  by_cases h : s ≤ t
  · rw [if_pos h]
    have habs : |(1 : ℝ) - t| = 1 - t := abs_of_nonneg (by linarith)
    rw [habs]
    have hmin : min s (1 - s) ≤ s := min_le_left _ _
    nlinarith [hmin, hm]
  · have h' := not_le.mp h
    rw [if_neg h, zero_sub, abs_neg, abs_of_nonneg ht0.le]
    have hmin : min s (1 - s) ≤ 1 - s := min_le_right _ _
    nlinarith [hmin, hm]

/-- The dominating function of the slice moment. -/
def sliceDominant (S : PositiveDensitySource) (s t : ℝ) : ℝ :=
  (quantileSpeed S t ^ 2 * (t * (1 - t)) + t * (1 - t)) / (2 * min s (1 - s))

theorem integrable_sliceDominant (S : PositiveDensitySource) (hfin : HasFiniteKernelEnergy S)
    (s : ℝ) : Integrable (sliceDominant S s) unitIntervalMeasure := by
  have hpoly : Integrable (fun t : ℝ => t * (1 - t)) unitIntervalMeasure := by
    refine Integrable.mono' (integrable_const 1) ?_ ?_
    · exact ((continuous_id.mul (continuous_const.sub continuous_id)).aestronglyMeasurable)
    · filter_upwards [ae_unitIntervalMeasure_mem_Ioo] with t ht
      obtain ⟨ht0, ht1⟩ := ht
      rw [Real.norm_eq_abs, abs_of_nonneg (by nlinarith)]
      nlinarith
  exact ((hfin.add hpoly).div_const _)

/-- **The slice moment integrand is integrable.** -/
theorem integrable_quantileSpeed_mul_pinnedKernelSlice (S : PositiveDensitySource)
    (hfin : HasFiniteKernelEnergy S) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    Integrable (fun t => quantileSpeed S t * pinnedKernelSlice t s) unitIntervalMeasure := by
  refine Integrable.mono' (integrable_sliceDominant S hfin s) ?_ ?_
  · have hmq : Measurable (quantileSpeed S) :=
      measurable_const.div (S.continuous_k.measurable.comp S.measurable_quantileFun)
    have h1 : Measurable (fun t : ℝ => (Set.Ici s).indicator (fun _ => (1 : ℝ)) t) :=
      measurable_const.indicator measurableSet_Ici
    have h2 : (fun t : ℝ => (Set.Ici s).indicator (fun _ => (1 : ℝ)) t)
        = fun t : ℝ => (if s ≤ t then (1 : ℝ) else 0) := by
      funext t; simp [Set.indicator_apply]
    rw [h2] at h1
    exact hmq.aestronglyMeasurable.mul (h1.sub measurable_id).aestronglyMeasurable
  · filter_upwards [ae_unitIntervalMeasure_mem_Ioo] with t ht
    have hm : 0 < min s (1 - s) := lt_min hs.1 (by linarith [hs.2])
    have hq : 0 < quantileSpeed S t := quantileSpeed_pos S t
    have hw : 0 ≤ t * (1 - t) := by nlinarith [ht.1, ht.2]
    have hslice := abs_pinnedKernelSlice_le_weight hs ht
    have hAM : quantileSpeed S t * (t * (1 - t))
        ≤ (quantileSpeed S t ^ 2 * (t * (1 - t)) + t * (1 - t)) / 2 := by
      nlinarith [sq_nonneg (quantileSpeed S t - 1), hw]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hq, sliceDominant]
    calc quantileSpeed S t * |pinnedKernelSlice t s|
        ≤ quantileSpeed S t * (t * (1 - t) / min s (1 - s)) := by
          exact mul_le_mul_of_nonneg_left hslice hq.le
      _ = (quantileSpeed S t * (t * (1 - t))) / min s (1 - s) := by ring
      _ ≤ ((quantileSpeed S t ^ 2 * (t * (1 - t)) + t * (1 - t)) / 2) / min s (1 - s) := by
          gcongr
      _ = (quantileSpeed S t ^ 2 * (t * (1 - t)) + t * (1 - t)) / (2 * min s (1 - s)) := by
          ring

/-- The slice moment of the quantile speed. -/
def sliceMoment (S : PositiveDensitySource) (s : ℝ) : ℝ :=
  ∫ t, quantileSpeed S t * pinnedKernelSlice t s ∂unitIntervalMeasure


/-- **The slice moment moves exactly like the quantile.**  Between two interior parameters the
difference of the two slice moments is minus the increment of the quantile, because the difference
of the two slices is the indicator of the interval between them. -/
theorem sliceMoment_sub_of_le (S : PositiveDensitySource) (hfin : HasFiniteKernelEnergy S)
    {s' s : ℝ} (hs' : s' ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Ioo (0 : ℝ) 1) (hle : s' ≤ s) :
    sliceMoment S s - sliceMoment S s' = -(S.quantileFun s - S.quantileFun s') := by
  have hsub : Icc s' s ⊆ Ioo (0 : ℝ) 1 := fun x hx =>
    ⟨lt_of_lt_of_le hs'.1 hx.1, lt_of_le_of_lt hx.2 hs.2⟩
  have hpt : ∀ t : ℝ, quantileSpeed S t * pinnedKernelSlice t s
      - quantileSpeed S t * pinnedKernelSlice t s'
      = -((Ico s' s).indicator (quantileSpeed S) t) := by
    intro t
    rw [pinnedKernelSlice, pinnedKernelSlice, Set.indicator_apply]
    by_cases h1 : s ≤ t
    · have h2 : s' ≤ t := hle.trans h1
      have h3 : t ∉ Ico s' s := fun hx => absurd h1 (not_le.mpr hx.2)
      rw [if_pos h1, if_pos h2, if_neg h3]
      ring
    · have h1' := not_le.mp h1
      by_cases h2 : s' ≤ t
      · have h3 : t ∈ Ico s' s := ⟨h2, h1'⟩
        rw [if_neg h1, if_pos h2, if_pos h3]
        ring
      · have h3 : t ∉ Ico s' s := fun hx => h2 hx.1
        rw [if_neg h1, if_neg h2, if_neg h3]
        ring
  have hint := integrable_quantileSpeed_mul_pinnedKernelSlice S hfin hs
  have hint' := integrable_quantileSpeed_mul_pinnedKernelSlice S hfin hs'
  rw [sliceMoment, sliceMoment, ← integral_sub hint hint',
    integral_congr_ae (Filter.Eventually.of_forall hpt), MeasureTheory.integral_neg]
  have hIco : (Ico s' s : Set ℝ) ⊆ Icc 0 1 := fun x hx =>
    ⟨(hs'.1.le).trans hx.1, (hx.2.le).trans hs.2.le⟩
  have hrestrict : ∫ t, (Ico s' s).indicator (quantileSpeed S) t ∂unitIntervalMeasure
      = ∫ t in Ico s' s, quantileSpeed S t := by
    rw [unitIntervalMeasure, integral_indicator measurableSet_Ico,
      Measure.restrict_restrict measurableSet_Ico, Set.inter_eq_left.mpr hIco]
  rw [hrestrict]
  have hcont : ContinuousOn (quantileSpeed S) (Set.uIcc s' s) := by
    rw [Set.uIcc_of_le hle]
    exact (HedenmalmQuantile.continuousOn_quantileSpeed S).mono hsub
  have hderiv : ∀ x ∈ Set.uIcc s' s, HasDerivAt S.quantileFun (quantileSpeed S x) x := by
    intro x hx
    rw [Set.uIcc_of_le hle] at hx
    exact hasDerivAt_quantileFun S (hsub hx)
  have hftc : ∫ t in s'..s, quantileSpeed S t = S.quantileFun s - S.quantileFun s' :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  have hIoc : ∫ t in Ico s' s, quantileSpeed S t = ∫ t in s'..s, quantileSpeed S t := by
    rw [intervalIntegral.integral_of_le hle]
    exact setIntegral_congr_set (Ico_ae_eq_Icc.trans Ioc_ae_eq_Icc.symm)
  rw [hIoc, hftc]



/-- **The slice moment is the quantile up to one additive constant.**  This is the calibration
identity of the trace invariant: `s ↦ sliceMoment S s + Q s` is constant on the open interval. -/
theorem sliceMoment_add_quantileFun_eq (S : PositiveDensitySource)
    (hfin : HasFiniteKernelEnergy S) {s' s : ℝ} (hs' : s' ∈ Ioo (0 : ℝ) 1)
    (hs : s ∈ Ioo (0 : ℝ) 1) :
    sliceMoment S s + S.quantileFun s = sliceMoment S s' + S.quantileFun s' := by
  rcases le_total s' s with h | h
  · have := sliceMoment_sub_of_le S hfin hs' hs h
    linarith
  · have := sliceMoment_sub_of_le S hfin hs hs' h
    linarith



/-! ### Reflection at the even theta source pins the constant -/

theorem sliceMoment_eq_intervalIntegral (S : PositiveDensitySource) (s : ℝ) :
    sliceMoment S s = ∫ t in (0 : ℝ)..1, quantileSpeed S t * pinnedKernelSlice t s := by
  rw [sliceMoment, unitIntervalMeasure,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact setIntegral_congr_set Ioc_ae_eq_Icc.symm

/-- **The quantile of the even theta source is odd.** -/
theorem quantileFun_one_sub {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    thetaSource.quantileFun (1 - s) = -thetaSource.quantileFun s := by
  have h1 : thetaSource.cdfFun (thetaSource.quantileFun s) = s :=
    thetaSource.cdfFun_quantile hs
  have h2 : thetaSource.cdfFun (-thetaSource.quantileFun s) = 1 - s := by
    rw [HedenmalmIntervalAnomaly.cdfFun_neg thetaSource thetaSource_even, h1]
  calc thetaSource.quantileFun (1 - s)
      = thetaSource.quantileFun
          (thetaSource.cdfFun (-thetaSource.quantileFun s)) := by rw [h2]
    _ = -thetaSource.quantileFun s := thetaSource.quantile_cdfFun _

/-- **The quantile speed of the even theta source is symmetric.** -/
theorem quantileSpeed_one_sub {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    quantileSpeed thetaSource (1 - t) = quantileSpeed thetaSource t := by
  rw [quantileSpeed, quantileSpeed, quantileFun_one_sub ht, thetaSource_even]

/-- **The slice moment of the even theta source is odd under reflection.** -/
theorem sliceMoment_one_sub (s : ℝ) :
    sliceMoment thetaSource (1 - s) = -sliceMoment thetaSource s := by
  rw [sliceMoment_eq_intervalIntegral, sliceMoment_eq_intervalIntegral,
    ← intervalIntegral.integral_neg]
  have hrefl : (∫ t in (0 : ℝ)..1,
        quantileSpeed thetaSource t * pinnedKernelSlice t (1 - s))
      = ∫ t in (0 : ℝ)..1,
        quantileSpeed thetaSource (1 - t) * pinnedKernelSlice (1 - t) (1 - s) := by
    have h := intervalIntegral.integral_comp_sub_left
      (fun t => quantileSpeed thetaSource t * pinnedKernelSlice t (1 - s)) (1 : ℝ)
      (a := (0 : ℝ)) (b := (1 : ℝ))
    norm_num at h
    exact h.symm
  rw [hrefl]
  refine intervalIntegral.integral_congr_ae ?_
  have hns : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ s :=
    ae_iff.mpr (by simp)
  have hn1 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 1 :=
    ae_iff.mpr (by simp)
  filter_upwards [hns, hn1] with t hts ht1 ht
  rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
  have ht' : t ∈ Ioo (0 : ℝ) 1 := ⟨ht.1, lt_of_le_of_ne ht.2 ht1⟩
  rw [quantileSpeed_one_sub ht']
  simp only [pinnedKernelSlice]
  have hiff : (1 - s ≤ 1 - t) ↔ (t ≤ s) := by constructor <;> intro h <;> linarith
  by_cases h1 : t ≤ s
  · have h2 : ¬ s ≤ t := by
      rcases lt_or_eq_of_le h1 with h | h
      · exact not_le.mpr h
      · exact absurd h hts
    rw [if_pos (hiff.mpr h1), if_neg h2]
    ring
  · have h2 : s ≤ t := not_le.mp h1 |>.le
    rw [if_neg (fun hc => h1 (hiff.mp hc)), if_pos h2]
    ring

/-- **The slice moment is minus the quantile.**  The additive constant is pinned by the reflection
symmetry of the even theta source. -/
theorem sliceMoment_eq_neg_quantileFun {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    sliceMoment thetaSource s = -thetaSource.quantileFun s := by
  have hs' : 1 - s ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hconst := sliceMoment_add_quantileFun_eq thetaSource hasFiniteKernelEnergy_thetaSource
    hs' hs
  rw [sliceMoment_one_sub s, quantileFun_one_sub hs] at hconst
  linarith



/-- **The trace calibration in quantile form.**  The mean square of the slice moment is the source
variance, which is the value the trace invariant of the compressed inverse must take. -/
theorem integral_sq_sliceMoment :
    (∫ s in Ioo (0 : ℝ) 1, sliceMoment thetaSource s ^ 2)
      = thetaSource.mass⁻¹ * ∫ x : ℝ, x ^ 2 * thetaCuspFullSource x := by
  rw [← integral_sq_quantileFun]
  refine setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
  rw [sliceMoment_eq_neg_quantileFun hs]
  ring



/-- **The quantile speed integrates to the quantile increment.**  This is the fundamental theorem of
calculus on the unit interval, written with an indicator so that no endpoint behaviour intervenes. -/
theorem integral_quantileSpeed_indicator_Ico (S : PositiveDensitySource) {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) (hab : a ≤ b) :
    (∫ t, (Ico a b).indicator (quantileSpeed S) t ∂unitIntervalMeasure)
      = S.quantileFun b - S.quantileFun a := by
  have hsub : Icc a b ⊆ Ioo (0 : ℝ) 1 := fun x hx =>
    ⟨lt_of_lt_of_le ha.1 hx.1, lt_of_le_of_lt hx.2 hb.2⟩
  have hIco : (Ico a b : Set ℝ) ⊆ Icc 0 1 := fun x hx =>
    ⟨(ha.1.le).trans hx.1, (hx.2.le).trans hb.2.le⟩
  have hrestrict : ∫ t, (Ico a b).indicator (quantileSpeed S) t ∂unitIntervalMeasure
      = ∫ t in Ico a b, quantileSpeed S t := by
    rw [unitIntervalMeasure, integral_indicator measurableSet_Ico,
      Measure.restrict_restrict measurableSet_Ico, Set.inter_eq_left.mpr hIco]
  rw [hrestrict]
  have hcont : ContinuousOn (quantileSpeed S) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    exact (HedenmalmQuantile.continuousOn_quantileSpeed S).mono hsub
  have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt S.quantileFun (quantileSpeed S x) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact hasDerivAt_quantileFun S (hsub hx)
  have hftc : ∫ t in a..b, quantileSpeed S t = S.quantileFun b - S.quantileFun a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  rw [show ∫ t in Ico a b, quantileSpeed S t = ∫ t in a..b, quantileSpeed S t from by
    rw [intervalIntegral.integral_of_le hab]
    exact setIntegral_congr_set (Ico_ae_eq_Icc.trans Ioc_ae_eq_Icc.symm), hftc]

/-- **The quantile map is integrable on the unit interval.**  Its transport is the first absolute
moment of the source. -/
theorem integrableOn_quantileFun_thetaSource :
    IntegrableOn thetaSource.quantileFun (Ioo (0 : ℝ) 1) volume := by
  rw [thetaSource.integrableOn_comp_quantileFun_iff
    (g := fun x : ℝ => x) continuous_id.aestronglyMeasurable]
  refine (integrable_mul_thetaSource.const_mul thetaSource.mass⁻¹).congr ?_
  filter_upwards with x
  show thetaSource.mass⁻¹ * (x * thetaCuspFullSource x) = thetaSource.normalized x • x
  show thetaSource.mass⁻¹ * (x * thetaCuspFullSource x) = thetaSource.k x / thetaSource.mass * x
  show thetaSource.mass⁻¹ * (x * thetaCuspFullSource x)
    = thetaCuspFullSource x / thetaSource.mass * x
  field_simp



/-- **The second absolute moment of the theta source is finite.**  The source is Schwartz, so every
polynomial weight is integrable against it. -/
theorem integrable_sq_mul_thetaSource :
    Integrable (fun x : ℝ => x ^ 2 * thetaCuspFullSource x) (volume : Measure ℝ) := by
  have hraw := thetaCuspSchwartzReal.integrable_pow_mul (volume : Measure ℝ) 2
  refine hraw.mono' ?_ ?_
  · exact ((continuous_pow 2).mul
      contDiff_thetaCuspFullSource.continuous).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    simp [thetaCuspSchwartzReal_apply, Real.norm_eq_abs]

/-- **The quantile map is square integrable on the unit interval.**  Its transport is the second
moment of the source. -/
theorem integrableOn_sq_quantileFun_thetaSource :
    IntegrableOn (fun t => thetaSource.quantileFun t ^ 2) (Ioo (0 : ℝ) 1) volume := by
  rw [thetaSource.integrableOn_comp_quantileFun_iff
    (g := fun x : ℝ => x ^ 2) (continuous_pow 2).aestronglyMeasurable]
  refine (integrable_sq_mul_thetaSource.const_mul thetaSource.mass⁻¹).congr ?_
  filter_upwards with x
  show thetaSource.mass⁻¹ * (x ^ 2 * thetaCuspFullSource x) = thetaSource.normalized x • x ^ 2
  show thetaSource.mass⁻¹ * (x ^ 2 * thetaCuspFullSource x)
    = thetaSource.k x / thetaSource.mass * x ^ 2
  show thetaSource.mass⁻¹ * (x ^ 2 * thetaCuspFullSource x)
    = thetaCuspFullSource x / thetaSource.mass * x ^ 2
  field_simp



/-- **The quantile map is monotone**, because the quantile speed is positive and integrates to its
increments. -/
theorem quantileFun_le_quantileFun (S : PositiveDensitySource) {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) (hab : a ≤ b) :
    S.quantileFun a ≤ S.quantileFun b := by
  have h := integral_quantileSpeed_indicator_Ico S ha hb hab
  have hnn : 0 ≤ ∫ t, (Ico a b).indicator (quantileSpeed S) t ∂unitIntervalMeasure :=
    integral_nonneg fun t => Set.indicator_nonneg (fun x _ => (quantileSpeed_pos S x).le) t
  rw [h] at hnn
  linarith

/-- **The slice increment is an interval indicator.**  Two pinned slices at the same row differ by
the indicator of the interval between their two parameters. -/
theorem abs_pinnedKernelSlice_sub (t s c : ℝ) :
    |pinnedKernelSlice t s - pinnedKernelSlice t c|
      = (Ico (min s c) (max s c)).indicator (fun _ => (1 : ℝ)) t := by
  rw [pinnedKernelSlice, pinnedKernelSlice, Set.indicator_apply]
  rcases le_total c s with h | h
  · rw [min_eq_right h, max_eq_left h]
    by_cases h1 : s ≤ t
    · have h2 : c ≤ t := h.trans h1
      have h3 : t ∉ Ico c s := fun hx => absurd h1 (not_le.mpr hx.2)
      rw [if_pos h1, if_pos h2, if_neg h3]
      norm_num
    · have h1' := not_le.mp h1
      by_cases h2 : c ≤ t
      · rw [if_neg h1, if_pos h2, if_pos ⟨h2, h1'⟩, abs_of_nonpos (by linarith)]
        ring
      · rw [if_neg h1, if_neg h2, if_neg (fun hx => h2 hx.1)]
        norm_num
  · rw [min_eq_left h, max_eq_right h]
    by_cases h1 : c ≤ t
    · have h2 : s ≤ t := h.trans h1
      have h3 : t ∉ Ico s c := fun hx => absurd h1 (not_le.mpr hx.2)
      rw [if_pos h2, if_pos h1, if_neg h3]
      norm_num
    · have h1' := not_le.mp h1
      by_cases h2 : s ≤ t
      · rw [if_pos h2, if_neg h1, if_pos ⟨h2, h1'⟩, abs_of_nonneg (by linarith)]
        ring
      · rw [if_neg h2, if_neg h1, if_neg (fun hx => h2 hx.1)]
        norm_num



/-- The absolute slice moment, the majorant of the slice moment. -/
def absSliceMoment (S : PositiveDensitySource) (s : ℝ) : ℝ :=
  ∫ t, quantileSpeed S t * |pinnedKernelSlice t s| ∂unitIntervalMeasure

theorem integrable_quantileSpeed_mul_abs_pinnedKernelSlice (S : PositiveDensitySource)
    (hfin : HasFiniteKernelEnergy S) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    Integrable (fun t => quantileSpeed S t * |pinnedKernelSlice t s|) unitIntervalMeasure := by
  refine (integrable_quantileSpeed_mul_pinnedKernelSlice S hfin hs).abs.congr ?_
  filter_upwards with t
  rw [abs_mul, abs_of_pos (quantileSpeed_pos S t)]

theorem integrableOn_quantileSpeed_Ico (S : PositiveDensitySource) {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) :
    Integrable ((Ico a b).indicator (quantileSpeed S)) unitIntervalMeasure := by
  have hsub : Icc a b ⊆ Ioo (0 : ℝ) 1 := fun x hx =>
    ⟨lt_of_lt_of_le ha.1 hx.1, lt_of_le_of_lt hx.2 hb.2⟩
  have hIco : (Ico a b : Set ℝ) ⊆ Icc 0 1 := fun x hx =>
    ⟨(ha.1.le).trans hx.1, (hx.2.le).trans hb.2.le⟩
  rw [integrable_indicator_iff measurableSet_Ico, IntegrableOn, unitIntervalMeasure,
    Measure.restrict_restrict measurableSet_Ico, Set.inter_eq_left.mpr hIco]
  exact (((HedenmalmQuantile.continuousOn_quantileSpeed S).mono hsub).integrableOn_compact
    isCompact_Icc).mono_set Set.Ico_subset_Icc_self

/-- **The absolute slice moment moves at most by the quantile increment.**  This is the majorant
that makes the slice-moment pairing product integrable. -/
theorem absSliceMoment_le (S : PositiveDensitySource) (hfin : HasFiniteKernelEnergy S)
    {s c : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (hc : c ∈ Ioo (0 : ℝ) 1) :
    absSliceMoment S s ≤ absSliceMoment S c + |S.quantileFun s - S.quantileFun c| := by
  have hmin : min s c ∈ Ioo (0 : ℝ) 1 := ⟨lt_min hs.1 hc.1, lt_of_le_of_lt (min_le_left _ _) hs.2⟩
  have hmax : max s c ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_lt_of_le hs.1 (le_max_left _ _),
    max_lt hs.2 hc.2⟩
  have hle : min s c ≤ max s c := min_le_max
  have hind := integrableOn_quantileSpeed_Ico S hmin hmax
  have hcabs := integrable_quantileSpeed_mul_abs_pinnedKernelSlice S hfin hc
  have hptwise : ∀ t : ℝ, quantileSpeed S t * |pinnedKernelSlice t s|
      ≤ (Ico (min s c) (max s c)).indicator (quantileSpeed S) t
        + quantileSpeed S t * |pinnedKernelSlice t c| := by
    intro t
    have htri : |pinnedKernelSlice t s|
        ≤ (Ico (min s c) (max s c)).indicator (fun _ => (1 : ℝ)) t
          + |pinnedKernelSlice t c| := by
      rw [← abs_pinnedKernelSlice_sub t s c]
      calc |pinnedKernelSlice t s|
          = |(pinnedKernelSlice t s - pinnedKernelSlice t c) + pinnedKernelSlice t c| := by
            ring_nf
        _ ≤ |pinnedKernelSlice t s - pinnedKernelSlice t c| + |pinnedKernelSlice t c| :=
            abs_add_le _ _
    have hq : 0 < quantileSpeed S t := quantileSpeed_pos S t
    have hexp : (Ico (min s c) (max s c)).indicator (quantileSpeed S) t
        = quantileSpeed S t * (Ico (min s c) (max s c)).indicator (fun _ => (1 : ℝ)) t := by
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases h : t ∈ Ico (min s c) (max s c) <;> simp [h]
    rw [hexp, ← mul_add]
    exact mul_le_mul_of_nonneg_left htri hq.le
  have hmono := integral_mono
    (integrable_quantileSpeed_mul_abs_pinnedKernelSlice S hfin hs) (hind.add hcabs) hptwise
  simp only [Pi.add_apply] at hmono
  rw [MeasureTheory.integral_add hind hcabs,
    integral_quantileSpeed_indicator_Ico S hmin hmax hle] at hmono
  have hdiff : S.quantileFun (max s c) - S.quantileFun (min s c)
      = |S.quantileFun s - S.quantileFun c| := by
    rcases le_total c s with h | h
    · rw [min_eq_right h, max_eq_left h,
        abs_of_nonneg (by linarith [quantileFun_le_quantileFun S hc hs h])]
    · rw [min_eq_left h, max_eq_right h,
        abs_of_nonpos (by linarith [quantileFun_le_quantileFun S hs hc h])]
      ring
  rw [hdiff] at hmono
  rw [absSliceMoment, absSliceMoment]
  linarith


end HedenmalmThetaSource

end

end RHTower
