import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmTransposeKernelField
import GaloisForLFunctions.RHTower.KernelOperatorPolarization

/-!
# The trace invariant as a double kernel integral

With the adjoint of the source inverse identified as the transposed kernel operator, the trace
invariant `tr(B²) = ⟨B†, B⟩_HS` is the polarized kernel pairing of the two fields.  Reading the
Riesz vectors of the two fields gives the double integral

```text
tr(B²) = ∬ q(t) q(u) (min(t,u) - t u) dt du,
```

which is the quantile form of `2 ∫_{x<y} p(x)(1-p(y)) dx dy`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmThetaSource

open HedenmalmQuantile HedenmalmHilbertSchmidt ContinuousLinearMap

local instance factTwoNeTopThetaTraceKernel : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

theorem toDual_symm_innerSL {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (v : E) :
    (InnerProductSpace.toDual ℂ E).symm (innerSL ℂ v) = v := by
  have h : InnerProductSpace.toDual ℂ E v = innerSL ℂ v := by
    ext y
    rfl
  rw [← h, LinearIsometryEquiv.symm_apply_apply]

/-- The Riesz vector of the pinned kernel field. -/
theorem toDual_symm_pinnedKernelField (S : PositiveDensitySource) (t : ℝ) :
    (InnerProductSpace.toDual ℂ (Lp ℂ 2 unitIntervalMeasure)).symm (pinnedKernelField S t)
      = (-(Complex.I * ((quantileSpeed S t : ℝ) : ℂ))) • pinnedSliceVec t :=
  toDual_symm_innerSL _

/-- The Riesz vector of the transposed kernel field. -/
theorem toDual_symm_transposeKernelField (S : PositiveDensitySource)
    (hfin : HasFiniteKernelEnergy S) (t : ℝ) :
    (InnerProductSpace.toDual ℂ (Lp ℂ 2 unitIntervalMeasure)).symm
        (transposeKernelField S hfin t)
      = -(transposeVec S hfin t) :=
  toDual_symm_innerSL _

/-- **The pointwise kernel pairing.**  At an interior parameter the pairing of the two Riesz
vectors is the inner slice integral. -/
theorem inner_riesz_eq (S : PositiveDensitySource) (hfin : HasFiniteKernelEnergy S)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (inner ℂ ((-(Complex.I * ((quantileSpeed S t : ℝ) : ℂ))) • pinnedSliceVec t)
        (-(transposeVec S hfin t)) : ℂ)
      = ∫ u, ((-(quantileSpeed S t * quantileSpeed S u
          * (pinnedKernelSlice t u * pinnedKernelSlice u t)) : ℝ) : ℂ) ∂unitIntervalMeasure := by
  have hcongr : (fun u => (inner ℂ ((pinnedSliceVec t : ℝ → ℂ) u)
        ((transposeVec S hfin t : ℝ → ℂ) u) : ℂ))
      =ᵐ[unitIntervalMeasure]
      fun u => ((pinnedKernelSlice t u : ℝ) : ℂ) * transposeKernelFun S t u := by
    filter_upwards [pinnedSliceVec_coeFn t, transposeVec_coeFn S hfin ht] with u h1 h2
    rw [h1, h2, RCLike.inner_apply', Complex.conj_ofReal]
  have hL : (inner ℂ ((-(Complex.I * ((quantileSpeed S t : ℝ) : ℂ))) • pinnedSliceVec t)
        (-(transposeVec S hfin t)) : ℂ)
      = -((starRingEnd ℂ) (-(Complex.I * ((quantileSpeed S t : ℝ) : ℂ)))
        * ∫ u, ((pinnedKernelSlice t u : ℝ) : ℂ) * transposeKernelFun S t u
          ∂unitIntervalMeasure) := by
    rw [inner_neg_right, inner_smul_left, MeasureTheory.L2.inner_def,
      integral_congr_ae hcongr]
  rw [hL, ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [transposeKernelFun, map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **The trace invariant as a double kernel integral.**  This is the quantile form of
`tr(B²) = 2 ∫_{x<y} p(x)(1-p(y)) dx dy`. -/
theorem thetaTraceSq_eq_double_integral :
    thetaTraceSq
      = ∫ t, (∫ u, ((quantileSpeed thetaSource t * quantileSpeed thetaSource u
          * (min t u - t * u) : ℝ) : ℂ) ∂unitIntervalMeasure) ∂unitIntervalMeasure := by
  have hadj := adjoint_kernelOperator_eq thetaSource hasFiniteKernelEnergy_thetaSource
  rw [thetaTraceSq_eq_hsInner, thetaKernelOperator, hadj,
    hsInner_kernelOperator (E := Lp ℂ 2 unitIntervalMeasure) unitIntervalMeasure
      (transposeKernelL2 thetaSource hasFiniteKernelEnergy_thetaSource)
      (pinnedKernelL2 thetaSource hasFiniteKernelEnergy_thetaSource)]
  refine integral_congr_ae ?_
  filter_upwards [pinnedKernelL2_coeFn thetaSource hasFiniteKernelEnergy_thetaSource,
    transposeKernelL2_coeFn thetaSource hasFiniteKernelEnergy_thetaSource,
    ae_unitIntervalMeasure_mem_Ioo] with t h1 h2 ht
  rw [h1, h2, toDual_symm_pinnedKernelField, toDual_symm_transposeKernelField,
    inner_riesz_eq thetaSource hasFiniteKernelEnergy_thetaSource ht]
  refine integral_congr_ae ?_
  have hnull : ∀ᵐ u ∂unitIntervalMeasure, u ≠ t := by
    have : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ t := ae_iff.mpr (by simp)
    exact ae_restrict_of_ae this
  filter_upwards [hnull] with u hu
  · have htu : t ≠ u := fun h => hu h.symm
    rw [show -(quantileSpeed thetaSource t * quantileSpeed thetaSource u
        * (pinnedKernelSlice t u * pinnedKernelSlice u t))
        = quantileSpeed thetaSource t * quantileSpeed thetaSource u
          * (-(pinnedKernelSlice t u * pinnedKernelSlice u t)) by ring,
      neg_mul_pinnedKernelSlice htu]


/-! ### The first interchange -/

theorem measurable_uncurry_abs_slice (S : PositiveDensitySource) :
    Measurable (fun p : ℝ × ℝ => quantileSpeed S p.1 * |pinnedKernelSlice p.1 p.2|) := by
  have hmq : Measurable (quantileSpeed S) :=
    measurable_const.div (S.continuous_k.measurable.comp S.measurable_quantileFun)
  have hset : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1} :=
    measurableSet_le measurable_snd measurable_fst
  have hite : Measurable (fun p : ℝ × ℝ => if p.2 ≤ p.1 then (1 : ℝ) else 0) :=
    Measurable.ite hset measurable_const measurable_const
  exact (hmq.comp measurable_fst).mul ((hite.sub measurable_fst).abs)

theorem integrable_poly_unitInterval :
    Integrable (fun t : ℝ => t * (1 - t)) unitIntervalMeasure := by
  refine Integrable.mono' (integrable_const 1) ?_ ?_
  · exact ((continuous_id.mul (continuous_const.sub continuous_id)).aestronglyMeasurable)
  · filter_upwards [ae_unitIntervalMeasure_mem_Ioo] with t ht
    obtain ⟨ht0, ht1⟩ := ht
    rw [Real.norm_eq_abs, abs_of_nonneg (by nlinarith)]
    nlinarith

theorem integrable_quantileSpeed_mul_poly (S : PositiveDensitySource)
    (hfin : HasFiniteKernelEnergy S) :
    Integrable (fun u => quantileSpeed S u * (2 * (u * (1 - u)))) unitIntervalMeasure := by
  have hmq : Measurable (quantileSpeed S) :=
    measurable_const.div (S.continuous_k.measurable.comp S.measurable_quantileFun)
  refine Integrable.mono' (hfin.add integrable_poly_unitInterval) ?_ ?_
  · exact (hmq.mul (measurable_const.mul
      (measurable_id.mul (measurable_const.sub measurable_id)))).aestronglyMeasurable
  · filter_upwards [ae_unitIntervalMeasure_mem_Ioo] with u hu
    have hq : 0 < quantileSpeed S u := quantileSpeed_pos S u
    have hw : 0 ≤ u * (1 - u) := by nlinarith [hu.1, hu.2]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simp only [Pi.add_apply]
    linarith only [mul_nonneg (sq_nonneg (quantileSpeed S u - 1)) hw]

theorem integrable_uncurry_abs_slice (S : PositiveDensitySource)
    (hfin : HasFiniteKernelEnergy S) :
    Integrable (fun p : ℝ × ℝ => quantileSpeed S p.1 * |pinnedKernelSlice p.1 p.2|)
      (unitIntervalMeasure.prod unitIntervalMeasure) := by
  rw [integrable_prod_iff (measurable_uncurry_abs_slice S).aestronglyMeasurable]
  refine ⟨?_, ?_⟩
  · filter_upwards [ae_unitIntervalMeasure_mem_Ioo] with u hu
    refine Integrable.mono' (integrable_const (quantileSpeed S u)) ?_ ?_
    · have hite : Measurable (fun s : ℝ => if s ≤ u then (1 : ℝ) else 0) :=
        Measurable.ite (measurableSet_le measurable_id measurable_const)
          measurable_const measurable_const
      exact (measurable_const.mul ((hite.sub measurable_const).abs)).aestronglyMeasurable
    · filter_upwards with s
      have h1 : |pinnedKernelSlice u s| ≤ 1 :=
        abs_pinnedKernelSlice_le (Ioo_subset_Icc_self hu) s
      have hq : 0 < quantileSpeed S u := quantileSpeed_pos S u
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      linarith [mul_le_mul_of_nonneg_left h1 hq.le]
  · refine (integrable_quantileSpeed_mul_poly S hfin).congr ?_
    filter_upwards [ae_unitIntervalMeasure_mem_Ioo] with u hu
    have hpt : ∀ s : ℝ, ‖quantileSpeed S u * |pinnedKernelSlice u s|‖
        = quantileSpeed S u * |pinnedKernelSlice u s| := by
      intro s
      have hq : 0 < quantileSpeed S u := quantileSpeed_pos S u
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
      MeasureTheory.integral_const_mul, unitIntervalMeasure_eq,
      integral_abs_pinnedKernelSlice hu]



/-- **The first interchange.**  Pairing the covariance kernel against the quantile speed produces
the slice moment. -/
theorem integral_quantileSpeed_min_sub (S : PositiveDensitySource)
    (hfin : HasFiniteKernelEnergy S) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (∫ u, quantileSpeed S u * (min t u - t * u) ∂unitIntervalMeasure)
      = ∫ s, pinnedKernelSlice t s * sliceMoment S s ∂unitIntervalMeasure := by
  have hmq : Measurable (quantileSpeed S) :=
    measurable_const.div (S.continuous_k.measurable.comp S.measurable_quantileFun)
  have hset : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1} :=
    measurableSet_le measurable_snd measurable_fst
  have hslice2 : Measurable (fun p : ℝ × ℝ => pinnedKernelSlice p.1 p.2) :=
    (Measurable.ite hset measurable_const measurable_const).sub measurable_fst
  have hslice1 : Measurable (fun p : ℝ × ℝ => pinnedKernelSlice t p.2) :=
    (Measurable.ite (measurableSet_le measurable_snd measurable_const)
      measurable_const measurable_const).sub measurable_const
  have hswapint : Integrable (Function.uncurry
      (fun u s : ℝ => quantileSpeed S u * pinnedKernelSlice t s * pinnedKernelSlice u s))
      (unitIntervalMeasure.prod unitIntervalMeasure) := by
    refine Integrable.mono' (integrable_uncurry_abs_slice S hfin) ?_ ?_
    · exact (((hmq.comp measurable_fst).mul hslice1).mul hslice2).aestronglyMeasurable
    · filter_upwards with p
      have h1 : |pinnedKernelSlice t p.2| ≤ 1 :=
        abs_pinnedKernelSlice_le (Ioo_subset_Icc_self ht) p.2
      have hq : 0 < quantileSpeed S p.1 := quantileSpeed_pos S p.1
      show ‖quantileSpeed S p.1 * pinnedKernelSlice t p.2 * pinnedKernelSlice p.1 p.2‖
        ≤ quantileSpeed S p.1 * |pinnedKernelSlice p.1 p.2|
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hq]
      have h2 : 0 ≤ |pinnedKernelSlice p.1 p.2| := abs_nonneg _
      linarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg hq.le h2)]
  have hL : (∫ u, quantileSpeed S u * (min t u - t * u) ∂unitIntervalMeasure)
      = ∫ u, ∫ s, quantileSpeed S u * pinnedKernelSlice t s * pinnedKernelSlice u s
        ∂unitIntervalMeasure ∂unitIntervalMeasure := by
    refine integral_congr_ae ?_
    filter_upwards [ae_unitIntervalMeasure_mem_Ioo] with u hu
    have hin : (∫ s, quantileSpeed S u * pinnedKernelSlice t s * pinnedKernelSlice u s
          ∂unitIntervalMeasure)
        = quantileSpeed S u * ∫ s, pinnedKernelSlice t s * pinnedKernelSlice u s
          ∂unitIntervalMeasure := by
      rw [← MeasureTheory.integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun s => by ring)
    rw [hin, unitIntervalMeasure_eq, integral_pinnedKernelSlice_mul_min ht hu]
  have hR : (∫ s, pinnedKernelSlice t s * sliceMoment S s ∂unitIntervalMeasure)
      = ∫ s, ∫ u, quantileSpeed S u * pinnedKernelSlice t s * pinnedKernelSlice u s
        ∂unitIntervalMeasure ∂unitIntervalMeasure := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [sliceMoment]
    rw [← MeasureTheory.integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun u => by ring)
  rw [hL, hR]
  exact integral_integral_swap hswapint



/-! ### The second interchange -/

theorem measurable_uncurry_slice_quantile :
    Measurable (Function.uncurry (fun s t : ℝ =>
      quantileSpeed thetaSource t * pinnedKernelSlice t s
        * (-thetaSource.quantileFun s))) := by
  have hmq : Measurable (quantileSpeed thetaSource) := measurable_const.div
    (thetaSource.continuous_k.measurable.comp thetaSource.measurable_quantileFun)
  have hset : MeasurableSet {p : ℝ × ℝ | p.1 ≤ p.2} :=
    measurableSet_le measurable_fst measurable_snd
  have hslice : Measurable (fun p : ℝ × ℝ => pinnedKernelSlice p.2 p.1) :=
    (Measurable.ite hset measurable_const measurable_const).sub measurable_snd
  exact ((hmq.comp measurable_snd).mul hslice).mul
    ((thetaSource.measurable_quantileFun.comp measurable_fst).neg)

theorem integrable_abs_quantileFun_thetaSource :
    Integrable (fun s => |thetaSource.quantileFun s|) unitIntervalMeasure := by
  rw [unitIntervalMeasure_eq]
  exact integrableOn_quantileFun_thetaSource.abs

theorem integrable_sq_quantileFun_thetaSource :
    Integrable (fun s => thetaSource.quantileFun s ^ 2) unitIntervalMeasure := by
  rw [unitIntervalMeasure_eq]
  exact integrableOn_sq_quantileFun_thetaSource

theorem integrable_uncurry_slice_quantile :
    Integrable (Function.uncurry (fun s t : ℝ =>
      quantileSpeed thetaSource t * pinnedKernelSlice t s
        * (-thetaSource.quantileFun s)))
      (unitIntervalMeasure.prod unitIntervalMeasure) := by
  have hhalf : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by constructor <;> norm_num
  set A : ℝ := absSliceMoment thetaSource (1 / 2) with hA
  set B : ℝ := |thetaSource.quantileFun (1 / 2)| with hB
  rw [integrable_prod_iff measurable_uncurry_slice_quantile.aestronglyMeasurable]
  refine ⟨?_, ?_⟩
  · filter_upwards [ae_unitIntervalMeasure_mem_Ioo] with s hs
    simp only [Function.uncurry]
    exact (integrable_quantileSpeed_mul_pinnedKernelSlice thetaSource
      hasFiniteKernelEnergy_thetaSource hs).mul_const _
  · have hdom : Integrable
        (fun s => (A + B) * |thetaSource.quantileFun s| + thetaSource.quantileFun s ^ 2)
        unitIntervalMeasure :=
      (integrable_abs_quantileFun_thetaSource.const_mul (A + B)).add
        integrable_sq_quantileFun_thetaSource
    refine Integrable.mono' hdom
      (measurable_uncurry_slice_quantile.aestronglyMeasurable.norm.integral_prod_right') ?_
    filter_upwards [ae_unitIntervalMeasure_mem_Ioo] with s hs
    simp only [Function.uncurry]
    have hval : (∫ t, ‖quantileSpeed thetaSource t * pinnedKernelSlice t s
          * (-thetaSource.quantileFun s)‖ ∂unitIntervalMeasure)
        = |thetaSource.quantileFun s| * absSliceMoment thetaSource s := by
      simp only [absSliceMoment]
      rw [← MeasureTheory.integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      show ‖quantileSpeed thetaSource t * pinnedKernelSlice t s
          * (-thetaSource.quantileFun s)‖
        = |thetaSource.quantileFun s| * (quantileSpeed thetaSource t
          * |pinnedKernelSlice t s|)
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg,
        abs_of_pos (quantileSpeed_pos thetaSource t)]
      ring
    have hle := absSliceMoment_le thetaSource hasFiniteKernelEnergy_thetaSource hs hhalf
    have hQ : 0 ≤ |thetaSource.quantileFun s| := abs_nonneg _
    have htri : |thetaSource.quantileFun s - thetaSource.quantileFun (1 / 2)|
        ≤ |thetaSource.quantileFun s| + B := by
      rw [hB]
      exact abs_sub _ _
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun t => norm_nonneg _), hval]
    linarith only [mul_le_mul_of_nonneg_left hle hQ,
      mul_le_mul_of_nonneg_left htri hQ, sq_abs (thetaSource.quantileFun s)]



/-- **The double kernel integral is the source variance.** -/
theorem integral_double_min_sub_eq :
    (∫ t, ∫ u, quantileSpeed thetaSource t * quantileSpeed thetaSource u * (min t u - t * u)
        ∂unitIntervalMeasure ∂unitIntervalMeasure)
      = ∫ s, thetaSource.quantileFun s ^ 2 ∂unitIntervalMeasure := by
  have hstep1 : (∫ t, ∫ u, quantileSpeed thetaSource t * quantileSpeed thetaSource u
        * (min t u - t * u) ∂unitIntervalMeasure ∂unitIntervalMeasure)
      = ∫ t, ∫ s, quantileSpeed thetaSource t * pinnedKernelSlice t s
        * (-thetaSource.quantileFun s) ∂unitIntervalMeasure ∂unitIntervalMeasure := by
    refine integral_congr_ae ?_
    filter_upwards [ae_unitIntervalMeasure_mem_Ioo] with t ht
    have h1 : (∫ u, quantileSpeed thetaSource t * quantileSpeed thetaSource u
          * (min t u - t * u) ∂unitIntervalMeasure)
        = quantileSpeed thetaSource t
          * ∫ u, quantileSpeed thetaSource u * (min t u - t * u) ∂unitIntervalMeasure := by
      rw [← MeasureTheory.integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun u => by ring)
    have h2 := integral_quantileSpeed_min_sub thetaSource hasFiniteKernelEnergy_thetaSource ht
    have h3 : (∫ s, pinnedKernelSlice t s * sliceMoment thetaSource s ∂unitIntervalMeasure)
        = ∫ s, pinnedKernelSlice t s * (-thetaSource.quantileFun s) ∂unitIntervalMeasure := by
      refine integral_congr_ae ?_
      filter_upwards [ae_unitIntervalMeasure_mem_Ioo] with s hs
      rw [sliceMoment_eq_neg_quantileFun hs]
    have h4 : (∫ s, quantileSpeed thetaSource t * pinnedKernelSlice t s
          * (-thetaSource.quantileFun s) ∂unitIntervalMeasure)
        = quantileSpeed thetaSource t * ∫ s, pinnedKernelSlice t s
          * (-thetaSource.quantileFun s) ∂unitIntervalMeasure := by
      rw [← MeasureTheory.integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun s => by ring)
    rw [h1, h2, h3, h4]
  rw [hstep1, ← integral_integral_swap integrable_uncurry_slice_quantile]
  refine integral_congr_ae ?_
  filter_upwards [ae_unitIntervalMeasure_mem_Ioo] with s hs
  have h5 : (∫ t, quantileSpeed thetaSource t * pinnedKernelSlice t s
        * (-thetaSource.quantileFun s) ∂unitIntervalMeasure)
      = (-thetaSource.quantileFun s) * sliceMoment thetaSource s := by
    simp only [sliceMoment]
    rw [← MeasureTheory.integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => by ring)
  show (∫ t, quantileSpeed thetaSource t * pinnedKernelSlice t s
      * (-thetaSource.quantileFun s) ∂unitIntervalMeasure) = _
  rw [h5, sliceMoment_eq_neg_quantileFun hs]
  ring

/-- **The trace calibration.**  The first nontrivial trace invariant of the compressed source
inverse is the source variance:  `tr(B²) = M⁻¹ ∫ x² k(x) dx`. -/
theorem thetaTraceSq_eq_source_variance :
    thetaTraceSq
      = ((thetaSource.mass⁻¹ * ∫ x : ℝ, x ^ 2 * thetaCuspFullSource x : ℝ) : ℂ) := by
  rw [thetaTraceSq_eq_double_integral]
  have hinner : ∀ t : ℝ, (∫ u, ((quantileSpeed thetaSource t * quantileSpeed thetaSource u
        * (min t u - t * u) : ℝ) : ℂ) ∂unitIntervalMeasure)
      = (((∫ u, quantileSpeed thetaSource t * quantileSpeed thetaSource u * (min t u - t * u)
        ∂unitIntervalMeasure : ℝ)) : ℂ) := fun t => integral_complex_ofReal
  rw [integral_congr_ae (Filter.Eventually.of_forall hinner), integral_complex_ofReal,
    integral_double_min_sub_eq, unitIntervalMeasure_eq, integral_sq_quantileFun]


end HedenmalmThetaSource

end

end RHTower
