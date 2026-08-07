import GaloisForLFunctions.RHTower.HedenmalmTransposeKernelField
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

local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

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

set_option maxHeartbeats 1000000 in
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

set_option maxHeartbeats 1000000 in
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

end HedenmalmThetaSource

end

end RHTower
