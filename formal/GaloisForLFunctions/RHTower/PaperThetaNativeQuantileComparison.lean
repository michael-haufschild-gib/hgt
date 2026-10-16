import GaloisForLFunctions.RHTower.PaperThetaNativeMomentIdentity
import GaloisForLFunctions.RHTower.HedenmalmThetaComplexResolventRow
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-! # Whole native space compared with the pinned Hilbert source

The actual native inverse, after subtraction of its actual tail trace, gives
a compact comparison into the quantile Hilbert source. Its only lost vectors
are constants. The comparison retains the full operator equation, so it can
transport generalized modes without a finite-packet admission premise.
-/

noncomputable section
open Complex MeasureTheory Set Filter Topology
open scoped BoundedContinuousFunction

namespace RHTower.PaperThetaEndpoint
open HedenmalmThetaSource HedenmalmQuantile HedenmalmHilbertSchmidt

abbrev NativeQuantileSpace := Lp ℂ 2 unitIntervalMeasure

/-- Bare quantile pullback of a bounded continuous function. -/
def nativeQuantileMap : NativeContinuousSpace →L[ℂ] NativeQuantileSpace :=
  (lawToUnitInterval thetaSource).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (BoundedContinuousFunction.toLp 2 thetaSource.law ℂ)

theorem nativeQuantileMap_ae (v : NativeContinuousSpace) :
    (nativeQuantileMap v : ℝ → ℂ) =ᵐ[unitIntervalMeasure]
      fun t => v (thetaSource.quantileFun t) := by
  have hv := (BoundedContinuousFunction.coeFn_toLp 2 thetaSource.law ℂ v).comp_tendsto
    (measurePreserving_quantile_unitInterval thetaSource).quasiMeasurePreserving.tendsto_ae
  exact (lawToUnitInterval_ae thetaSource _).trans hv

theorem nativeQuantileMap_injective : Function.Injective nativeQuantileMap := by
  intro v w h
  have he := (lawToUnitInterval thetaSource).injective h
  have hlp : (BoundedContinuousFunction.toLp 2 thetaSource.law ℂ v : ℝ → ℂ)
      =ᵐ[thetaSource.law] BoundedContinuousFunction.toLp 2 thetaSource.law ℂ w := by
    rw [he]
  have hae : (v : ℝ → ℂ) =ᵐ[thetaSource.law] w :=
    (BoundedContinuousFunction.coeFn_toLp 2 thetaSource.law ℂ v).symm.trans
      (hlp.trans
        (BoundedContinuousFunction.coeFn_toLp 2 thetaSource.law ℂ w))
  apply BoundedContinuousFunction.ext
  exact congrFun ((v.continuous.ae_eq_iff_eq volume w.continuous).mp
    (thetaSource.law_ae_eq.mp hae))

theorem nativeQuantileMap_constant (c : ℂ) :
    nativeQuantileMap (nativeConstantCLM c) = c • pinnedOne := by
  apply Lp.ext
  filter_upwards [nativeQuantileMap_ae (nativeConstantCLM c),
    Lp.coeFn_smul c pinnedOne, pinnedOne_coeFn] with t ht hs h1
  rw [ht, hs]
  change c = c*pinnedOne t
  rw [h1, mul_one]

theorem pinnedMean_nativeQuantileMap (v : NativeContinuousSpace) :
    pinnedMean (nativeQuantileMap v) = boundedThetaMomentCLM 0 v := by
  rw [pinnedMean, integral_congr_ae (nativeQuantileMap_ae v), unitIntervalMeasure_eq,
    integral_comp_quantile thetaSource v v.continuous.aestronglyMeasurable]
  change (∫ x, thetaSource.normalized x • v x) = ∫ x, flatCharDensity 0 x*v x
  simp only [flatCharDensity, sourceChar, mul_zero, zero_mul, Complex.exp_zero, mul_one,
    Complex.real_smul]

theorem pinnedPrefix_nativeQuantileMap (v : NativeContinuousSpace)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    pinnedPrefix (nativeQuantileMap v) t =
      ∫ x in Iic (thetaSource.quantileFun t), flatCharDensity 0 x*v x := by
  have hcongr : (Iic t).indicator (fun u => (nativeQuantileMap v) u) =ᵐ[unitIntervalMeasure]
      (Iic t).indicator (fun u => v (thetaSource.quantileFun u)) := by
    filter_upwards [nativeQuantileMap_ae v] with u hu
    by_cases hut : u ∈ Iic t
    · simpa only [Set.indicator_of_mem hut] using hu
    · simp only [Set.indicator_of_notMem hut]
  rw [pinnedPrefix, integral_congr_ae hcongr, unitIntervalMeasure_eq,
    setIntegral_indicator measurableSet_Iic, Ioo_inter_Iic ht,
    ← setIntegral_congr_set (μ := volume) (f := fun u => v (thetaSource.quantileFun u))
      Ioo_ae_eq_Ioc,
    setIntegral_comp_quantile thetaSource v v.continuous.aestronglyMeasurable ht]
  simp only [flatCharDensity, sourceChar, mul_zero, zero_mul, Complex.exp_zero, mul_one,
    Complex.real_smul]

/-- The compact comparison uses the actual tail trace, not a chosen mean. -/
def nativeSourceComparison : NativeContinuousSpace →L[ℂ] NativeQuantileSpace :=
  nativeQuantileMap.comp (boundedNativeResidual nativeCompactParameter)

theorem nativeSourceComparison_compact : IsCompactOperator nativeSourceComparison :=
  (isCompactOperator_boundedNativeResidual nativeCompactParameter).clm_comp nativeQuantileMap

theorem nativeResidual_zero_tail (v : NativeContinuousSpace) (x : ℝ) :
    boundedNativeResidual nativeCompactParameter v x =
      I*boundedThetaTail 0 (v+I • nativeCompactResolvent v) x := by
  let h := v+I • nativeCompactResolvent v
  let r : ℝ → ℂ := fun y => boundedNativeResidual nativeCompactParameter v y
  have hr : Differentiable ℝ r := fun y =>
    (hasDerivAt_boundedNativeResidual nativeCompactParameter v y).differentiableAt
  have hs : Differentiable ℝ (fun y => I*boundedThetaTail 0 h y) := fun y =>
    ((hasDerivAt_boundedThetaTail 0 h y).const_mul I).differentiableAt
  have ht : Tendsto r atTop (𝓝 0) := by
    change Tendsto (fun y => boundedNativeResolvent nativeCompactParameter v y-
      boundedResolventTrace nativeCompactParameter v) atTop (𝓝 0)
    have hh := (boundedNativeResolvent_atTop nativeCompactParameter v).sub_const
      (boundedResolventTrace nativeCompactParameter v)
    simpa only [sub_self] using hh
  have hz := nativeODE_zero_of_trace_zero 0 (fun y => r y-I*boundedThetaTail 0 h y)
    (hr.sub hs)
    (by simpa only [mul_zero, sub_zero] using
      (ht.sub ((tendsto_boundedThetaTail_atTop 0 h).const_mul I))) (fun y => ?_)
  · exact sub_eq_zero.mp (congrFun hz x)
  · rw [deriv_sub (hr y) (hs y),
      ((hasDerivAt_boundedThetaTail 0 h y).const_mul I).deriv]
    have he := boundedNativeResolvent_ode nativeCompactParameter v y
    rw [nativeCompactParameter_val] at he
    have hd : deriv r y = deriv (nativeCompactResolvent v) y := by
      exact deriv_sub_const (boundedResolventTrace nativeCompactParameter v)
    rw [hd]
    change deriv (nativeCompactResolvent v) y-
      I*(-(sourceLogDerivative y+I*0)*boundedThetaTail 0 h y-h y)+
      (sourceLogDerivative y+I*0)*
        ((nativeCompactResolvent v y-boundedResolventTrace nativeCompactParameter v)-
          I*boundedThetaTail 0 h y) = 0
    dsimp only [h, BoundedContinuousFunction.add_apply,
      BoundedContinuousFunction.smul_apply, smul_eq_mul]
    dsimp only [nativeCompactResolvent] at *
    linear_combination (norm := ring_nf) he
    simp only [Complex.I_sq]
    ring

/-- Exact comparison on every bounded continuous forcing. -/
theorem thetaKernel_native_source_identity (v : NativeContinuousSpace) :
    thetaKernelOperator (nativeQuantileMap (v+I • nativeCompactResolvent v)) =
      -nativeSourceComparison v := by
  let h := v+I • nativeCompactResolvent v
  have hm : boundedThetaMomentCLM 0 h = 0 := by
    simpa only [sub_zero, zero_mul, zero_add, add_zero] using nativeCompactResolvent_moment 0 v
  apply Lp.ext
  filter_upwards [pinnedKernelOperator_ae thetaSource hasFiniteKernelEnergy_thetaSource
    (nativeQuantileMap h), nativeQuantileMap_ae (boundedNativeResidual nativeCompactParameter v),
    Lp.coeFn_neg (nativeSourceComparison v), ae_unitIntervalMeasure_mem_Ioo]
    with t hB hJ hn ht
  change thetaKernelOperator (nativeQuantileMap h) t = _ at hB
  change (nativeSourceComparison v : NativeQuantileSpace) t = _ at hJ
  rw [hB, hn, Pi.neg_apply, hJ, pinnedKernelField_apply_eq_pinnedVolterraFun, pinnedVolterraFun,
    pinnedMean_nativeQuantileMap, hm, mul_zero, sub_zero,
    pinnedPrefix_nativeQuantileMap h ht, nativeResidual_zero_tail]
  change I*(quantileSpeed thetaSource t : ℂ)*
      (∫ x in Iic (thetaSource.quantileFun t), flatCharDensity 0 x*h x) =
    -(I*boundedThetaTail 0 h (thetaSource.quantileFun t))
  have hm' : boundedThetaMoment 0 h = 0 := hm
  rw [boundedThetaTail, boundedThetaTail_integral_split, hm', zero_sub]
  simp only [mul_zero, neg_zero, zero_mul, Complex.exp_zero]
  have hs : (quantileSpeed thetaSource t : ℂ) =
      (thetaSource.normalized (thetaSource.quantileFun t) : ℂ)⁻¹ := by
    simp only [quantileSpeed, GaloisForLFunctions.HTGeometry.PositiveDensitySource.normalized,
      Complex.ofReal_div, inv_div]
  rw [hs]
  ring

theorem thetaKernel_nativeQuantile_constant (c : ℂ) :
    thetaKernelOperator (nativeQuantileMap (nativeConstantCLM c)) = 0 := by
  rw [nativeQuantileMap_constant, map_smul, thetaKernelOperator_pinnedOne, smul_zero]

theorem thetaKernel_native_residual (v : NativeContinuousSpace) :
    thetaKernelOperator (nativeQuantileMap (nativeCompactResolvent v)) =
      thetaKernelOperator (nativeSourceComparison v) := by
  change _ = thetaKernelOperator (nativeQuantileMap
    (nativeCompactResolvent v-nativeConstantCLM (boundedResolventTrace nativeCompactParameter v)))
  rw [map_sub, map_sub, thetaKernel_nativeQuantile_constant, sub_zero]

/-- The whole native compact inverse intertwines with the source Möbius pencil. -/
theorem nativeSourceComparison_intertwining (v : NativeContinuousSpace) :
    nativeSourceComparison (nativeCompactResolvent v)+
      I • thetaKernelOperator (nativeSourceComparison (nativeCompactResolvent v)) =
        -thetaKernelOperator (nativeSourceComparison v) := by
  have h := thetaKernel_native_source_identity (nativeCompactResolvent v)
  rw [map_add, map_smul, map_add, map_smul, thetaKernel_native_residual,
    thetaKernel_native_residual] at h
  have hz : thetaKernelOperator (nativeSourceComparison v)+
      I • thetaKernelOperator (nativeSourceComparison (nativeCompactResolvent v))+
      nativeSourceComparison (nativeCompactResolvent v) = 0 := by
    rw [h, neg_add_cancel]
  calc
    _ = (thetaKernelOperator (nativeSourceComparison v)+
        I • thetaKernelOperator (nativeSourceComparison (nativeCompactResolvent v))+
        nativeSourceComparison (nativeCompactResolvent v))-
        thetaKernelOperator (nativeSourceComparison v) := by abel
    _ = _ := by rw [hz, zero_sub]

end RHTower.PaperThetaEndpoint
