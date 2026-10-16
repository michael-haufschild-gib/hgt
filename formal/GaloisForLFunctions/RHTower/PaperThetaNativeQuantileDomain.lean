import GaloisForLFunctions.RHTower.PaperThetaNativeResolvent
import GaloisForLFunctions.RHTower.PaperThetaBranchAbsoluteContinuity

/-! # The whole native differential domain survives the singular quantile

The original two-ended trace supplies both compact endpoints. Variation is
preserved exactly, and the actual derivative has its interval primitive.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex

namespace RHTower.PaperThetaEndpoint
open HedenmalmThetaSource HedenmalmQuantile

def nativeClosedQuantile (f : ThetaNativeDomain) (t : ℝ) : ℂ :=
  if t ∈ Ioo (0 : ℝ) 1 then f (thetaSource.quantileFun t) else thetaTailTrace f

theorem nativeClosedQuantile_interior (f : ThetaNativeDomain) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    nativeClosedQuantile f t = f (thetaSource.quantileFun t) := if_pos ht

theorem nativeClosedQuantile_endpoints (f : ThetaNativeDomain) :
    nativeClosedQuantile f 0 = thetaTailTrace f ∧
      nativeClosedQuantile f 1 = thetaTailTrace f := by simp [nativeClosedQuantile]

theorem differentiableAt_nativeClosedQuantile (f : ThetaNativeDomain)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ (nativeClosedQuantile f) t := by
  have hd := (f.differentiable (thetaSource.quantileFun t)).comp t
    (hasDerivAt_quantileFun thetaSource ht).differentiableAt
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
  exact nativeClosedQuantile_interior f hx

theorem continuousOn_nativeClosedQuantile (f : ThetaNativeDomain) :
    ContinuousOn (nativeClosedQuantile f) (Icc (0 : ℝ) 1) := by
  let F : ℝ → ℂ := fun t => f (thetaSource.quantileFun t)
  have hi : ContinuousOn F (Ioo (0 : ℝ) 1) := fun t ht =>
    ((f.differentiable _).comp t (hasDerivAt_quantileFun thetaSource ht).differentiableAt).continuousAt.continuousWithinAt
  have hl : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 (thetaTailTrace f)) :=
    f.leftTrace.comp (tendsto_quantileFun_nhdsGT_zero thetaSource)
  have hr : Tendsto F (𝓝[<] (1 : ℝ)) (𝓝 (thetaTailTrace f)) :=
    f.rightTrace.comp (tendsto_quantileFun_nhdsLT_one thetaSource)
  apply (continuousOn_Icc_extendFrom_Ioo hi hl hr).congr
  intro t ht
  rcases eq_endpoints_or_mem_Ioo_of_mem_Icc ht with rfl | rfl | ht
  · rw [(nativeClosedQuantile_endpoints f).1,
      eq_lim_at_left_extendFrom_Ioo (by norm_num) hl]
  · rw [(nativeClosedQuantile_endpoints f).2,
      eq_lim_at_right_extendFrom_Ioo (by norm_num) hr]
  · rw [nativeClosedQuantile_interior f ht, extendFrom_extends hi t ht]

/-- Neither the singular coordinate nor endpoint completion loses variation. -/
theorem eVariationOn_nativeClosedQuantile (f : ThetaNativeDomain) :
    eVariationOn (nativeClosedQuantile f) (Icc (0 : ℝ) 1) = eVariationOn f univ := by
  have himage : thetaSource.quantileFun '' Ioo (0 : ℝ) 1 = univ := by
    apply eq_univ_of_forall
    intro x
    exact ⟨thetaSource.cdfFun x, thetaSource.cdfFun_mem_Ioo x, thetaSource.quantile_cdfFun x⟩
  have hi : eVariationOn (nativeClosedQuantile f) (Ioo (0 : ℝ) 1) = eVariationOn f univ := by
    rw [eVariationOn.congr (fun t ht => nativeClosedQuantile_interior f ht)]
    change eVariationOn (f ∘ thetaSource.quantileFun) _ = _
    rw [eVariationOn.comp_eq_of_monotoneOn _ _ thetaSource.strictMonoOn_quantileFun.monotoneOn,
      himage]
  have hc := continuousOn_nativeClosedQuantile f
  have h0 : ContinuousWithinAt (nativeClosedQuantile f) (Ici (0 : ℝ)) 0 := by
    have h := hc 0 (by norm_num)
    simpa only [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsGE (show (0 : ℝ) < 1 by norm_num)] using h
  have h1 : ContinuousWithinAt (nativeClosedQuantile f) (Iic (1 : ℝ)) 1 := by
    have h := hc 1 (by norm_num)
    simpa only [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsLE (show (0 : ℝ) < 1 by norm_num)] using h
  have hne : (𝓝[Ioi (0 : ℝ) ∩ Iio 1] (1 : ℝ)).NeBot := by
    rw [Ioi_inter_Iio, nhdsWithin_Ioo_eq_nhdsLT (show (0 : ℝ) < 1 by norm_num)]
    infer_instance
  have hright := eVariationOn.eVariationOn_inter_Iio_eq_inter_Iic_of_continuousWithinAt hne
    (h1.mono inter_subset_right : ContinuousWithinAt (nativeClosedQuantile f)
      (Ioi (0 : ℝ) ∩ Iic 1) 1)
  rw [Ioi_inter_Iio, Ioi_inter_Iic] at hright
  rw [← eVariationOn.eVariationOn_Ioc_eq_Icc_of_continuousWithinAt h0, ← hright, hi]

theorem boundedVariationOn_nativeClosedQuantile (f : ThetaNativeDomain) :
    BoundedVariationOn (nativeClosedQuantile f) (Icc (0 : ℝ) 1) := by
  change eVariationOn _ _ ≠ ⊤
  rw [eVariationOn_nativeClosedQuantile]
  exact f.bv

theorem intervalIntegrable_deriv_nativeClosedQuantile (f : ThetaNativeDomain) :
    IntervalIntegrable (deriv (nativeClosedQuantile f)) volume 0 1 :=
  intervalIntegrable_complex_deriv_of_bv zero_le_one (boundedVariationOn_nativeClosedQuantile f)
    (fun _ ht => differentiableAt_nativeClosedQuantile f ht)

theorem nativeClosedQuantile_primitive (f : ThetaNativeDomain) (t : Icc (0 : ℝ) 1) :
    nativeClosedQuantile f t.val = thetaTailTrace f+
      ∫ x in (0 : ℝ)..t.val, deriv (nativeClosedQuantile f) x := by
  have hs : Icc (0 : ℝ) t.val ⊆ Icc 0 1 := Icc_subset_Icc le_rfl t.property.2
  have ht := (intervalIntegrable_deriv_nativeClosedQuantile f).mono_set (by
    simpa only [uIcc_of_le t.property.1, uIcc_of_le zero_le_one] using hs)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le t.property.1
    ((continuousOn_nativeClosedQuantile f).mono hs)
    (fun x hx => (differentiableAt_nativeClosedQuantile f
      ⟨hx.1, hx.2.trans_le t.property.2⟩).hasDerivAt) ht
  rw [(nativeClosedQuantile_endpoints f).1] at he
  rw [he]
  ring

/-- Every forced solution is an actual compact absolutely continuous profile. -/
theorem absolutelyContinuousOnInterval_nativeClosedQuantile (f : ThetaNativeDomain) :
    AbsolutelyContinuousOnInterval (nativeClosedQuantile f) 0 1 := by
  have hp := GaloisForLFunctions.HTGeometry.IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral_normed
    (intervalIntegrable_deriv_nativeClosedQuantile f) (c := 0) (by simp)
  have hk : AbsolutelyContinuousOnInterval (fun _ : ℝ => thetaTailTrace f) 0 1 :=
    (LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval
  apply (hk.fun_add hp).congr
  intro t ht
  rw [uIcc_of_le zero_le_one] at ht
  exact (nativeClosedQuantile_primitive f ⟨t, ht⟩).symm

theorem integral_deriv_nativeClosedQuantile (f : ThetaNativeDomain) :
    (∫ x in (0 : ℝ)..1, deriv (nativeClosedQuantile f) x) = 0 := by
  have h := nativeClosedQuantile_primitive f ⟨1, by norm_num⟩
  rw [(nativeClosedQuantile_endpoints f).2] at h
  exact add_eq_left.mp h.symm

end RHTower.PaperThetaEndpoint
