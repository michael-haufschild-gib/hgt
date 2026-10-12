import GaloisForLFunctions.RHTower.PaperThetaBoundedVariation
import GaloisForLFunctions.RHTower.PaperThetaLocalRegularity
import Mathlib.Topology.Order.ExtendFrom

/-! # Exact variation transport through the original theta quantile

The increasing quantile covers the whole source line. Assigning the proven
common trace at the two interval ends preserves its total variation exactly.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower.PaperThetaEndpoint

open HedenmalmThetaSource HedenmalmQuantile

def closedQuantileMode (z : ℂ) (t : ℝ) : ℂ :=
  if t ∈ Ioo (0 : ℝ) 1 then flatModePullback z t else -1

theorem closedQuantileMode_interior (z : ℂ) (t : Ioo (0 : ℝ) 1) :
    closedQuantileMode z t.val = flatModePullback z t.val := by
  simp only [closedQuantileMode, if_pos t.property]

theorem closedQuantileMode_endpoints (z : ℂ) :
    closedQuantileMode z 0 = -1 ∧ closedQuantileMode z 1 = -1 := by
  simp [closedQuantileMode]

theorem closedQuantileMode_zero (t : ℝ) : closedQuantileMode 0 t = -1 := by
  simp [closedQuantileMode, flatModePullback_zero]

private theorem continuousOn_pullback (z : ℂ) :
    ContinuousOn (flatModePullback z) (Ioo (0 : ℝ) 1) :=
  fun t ht => (differentiableAt_pullback z ⟨t, ht⟩).continuousAt.continuousWithinAt

/-- Matching native traces pay the continuous closed-interval representative. -/
theorem continuousOn_closedQuantileMode (z : {z : ℂ // z = 0 ∨ XiC z = 0}) :
    ContinuousOn (closedQuantileMode z.val) (Icc (0 : ℝ) 1) := by
  have hleft : Tendsto (flatModePullback z.val) (𝓝[>] (0 : ℝ)) (𝓝 (-1)) := by
    rcases z.property with hz | hz
    · rw [hz, show flatModePullback 0 = (fun _ : ℝ => (-1 : ℂ)) from funext flatModePullback_zero]
      exact tendsto_const_nhds
    · exact tendsto_divisor_pullback_at_zero ⟨z.val, hz⟩
  have hc := continuousOn_Icc_extendFrom_Ioo (continuousOn_pullback z.val)
    hleft (tendsto_pullback_at_one z.val)
  apply hc.congr
  intro t ht
  rcases eq_endpoints_or_mem_Ioo_of_mem_Icc ht with rfl | rfl | ht
  · rw [(closedQuantileMode_endpoints z.val).1,
      eq_lim_at_left_extendFrom_Ioo (by norm_num) hleft]
  · rw [(closedQuantileMode_endpoints z.val).2,
      eq_lim_at_right_extendFrom_Ioo (by norm_num) (tendsto_pullback_at_one z.val)]
  · rw [closedQuantileMode_interior z.val ⟨t, ht⟩,
      extendFrom_extends (continuousOn_pullback z.val) t ht]

/-- No variation is lost in the increasing, onto source-to-quantile coordinate change. -/
theorem eVariationOn_flatModePullback_Ioo (z : ℂ) :
    eVariationOn (flatModePullback z) (Ioo (0 : ℝ) 1) =
      eVariationOn (flatQuotient z) univ := by
  have himage : thetaSource.quantileFun '' Ioo (0 : ℝ) 1 = univ := by
    apply eq_univ_of_forall
    intro x
    exact ⟨thetaSource.cdfFun x, thetaSource.cdfFun_mem_Ioo x, thetaSource.quantile_cdfFun x⟩
  change eVariationOn (flatQuotient z ∘ thetaSource.quantileFun) _ = _
  rw [eVariationOn.comp_eq_of_monotoneOn _ _ thetaSource.strictMonoOn_quantileFun.monotoneOn,
    himage]

theorem eVariationOn_closedQuantileMode_Ioo (z : ℂ) :
    eVariationOn (closedQuantileMode z) (Ioo (0 : ℝ) 1) =
      eVariationOn (flatQuotient z) univ := by
  rw [eVariationOn.congr (fun t ht => closedQuantileMode_interior z ⟨t, ht⟩),
    eVariationOn_flatModePullback_Ioo]

/-- Assigning the common trace preserves total variation, including infinite variation. -/
theorem eVariationOn_closedQuantileMode (z : ℂ) :
    eVariationOn (closedQuantileMode z) (Icc (0 : ℝ) 1) =
      eVariationOn (flatQuotient z) univ := by
  by_cases hz : z = 0 ∨ XiC z = 0
  · have hc := continuousOn_closedQuantileMode ⟨z, hz⟩
    have h0 : ContinuousWithinAt (closedQuantileMode z) (Ici (0 : ℝ)) 0 := by
      have h := hc 0 (by norm_num)
      simpa only [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsGE (show (0 : ℝ) < 1 by norm_num)] using h
    have h1 : ContinuousWithinAt (closedQuantileMode z) (Iic (1 : ℝ)) 1 := by
      have h := hc 1 (by norm_num)
      simpa only [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsLE (show (0 : ℝ) < 1 by norm_num)] using h
    have hne : (𝓝[Ioi (0 : ℝ) ∩ Iio 1] (1 : ℝ)).NeBot := by
      rw [Ioi_inter_Iio, nhdsWithin_Ioo_eq_nhdsLT (show (0 : ℝ) < 1 by norm_num)]
      infer_instance
    have h1' : ContinuousWithinAt (closedQuantileMode z) (Ioi (0 : ℝ) ∩ Iic 1) 1 :=
      h1.mono inter_subset_right
    have hright := eVariationOn.eVariationOn_inter_Iio_eq_inter_Iic_of_continuousWithinAt hne h1'
    rw [Ioi_inter_Iio, Ioi_inter_Iic] at hright
    rw [← eVariationOn.eVariationOn_Ioc_eq_Icc_of_continuousWithinAt h0, ← hright,
      eVariationOn_closedQuantileMode_Ioo]
  · have htop : eVariationOn (flatQuotient z) univ = ⊤ := by
      by_contra hn
      exact hz ((boundedVariationOn_flatQuotient_iff z).mp hn)
    have hle := eVariationOn.mono (closedQuantileMode z)
      (show Ioo (0 : ℝ) 1 ⊆ Icc 0 1 from Ioo_subset_Icc_self)
    rw [eVariationOn_closedQuantileMode_Ioo, htop] at hle
    rw [htop]
    exact top_unique hle

theorem boundedVariationOn_closedQuantileMode_iff (z : ℂ) :
    BoundedVariationOn (closedQuantileMode z) (Icc (0 : ℝ) 1) ↔ z = 0 ∨ XiC z = 0 := by
  change eVariationOn (closedQuantileMode z) (Icc (0 : ℝ) 1) ≠ ⊤ ↔ _
  rw [eVariationOn_closedQuantileMode]
  exact boundedVariationOn_flatQuotient_iff z

end RHTower.PaperThetaEndpoint
