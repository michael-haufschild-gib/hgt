import GaloisForLFunctions.RHTower.PaperThetaCutBranches
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-! # The full theta current on one fixed compact interval

The actual derivative is integrable on each side of any interior cut.
Its missing mass is exactly one interior atom. Integration by parts retains
both endpoint traces and the complete, signed connection coefficient.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped SchwartzMap

namespace RHTower.PaperThetaEndpoint
open HedenmalmThetaSource HedenmalmQuantile

def cutQuantileMode (z : ℂ) (c : Ioo (0 : ℝ) 1) (t : ℝ) : ℂ :=
  if t < c.val then leftClosedQuantileMode z t else closedQuantileMode z t

theorem cutQuantileMode_endpoints (z : ℂ) (c : Ioo (0 : ℝ) 1) :
    cutQuantileMode z c 0 = -1 ∧ cutQuantileMode z c 1 = -1 := by
  simp only [cutQuantileMode, if_pos c.property.1,
    if_neg (not_lt.mpr c.property.2.le), leftClosedQuantileMode_zero,
    (closedQuantileMode_endpoints z).2, and_self]

theorem cutQuantileMode_interior (z : ℂ) (c t : Ioo (0 : ℝ) 1) :
    cutQuantileMode z c t.val = cutQuotient z
      (thetaSource.quantileFun c.val) (thetaSource.quantileFun t.val) := by
  by_cases h : t.val < c.val
  · rw [cutQuantileMode, if_pos h, leftClosedQuantileMode_interior,
      cutQuotient_left z (thetaSource.strictMonoOn_quantileFun t.property c.property h)]
  · rw [cutQuantileMode, if_neg h, closedQuantileMode_interior,
      flatModePullback_eq_flatQuotient,
      cutQuotient_right z (thetaSource.strictMonoOn_quantileFun.monotoneOn
        c.property t.property (le_of_not_gt h))]

theorem cutQuantileMode_eventuallyEq_left (z : ℂ) (c : Ioo (0 : ℝ) 1)
    {t : ℝ} (ht : t < c.val) :
    cutQuantileMode z c =ᶠ[𝓝 t] leftClosedQuantileMode z := by
  filter_upwards [Iio_mem_nhds ht] with x hx
  exact if_pos hx

theorem cutQuantileMode_eventuallyEq_right (z : ℂ) (c : Ioo (0 : ℝ) 1)
    {t : ℝ} (ht : c.val < t) :
    cutQuantileMode z c =ᶠ[𝓝 t] closedQuantileMode z := by
  filter_upwards [Ioi_mem_nhds ht] with x hx
  exact if_neg (not_lt.mpr hx.le)

theorem boundedVariationOn_cutQuantileMode (z : ℂ) (c : Ioo (0 : ℝ) 1) :
    BoundedVariationOn (cutQuantileMode z c) (Icc (0 : ℝ) 1) := by
  have hl : eVariationOn (cutQuantileMode z c) (Ico (0 : ℝ) c.val) ≠ ⊤ := by
    rw [eVariationOn.congr (s := Ico (0 : ℝ) c.val)
      (fun t ht => show cutQuantileMode z c t = leftClosedQuantileMode z t from if_pos ht.2)]
    exact ne_top_of_le_ne_top (boundedVariationOn_leftClosedQuantileMode z c)
      (eVariationOn.mono _ Ico_subset_Icc_self)
  have hlim : Tendsto (cutQuantileMode z c) (𝓝[<] c.val)
      (𝓝 (leftClosedQuantileMode z c.val)) := by
    apply ((differentiableAt_leftClosedQuantileMode z c).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds).congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (show cutQuantileMode z c t = leftClosedQuantileMode z t from if_pos ht).symm
  have he := eVariationOn.eVariationOn_on_inter_Iic_eq_Iio_add_edist
    (f := cutQuantileMode z c) (s := Ici (0 : ℝ)) (a := c.val)
    (l := leftClosedQuantileMode z c.val)
    (by rw [Ici_inter_Iio, nhdsWithin_Ico_eq_nhdsLT c.property.1]; infer_instance)
    c.property.1.le
    (by simpa only [Ici_inter_Iio, nhdsWithin_Ico_eq_nhdsLT c.property.1] using hlim)
  rw [Ici_inter_Iic, Ici_inter_Iio] at he
  have hlc : eVariationOn (cutQuantileMode z c) (Icc (0 : ℝ) c.val) ≠ ⊤ := by
    rw [he]
    exact ENNReal.add_ne_top.mpr ⟨hl, edist_ne_top _ _⟩
  have hr : eVariationOn (cutQuantileMode z c) (Icc c.val 1) ≠ ⊤ := by
    rw [eVariationOn.congr (s := Icc c.val 1)
      (fun t ht => show cutQuantileMode z c t = closedQuantileMode z t from
        if_neg (not_lt.mpr ht.1))]
    exact boundedVariationOn_closedQuantileMode_right z c
  change eVariationOn (cutQuantileMode z c) (Icc (0 : ℝ) 1) ≠ ⊤
  rw [← Icc_union_Icc_eq_Icc c.property.1.le c.property.2.le,
    eVariationOn.union (cutQuantileMode z c)
      (s := Icc (0 : ℝ) c.val) (t := Icc c.val 1) (x := c.val)
      ⟨⟨c.property.1.le, le_rfl⟩, fun _ h => h.2⟩
      ⟨⟨le_rfl, c.property.2.le⟩, fun _ h => h.1⟩]
  exact ENNReal.add_ne_top.mpr ⟨hlc, hr⟩

theorem intervalIntegrable_deriv_cutQuantileMode_left (z : ℂ) (c : Ioo (0 : ℝ) 1) :
    IntervalIntegrable (deriv (cutQuantileMode z c)) volume 0 c.val := by
  apply (intervalIntegrable_deriv_leftClosedQuantileMode z c).congr_uIoo
  intro t ht
  rw [uIoo_of_le c.property.1.le] at ht
  exact (cutQuantileMode_eventuallyEq_left z c ht.2).deriv_eq.symm

theorem intervalIntegrable_deriv_cutQuantileMode_right (z : ℂ) (c : Ioo (0 : ℝ) 1) :
    IntervalIntegrable (deriv (cutQuantileMode z c)) volume c.val 1 := by
  apply (intervalIntegrable_deriv_closedQuantileMode_right z c).congr_uIoo
  intro t ht
  rw [uIoo_of_le c.property.2.le] at ht
  exact (cutQuantileMode_eventuallyEq_right z c ht.1).deriv_eq.symm

/-- The density is the actual derivative, not an unspecified weak representative. -/
theorem intervalIntegrable_deriv_cutQuantileMode (z : ℂ) (c : Ioo (0 : ℝ) 1) :
    IntervalIntegrable (deriv (cutQuantileMode z c)) volume 0 1 :=
  (intervalIntegrable_deriv_cutQuantileMode_left z c).trans
    (intervalIntegrable_deriv_cutQuantileMode_right z c)

private theorem cutIntegral_left (z : ℂ) (c : Ioo (0 : ℝ) 1) (f : ℝ → ℂ) :
    (∫ t in (0 : ℝ)..c.val, cutQuantileMode z c t * f t) =
      ∫ t in (0 : ℝ)..c.val, leftClosedQuantileMode z t * f t :=
  intervalIntegral.integral_congr_Ioo_of_le c.property.1.le fun t ht => by
    simp only [cutQuantileMode, if_pos ht.2]

private theorem cutIntegral_right (z : ℂ) (c : Ioo (0 : ℝ) 1) (f : ℝ → ℂ) :
    (∫ t in c.val..1, cutQuantileMode z c t * f t) =
      ∫ t in c.val..1, closedQuantileMode z t * f t :=
  intervalIntegral.integral_congr_Ioo_of_le c.property.2.le fun t ht => by
    simp only [cutQuantileMode, if_neg (not_lt.mpr ht.1.le)]

private theorem cutDerivIntegral_left (z : ℂ) (c : Ioo (0 : ℝ) 1) (f : ℝ → ℂ) :
    (∫ t in (0 : ℝ)..c.val, deriv (cutQuantileMode z c) t * f t) =
      ∫ t in (0 : ℝ)..c.val, deriv (leftClosedQuantileMode z) t * f t :=
  intervalIntegral.integral_congr_Ioo_of_le c.property.1.le fun t ht => by
    rw [(cutQuantileMode_eventuallyEq_left z c ht.2).deriv_eq]

private theorem cutDerivIntegral_right (z : ℂ) (c : Ioo (0 : ℝ) 1) (f : ℝ → ℂ) :
    (∫ t in c.val..1, deriv (cutQuantileMode z c) t * f t) =
      ∫ t in c.val..1, deriv (closedQuantileMode z) t * f t :=
  intervalIntegral.integral_congr_Ioo_of_le c.property.2.le fun t ht => by
    rw [(cutQuantileMode_eventuallyEq_right z c ht.1).deriv_eq]

/-- All source parameters have an exact compact weak current: L1 density plus one Dirac atom. -/
theorem cutQuantileMode_weak_current (z : ℂ) (c : Ioo (0 : ℝ) 1) (φ : 𝓢(ℝ, ℂ)) :
    (∫ t in (0 : ℝ)..1, cutQuantileMode z c t * deriv φ t) =
      φ 0 - φ 1 - (∫ t in (0 : ℝ)..1, deriv (cutQuantileMode z c) t * φ t) -
        cutCharge z (thetaSource.quantileFun c.val) * φ c.val := by
  have hL : ContinuousOn (leftClosedQuantileMode z) (uIcc (0 : ℝ) c.val) := by
    simpa only [uIcc_of_le c.property.1.le] using continuousOn_leftClosedQuantileMode z c
  have hR : ContinuousOn (closedQuantileMode z) (uIcc c.val 1) := by
    simpa only [uIcc_of_le c.property.2.le] using continuousOn_closedQuantileMode_right z c
  have hφ' : Continuous (deriv φ) := (SchwartzMap.derivCLM ℂ ℂ φ).continuous
  have hDL := intervalIntegrable_deriv_leftClosedQuantileMode z c
  have hDR := intervalIntegrable_deriv_closedQuantileMode_right z c
  have hleft := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hL φ.continuous.continuousOn
    (fun t ht => (differentiableAt_leftClosedQuantileMode z
      ⟨t, by simpa [min_eq_left c.property.1.le, max_eq_right c.property.1.le] using ht.1,
        by have := ht.2; simp only [max_eq_right c.property.1.le] at this; exact this.trans c.property.2⟩).hasDerivAt)
    (fun t _ => φ.hasDerivAt t) hDL (hφ'.intervalIntegrable _ _)
  have hright := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hR φ.continuous.continuousOn
    (fun t ht => (differentiableAt_closedQuantileMode z
      ⟨t, by have := ht.1; simp only [min_eq_left c.property.2.le] at this; exact c.property.1.trans this,
        by simpa [max_eq_right c.property.2.le] using ht.2⟩).hasDerivAt)
    (fun t _ => φ.hasDerivAt t) hDR (hφ'.intervalIntegrable _ _)
  have hML : IntervalIntegrable (fun t => cutQuantileMode z c t * deriv φ t) volume 0 c.val := by
    have hi : IntervalIntegrable (fun t => leftClosedQuantileMode z t * deriv φ t)
        volume 0 c.val := (hL.mul hφ'.continuousOn).intervalIntegrable
    apply hi.congr_uIoo
    intro t ht
    rw [uIoo_of_le c.property.1.le] at ht
    simp only [cutQuantileMode, if_pos ht.2]
  have hMR : IntervalIntegrable (fun t => cutQuantileMode z c t * deriv φ t) volume c.val 1 := by
    have hi : IntervalIntegrable (fun t => closedQuantileMode z t * deriv φ t)
        volume c.val 1 := (hR.mul hφ'.continuousOn).intervalIntegrable
    apply hi.congr_uIoo
    intro t ht
    rw [uIoo_of_le c.property.2.le] at ht
    simp only [cutQuantileMode, if_neg (not_lt.mpr ht.1.le)]
  have hJL := (intervalIntegrable_deriv_cutQuantileMode_left z c).mul_continuousOn
    φ.continuous.continuousOn
  have hJR := (intervalIntegrable_deriv_cutQuantileMode_right z c).mul_continuousOn
    φ.continuous.continuousOn
  rw [← intervalIntegral.integral_add_adjacent_intervals hML hMR,
    ← intervalIntegral.integral_add_adjacent_intervals hJL hJR,
    cutIntegral_left, cutIntegral_right, cutDerivIntegral_left, cutDerivIntegral_right,
    hleft, hright, leftClosedQuantileMode_zero, (closedQuantileMode_endpoints z).2,
    ← closedQuantileMode_sub_left z c]
  ring

/-- The one-sided construction agrees with the literal source mode throughout its original domain. -/
theorem cutQuantileMode_eq_native (z : {z : ℂ // z = 0 ∨ XiC z = 0})
    (c : Ioo (0 : ℝ) 1) (t : Icc (0 : ℝ) 1) :
    cutQuantileMode z.val c t.val = closedQuantileMode z.val t.val := by
  rcases eq_endpoints_or_mem_Ioo_of_mem_Icc t.property with ht | ht | ht
  · rw [ht, (cutQuantileMode_endpoints z.val c).1, (closedQuantileMode_endpoints z.val).1]
  · rw [ht, (cutQuantileMode_endpoints z.val c).2, (closedQuantileMode_endpoints z.val).2]
  · rw [cutQuantileMode_interior z.val c ⟨t.val, ht⟩, cutQuotient_eq_native z,
      closedQuantileMode_interior z.val ⟨t.val, ht⟩, flatModePullback_eq_flatQuotient]

end RHTower.PaperThetaEndpoint
