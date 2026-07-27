import GaloisForLFunctions.RHTower.MobiusCausalMidRangeBound
import GaloisForLFunctions.RHTower.MobiusCausalNearOriginBound
import GaloisForLFunctions.HTGeometry.GammaCyclicDensityTail

/-!
# The boundary majorant of the parameter derivative

The near-origin, mid-range and far-field bounds combine into one majorant on the boundary line,
uniform in the parameter:

```text
‖∂_ω M_ω(iτ)‖ ≤ K·1_{|τ|≤9} + C·log²⁶|τ|/|τ|·1_{|τ|>9}      (0 < ω ≤ ω₀, τ ≠ 0),
```

whose square is integrable — the constant part lives on a bounded interval and the far part is
dominated by `|τ|^{-3/2}` because every log power is.
-/

open MeasureTheory Filter Topology Complex Set

namespace RHTower

noncomputable section

/-- Every log power is dominated by a root. -/
theorem log_pow_le_rpow {x : ℝ} (hx : 9 ≤ |x|) :
    Real.log |x| ^ 52 ≤ 104 ^ 52 * |x| ^ (1 / 2 : ℝ) := by
  have hx0 : (0 : ℝ) < |x| := by linarith
  have hroot : (0 : ℝ) < |x| ^ (1 / 104 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hlog : Real.log |x| ≤ 104 * |x| ^ (1 / 104 : ℝ) := by
    have h1 : Real.log (|x| ^ (1 / 104 : ℝ)) = (1 / 104 : ℝ) * Real.log |x| :=
      Real.log_rpow hx0 _
    have h2 : Real.log (|x| ^ (1 / 104 : ℝ)) ≤ |x| ^ (1 / 104 : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos hroot
    rw [h1] at h2
    linarith
  have hlognn : (0 : ℝ) ≤ Real.log |x| := Real.log_nonneg (by linarith)
  have hpow : Real.log |x| ^ 52 ≤ (104 * |x| ^ (1 / 104 : ℝ)) ^ 52 :=
    pow_le_pow_left₀ hlognn hlog 52
  have hid : (104 * |x| ^ (1 / 104 : ℝ)) ^ 52 = 104 ^ 52 * |x| ^ (1 / 2 : ℝ) := by
    rw [mul_pow]
    congr 1
    rw [← Real.rpow_natCast (|x| ^ (1 / 104 : ℝ)) 52, ← Real.rpow_mul (abs_nonneg x)]
    norm_num
  rw [hid] at hpow
  exact hpow

/-- The constant part of the boundary majorant. -/
def boundaryNear : Set ℝ := {t : ℝ | |t| ≤ 9}

/-- The decaying part of the boundary majorant. -/
def boundaryFar : Set ℝ := {t : ℝ | 9 < |t|}

theorem measurableSet_boundaryNear : MeasurableSet boundaryNear :=
  measurableSet_le continuous_abs.measurable measurable_const

theorem measurableSet_boundaryFar : MeasurableSet boundaryFar :=
  measurableSet_lt measurable_const continuous_abs.measurable

/-- The square majorant used for dominated convergence on the boundary. -/
def boundaryBound (K : ℝ) (τ : ℝ) : ℝ :=
  Set.indicator boundaryNear (fun _ => 4 * K ^ 2) τ +
    Set.indicator boundaryFar
      (fun t => 4 * (farFieldConstant * Real.log |t| ^ 26 / |t|) ^ 2) τ

theorem integrable_boundaryBound (K : ℝ) : Integrable (boundaryBound K) := by
  have h1 : Integrable (Set.indicator boundaryNear (fun _ => 4 * K ^ 2)) := by
    rw [integrable_indicator_iff measurableSet_boundaryNear]
    have hsub : boundaryNear ⊆ Set.Icc (-9 : ℝ) 9 := by
      intro t ht
      have : |t| ≤ 9 := ht
      exact Set.mem_Icc.2 (abs_le.1 this)
    have hfin : volume boundaryNear ≠ ⊤ := by
      refine ne_of_lt (lt_of_le_of_lt (measure_mono hsub) ?_)
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_lt_top
    exact integrableOn_const hfin
  have h2 : Integrable (Set.indicator boundaryFar
      (fun t => 4 * (farFieldConstant * Real.log |t| ^ 26 / |t|) ^ 2)) := by
    rw [integrable_indicator_iff measurableSet_boundaryFar]
    have hdom : IntegrableOn
        (fun t : ℝ => (4 * farFieldConstant ^ 2 * 104 ^ 52) * |t| ^ (-(3 / 2) : ℝ))
        boundaryFar := by
      have hsub : boundaryFar ⊆ {x : ℝ | 3 ≤ |x|} := by
        intro t ht
        have h9 : (9 : ℝ) < |t| := ht
        show (3 : ℝ) ≤ |t|
        linarith
      exact ((HTGeometry.integrableOn_abs_rpow_tail.mono_set hsub).const_mul _)
    refine Integrable.mono hdom ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_boundaryFar
      intro t ht
      have h9 : (9 : ℝ) < |t| := ht
      have ht0 : t ≠ 0 := by
        intro h
        rw [h, abs_zero] at h9
        linarith
      have hc : ContinuousAt (fun t : ℝ => 4 * (farFieldConstant * Real.log |t| ^ 26 / |t|) ^ 2) t := by
        have habs : ContinuousAt (fun t : ℝ => |t|) t := continuous_abs.continuousAt
        have hlog : ContinuousAt (fun t : ℝ => Real.log |t|) t :=
          (Real.continuousAt_log (by simpa using ht0)).comp habs
        have habs0 : |t| ≠ 0 := by simpa using ht0
        exact (((hlog.pow 26).const_mul farFieldConstant).div habs habs0).pow 2 |>.const_mul 4
      exact hc.continuousWithinAt
    · filter_upwards [ae_restrict_mem measurableSet_boundaryFar] with t ht
      have h9 : 9 < |t| := ht
      have ht0 : (0 : ℝ) < |t| := by linarith
      have hlog := log_pow_le_rpow (le_of_lt h9)
      have hsq : (farFieldConstant * Real.log |t| ^ 26 / |t|) ^ 2
          = farFieldConstant ^ 2 * Real.log |t| ^ 52 / |t| ^ 2 := by
        rw [div_pow, mul_pow, ← pow_mul]
      have hFnn : (0 : ℝ) ≤ farFieldConstant := farFieldConstant_nonneg
      have hkey : farFieldConstant ^ 2 * Real.log |t| ^ 52 / |t| ^ 2
          ≤ farFieldConstant ^ 2 * (104 ^ 52 * |t| ^ (1 / 2 : ℝ)) / |t| ^ 2 := by
        apply div_le_div_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hlog (by positivity)
      have hrpow : |t| ^ (1 / 2 : ℝ) / |t| ^ 2 = |t| ^ (-(3 / 2) : ℝ) := by
        rw [← Real.rpow_natCast |t| 2, ← Real.rpow_sub ht0]
        norm_num
      have hlhs0 : (0 : ℝ) ≤ 4 * (farFieldConstant * Real.log |t| ^ 26 / |t|) ^ 2 := by positivity
      have hrhs0 : (0 : ℝ) ≤ 4 * farFieldConstant ^ 2 * 104 ^ 52 * |t| ^ (-(3 / 2) : ℝ) := by
        have : (0 : ℝ) ≤ |t| ^ (-(3 / 2) : ℝ) := Real.rpow_nonneg (abs_nonneg t) _
        positivity
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlhs0, abs_of_nonneg hrhs0, hsq]
      have hfinal : farFieldConstant ^ 2 * (104 ^ 52 * |t| ^ (1 / 2 : ℝ)) / |t| ^ 2
          = farFieldConstant ^ 2 * 104 ^ 52 * |t| ^ (-(3 / 2) : ℝ) := by
        rw [← hrpow]
        ring
      have hstep := mul_le_mul_of_nonneg_left (le_trans hkey (le_of_eq hfinal))
        (by norm_num : (0 : ℝ) ≤ 4)
      calc 4 * (farFieldConstant ^ 2 * Real.log |t| ^ 52 / |t| ^ 2)
          ≤ 4 * (farFieldConstant ^ 2 * 104 ^ 52 * |t| ^ (-(3 / 2) : ℝ)) := hstep
        _ = 4 * farFieldConstant ^ 2 * 104 ^ 52 * |t| ^ (-(3 / 2) : ℝ) := by ring
  exact h1.add h2

end

end RHTower
