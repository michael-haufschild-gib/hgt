import GaloisForLFunctions.HTGeometry.BurnolHalfLineWeightedShift
import GaloisForLFunctions.HTGeometry.HalfLineLaplaceL2
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Causal translations and their Laplace multipliers

Zero extension, whole-line translation, and restriction give strong continuity
of the half-line shifts. Translation of the Laplace integral gives their exact
exponential multiplier.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex
open scoped NNReal ENNReal

namespace GaloisForLFunctions.HTGeometry
open _root_.HTGeometry

local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

/-- Causal translation multiplies the Laplace transform by its delay factor. -/
theorem laplaceRay_rightShiftFun (h : ℝ≥0) (f : ℝ → ℂ) (w : ℂ) :
    laplaceRay (rightShiftFun h f) w =
      Complex.exp (-w * (h : ℂ)) * laplaceRay f w := by
  have hi : (∫ x in Ioi (0 : ℝ), rightShiftFun h f x * expRay w x) =
      ∫ x in Ioi (h : ℝ), f (x - h) * expRay w x := by
    simp only [rightShiftFun, ← Set.indicator_mul_left]
    rw [integral_indicator measurableSet_Ioi, restrict_Ioi_zero_restrict_Ioi h.coe_nonneg]
  change (∫ x in Ioi (0 : ℝ), rightShiftFun h f x * expRay w x) = _
  rw [hi]
  have he := (measurePreserving_add_right_Ioi (h : ℝ)).integral_comp
    (measurableEmbedding_addRight (h : ℝ)) (fun x => f (x - h) * expRay w x)
  rw [← he]
  simp only [add_sub_cancel_right]
  rw [laplaceRay, ← integral_const_mul]
  apply integral_congr_ae
  refine Eventually.of_forall fun x => ?_
  simp only [expRay, ofReal_add, mul_add, neg_add_rev, Complex.exp_add, neg_mul]
  ring

/-- The actual L² shift has the same literal Laplace multiplier. -/
theorem laplaceRay_burnolRightShift (h : ℝ≥0) (f : BurnolHalfLineL2) (w : ℂ) :
    laplaceRay (burnolRightShift h f) w =
      Complex.exp (-w * (h : ℂ)) * laplaceRay f w := by
  rw [← laplaceRay_rightShiftFun]
  unfold laplaceRay
  apply integral_congr_ae
  filter_upwards [burnolRightShift_coeFn h f] with x hx
  rw [hx]

/-- The causal shifts form a semigroup. -/
theorem burnolRightShift_add (h k : ℝ≥0) (f : BurnolHalfLineL2) :
    burnolRightShift (h + k) f = burnolRightShift h (burnolRightShift k f) := by
  apply Lp.ext
  filter_upwards [burnolRightShift_coeFn (h + k) f,
    burnolRightShift_coeFn h (burnolRightShift k f),
    rightShiftFun_congr h.coe_nonneg (burnolRightShift_coeFn k f)] with x hsum hh hk
  rw [hsum, hh, hk]
  simp only [rightShiftFun, NNReal.coe_add]
  by_cases hx : (h : ℝ) + k < x
  · have hhx : (h : ℝ) < x := lt_of_le_of_lt (le_add_of_nonneg_right k.coe_nonneg) hx
    have hkx : (k : ℝ) < x - h := by linarith only [hx]
    rw [indicator_of_mem (show x ∈ Ioi ((h : ℝ) + k) from hx),
      indicator_of_mem (show x ∈ Ioi (h : ℝ) from hhx),
      indicator_of_mem (show x - h ∈ Ioi (k : ℝ) from hkx)]
    congr 1
    ring
  · rw [indicator_of_notMem (show x ∉ Ioi ((h : ℝ) + k) from hx)]
    by_cases hhx : (h : ℝ) < x
    · have hkx : ¬ (k : ℝ) < x - h := by linarith only [hx]
      rw [indicator_of_mem (show x ∈ Ioi (h : ℝ) from hhx),
        indicator_of_notMem (show x - h ∉ Ioi (k : ℝ) from hkx)]
    · rw [indicator_of_notMem (show x ∉ Ioi (h : ℝ) from hhx)]

@[simp] theorem burnolRightShift_zero (f : BurnolHalfLineL2) :
    burnolRightShift 0 f = f := by
  apply Lp.ext
  filter_upwards [burnolRightShift_coeFn 0 f, ae_restrict_mem measurableSet_Ioi] with x hx hpos
  simpa only [rightShiftFun, NNReal.coe_zero, indicator_of_mem hpos, sub_zero] using hx

/-- Zero extension and restriction transfer norm continuity from whole-line translation. -/
theorem continuous_burnolRightShift (f : BurnolHalfLineL2) :
    Continuous (fun h : ℝ≥0 => burnolRightShift h f) := by
  let g : ℝ → ℂ := (Ioi (0 : ℝ)).indicator (f : ℝ → ℂ)
  have hg : MemLp g 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_Ioi).mpr (Lp.memLp f)
  let G := hg.toLp g
  let R := LpToLpRestrictCLM ℝ ℂ ℂ volume 2 (Ioi 0)
  let H : ℝ≥0 → Lp ℂ 2 (volume : Measure ℝ) :=
    fun h => DomAddAct.mk (-(h : ℝ)) +ᵥ G
  have hH : Continuous H := by
    have hmk : Continuous (fun h : ℝ≥0 => (DomAddAct.mk (-(h : ℝ)) : DomAddAct ℝ)) :=
      DomAddAct.continuous_mk.comp continuous_subtype_val.neg
    exact continuous_vadd.comp (hmk.prodMk continuous_const)
  have hHae (h : ℝ≥0) : (H h : ℝ → ℂ) =ᵐ[volume] fun x => (G : ℝ → ℂ) (x - h) := by
    have hh := DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk (-(h : ℝ))) G
    refine hh.trans ?_
    filter_upwards with x
    have hv : (DomAddAct.mk.symm (DomAddAct.mk (-(h : ℝ))) : ℝ) +ᵥ x = x - h := by
      simp only [Equiv.symm_apply_apply, vadd_eq_add]
      ring
    rw [hv]
  have he (h : ℝ≥0) : burnolRightShift h f = R (H h) := by
    apply Lp.ext
    have hG := (measurePreserving_sub_right volume (h : ℝ)).quasiMeasurePreserving.ae_eq_comp
      (MemLp.coeFn_toLp hg)
    filter_upwards [burnolRightShift_coeFn h f,
      LpToLpRestrictCLM_coeFn ℂ (Ioi (0 : ℝ)) (H h),
      ae_restrict_of_ae (hHae h),
      ae_restrict_of_ae hG] with x h1 h2 h3 h4
    change _ = (R (H h) : ℝ → ℂ) x
    rw [h1, h2, h3]
    change (G : ℝ → ℂ) (x - h) = g (x - h) at h4
    rw [h4]
    dsimp only [rightShiftFun, g]
    by_cases hx : (h : ℝ) < x
    · rw [indicator_of_mem (show x ∈ Ioi (h : ℝ) from hx),
        indicator_of_mem (show x - h ∈ Ioi (0 : ℝ) from sub_pos.mpr hx)]
    · rw [indicator_of_notMem (show x ∉ Ioi (h : ℝ) from hx),
        indicator_of_notMem (show x - h ∉ Ioi (0 : ℝ) from fun hn => hx (sub_pos.mp hn))]
  have hc := R.continuous.comp hH
  exact hc.congr (fun h => (he h).symm)

#print axioms continuous_burnolRightShift
#print axioms laplaceRay_burnolRightShift

end GaloisForLFunctions.HTGeometry
