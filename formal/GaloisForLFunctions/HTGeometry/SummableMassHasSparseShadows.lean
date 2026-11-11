import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Summable mass has sparse shadows

Atoms with summable nonnegative weights cannot cover a positive proportion of a
long interval by bounded-length shadows if every contributing atom costs at least
the reciprocal of the interval length. The proof uses dominated convergence on
the truncated weights `min (1/T) w` and countable subadditivity.
-/

open Filter Topology MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Truncating every summable weight at a level tending to zero loses all mass. -/
theorem tendsto_tsum_min_inv_of_summable {ι : Type*} {w : ι → ℝ}
    (hw0 : ∀ i, 0 ≤ w i) (hw : Summable w) :
    Tendsto (fun T : ℝ => ∑' i, min T⁻¹ (w i)) atTop (𝓝 0) := by
  have hi : Tendsto (fun T : ℝ => T⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have h := tendsto_tsum_of_dominated_convergence
    (f := fun T : ℝ => fun i => min T⁻¹ (w i)) (g := fun _ : ι => (0 : ℝ))
    (bound := w) hw (fun i => by
      simpa only [min_eq_left (hw0 i)] using hi.min
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => w i) atTop (𝓝 (w i))))
    (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT i
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (inv_nonneg.mpr hT) (hw0 i))]
      exact min_le_right _ _)
  simpa only [tsum_zero] using h

/-- A union of bounded-measure sets selected only by atoms of weight at least
`1/T` has measure `o(T)`. No separation between the sets is required. -/
theorem eventually_measure_heavy_union_le {ι X : Type*} [Countable ι]
    [MeasurableSpace X] (μ : Measure X) {w : ι → ℝ}
    (hw0 : ∀ i, 0 ≤ w i) (hw : Summable w) (S : ι → Set X)
    {D : ℝ} (hD : 0 ≤ D) (hS : ∀ i, μ (S i) ≤ ENNReal.ofReal D)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop,
      μ (⋃ i, if 1 ≤ T * w i then S i else ∅) ≤ ENNReal.ofReal (ε * T) := by
  classical
  have hlim : Tendsto (fun T : ℝ => D * ∑' i, min T⁻¹ (w i)) atTop (𝓝 0) := by
    simpa using (tendsto_tsum_min_inv_of_summable hw0 hw).const_mul D
  filter_upwards [hlim.eventually (gt_mem_nhds hε), eventually_gt_atTop (0 : ℝ)]
    with T hTε hT
  have hmin0 : ∀ i, 0 ≤ min T⁻¹ (w i) := fun i =>
    le_min (inv_nonneg.mpr hT.le) (hw0 i)
  have hsum : Summable (fun i => min T⁻¹ (w i)) :=
    Summable.of_nonneg_of_le hmin0 (fun i => min_le_right _ _) hw
  have hbound : ∀ i, μ (if 1 ≤ T * w i then S i else ∅) ≤
      ENNReal.ofReal (D * T * min T⁻¹ (w i)) := by
    intro i
    split_ifs with hi
    · have hwi : T⁻¹ ≤ w i := by
        rw [inv_eq_one_div, div_le_iff₀ hT]
        simpa only [mul_comm] using hi
      rw [min_eq_left hwi, mul_assoc, mul_inv_cancel₀ hT.ne', mul_one]
      exact hS i
    · simp only [measure_empty]
      exact bot_le
  calc μ (⋃ i, if 1 ≤ T * w i then S i else ∅)
      ≤ ∑' i, μ (if 1 ≤ T * w i then S i else ∅) := measure_iUnion_le _
    _ ≤ ∑' i, ENNReal.ofReal (D * T * min T⁻¹ (w i)) := ENNReal.tsum_le_tsum hbound
    _ = ENNReal.ofReal (D * T * ∑' i, min T⁻¹ (w i)) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => mul_nonneg (mul_nonneg hD hT.le) (hmin0 i))
        (hsum.mul_left (D * T)), tsum_mul_left]
    _ ≤ ENNReal.ofReal (ε * T) := ENNReal.ofReal_le_ofReal (by
      calc D * T * ∑' i, min T⁻¹ (w i) = (D * ∑' i, min T⁻¹ (w i)) * T := by ring
        _ ≤ ε * T := mul_le_mul_of_nonneg_right hTε.le hT.le)

/-- Points of summable mass satisfying `b ≤ |p| w(p)` cast a density-zero set of
fixed-radius vertical shadows. -/
theorem eventually_volume_weighted_vertical_shadows_le {ι : Type*} [Countable ι]
    (p : ι → ℂ) {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw : Summable w)
    (c : ℂ) {r b : ℝ} (hr : 0 < r) (hb : 0 < b) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop,
      volume ({t : ℝ | ∃ i, ‖p i - (c + t * Complex.I)‖ < r ∧ b ≤ ‖p i‖ * w i} ∩ Icc 0 T)
        ≤ ENNReal.ofReal (ε * T) := by
  classical
  let S : ι → Set ℝ := fun i => Ioo ((p i).im - c.im - r) ((p i).im - c.im + r)
  have hS : ∀ i, volume (S i) ≤ ENNReal.ofReal (2 * r) := by
    intro i
    simp only [S, Real.volume_Ioo]
    apply ENNReal.ofReal_le_ofReal
    linarith
  have hheavy := eventually_measure_heavy_union_le volume
    (w := fun i => 2 * w i / b)
    (fun i => div_nonneg (mul_nonneg (by norm_num) (hw0 i)) hb.le)
    ((hw.mul_left 2).div_const b) S (show 0 ≤ 2 * r by positivity) hS (half_pos hε)
  filter_upwards [hheavy, eventually_ge_atTop (‖c‖ + r), eventually_gt_atTop (0 : ℝ)]
    with T hT hTC hT0
  have hsub : {t : ℝ | ∃ i, ‖p i - (c + t * Complex.I)‖ < r ∧ b ≤ ‖p i‖ * w i} ∩ Icc 0 T
      ⊆ ⋃ i, if 1 ≤ T * (2 * w i / b) then S i else ∅ := by
    rintro t ⟨⟨i, hdist, hweight⟩, ht⟩
    have hpi : ‖p i‖ ≤ 2 * T := by
      calc ‖p i‖ ≤ ‖p i - (c + t * Complex.I)‖ + ‖c + t * Complex.I‖ :=
          norm_le_norm_sub_add _ _
        _ ≤ r + (‖c‖ + t) := by
          refine add_le_add hdist.le ((norm_add_le _ _).trans ?_)
          simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg ht.1, le_refl]
        _ ≤ 2 * T := by linarith [ht.2]
    have hsel : 1 ≤ T * (2 * w i / b) := by
      have hbound := hweight.trans (mul_le_mul_of_nonneg_right hpi (hw0 i))
      rw [← mul_div_assoc, le_div_iff₀ hb]
      nlinarith only [hbound]
    refine mem_iUnion.mpr ⟨i, ?_⟩
    rw [if_pos hsel]
    have him := (Complex.abs_im_le_norm (p i - (c + t * Complex.I))).trans_lt hdist
    have him' : |(p i).im - c.im - t| < r := by
      simpa only [Complex.sub_im, Complex.add_im, Complex.mul_I_im, Complex.ofReal_re,
        ← sub_sub] using him
    exact ⟨by linarith [(abs_lt.mp him').2], by linarith [(abs_lt.mp him').1]⟩
  exact (measure_mono hsub).trans (hT.trans (ENNReal.ofReal_le_ofReal (by
    nlinarith [mul_nonneg hε.le hT0.le])))

end GaloisForLFunctions.HTGeometry
