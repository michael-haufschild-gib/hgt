import GaloisForLFunctions.RHTower.RouteBChiDecay
import GaloisForLFunctions.RHTower.SmoothAFEZetaChiPowerBound

/-!
# A power bound for the archimedean factor on a fixed left line

On the line `Re s = 1/2 − a` with `0 < a < 1/2` the archimedean factor grows like `|t|^a`.  Away
from the origin this is the left-strip envelope `norm_zetaChi_le_left_line`; on a bounded segment
it is continuity and compactness.

This is the growth input for the large-scale decay of the exact dual Gaussian weight: shifting the
dual contour to `Re w = a > 0` costs `Y^{-a}` from the Mellin factor and gains at most `|τ|^a` from
the shifted archimedean ratio.
-/

open Complex

noncomputable section

namespace RHTower

theorem continuous_norm_zetaChi_left_line {a : ℝ} (ha : 0 < a) (hahalf : a < 1 / 2) :
    Continuous fun t : ℝ => ‖zetaChi (((1 / 2 - a : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
  apply Continuous.norm
  rw [continuous_iff_continuousAt]
  intro t
  apply (zetaChi_analyticAt ?_).continuousAt.comp
  · fun_prop
  · apply Complex.Gammaℝ_ne_zero_of_re_pos
    simp
    linarith

theorem exists_norm_zetaChi_left_line_compact_bound {a : ℝ} (ha : 0 < a) (hahalf : a < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |t| ≤ 1 →
      ‖zetaChi (((1 / 2 - a : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ C := by
  set f : ℝ → ℝ := fun t => ‖zetaChi (((1 / 2 - a : ℝ) : ℂ) + (t : ℂ) * I)‖ with hf
  have hcont : Continuous f := continuous_norm_zetaChi_left_line ha hahalf
  obtain ⟨t₀, ht₀, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn (⟨0, by norm_num⟩ : (Set.Icc (-1 : ℝ) 1).Nonempty)
      hcont.continuousOn
  refine ⟨f t₀, norm_nonneg _, fun t ht => ?_⟩
  exact hmax (Set.mem_Icc.mpr ⟨by cases abs_le.mp ht with | intro h1 h2 => linarith,
    by cases abs_le.mp ht with | intro h1 h2 => linarith⟩)

/-- **Left-line power bound.**  For `0 < a < 1/2` the archimedean factor on `Re s = 1/2 − a` is at
most a constant times `(max 1 |t|)^a`. -/
theorem exists_norm_zetaChi_fixed_left_line_le_rpow {a : ℝ} (ha : 0 < a) (hahalf : a < 1 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ,
      ‖zetaChi (((1 / 2 - a : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ K * (max 1 |t|) ^ a := by
  obtain ⟨C, hC, hcompact⟩ := exists_norm_zetaChi_left_line_compact_bound ha hahalf
  refine ⟨max C (Real.exp (a * (4 + Real.pi))), le_trans hC (le_max_left _ _), fun t => ?_⟩
  by_cases ht : |t| ≤ 1
  · have hmax1 : max 1 |t| = 1 := max_eq_left ht
    rw [hmax1, Real.one_rpow, mul_one]
    exact le_trans (hcompact t ht) (le_max_left _ _)
  · rw [not_le] at ht
    have htpos : (0 : ℝ) < |t| := by linarith
    have hmaxabs : max 1 |t| = |t| := max_eq_right ht.le
    rw [norm_zetaChi_real_add_im_eq_abs, hmaxabs]
    have hleft := norm_zetaChi_le_left_line (σ := 1 / 2 - a) (t := |t|)
      (by linarith) (by linarith) htpos
    refine le_trans hleft ?_
    have hbracket : (1 / 2 : ℝ) * Real.log ((1 / 2 : ℝ) ^ 2 + (|t| / 2) ^ 2)
        + (1 / (|t| / 2) ^ 2 + Real.pi / (2 * (|t| / 2))) - Real.log Real.pi
        ≤ Real.log |t| + (4 + Real.pi) := by
      have hlog : (1 / 2 : ℝ) * Real.log ((1 / 2 : ℝ) ^ 2 + (|t| / 2) ^ 2) ≤ Real.log |t| := by
        have hle : ((1 / 2 : ℝ) ^ 2 + (|t| / 2) ^ 2) ≤ |t| ^ 2 := by nlinarith
        have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ 2 + (|t| / 2) ^ 2 := by positivity
        have := Real.log_le_log hpos hle
        rw [Real.log_pow] at this
        push_cast at this
        linarith
      have hinv : (1 : ℝ) / (|t| / 2) ^ 2 ≤ 4 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      have hpi : Real.pi / (2 * (|t| / 2)) ≤ Real.pi := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [Real.pi_pos]
      have hlogpi : (0 : ℝ) ≤ Real.log Real.pi :=
        Real.log_nonneg (by linarith [Real.pi_gt_three])
      linarith
    have hmul : a * ((1 / 2 : ℝ) * Real.log ((1 / 2 : ℝ) ^ 2 + (|t| / 2) ^ 2)
        + (1 / (|t| / 2) ^ 2 + Real.pi / (2 * (|t| / 2))) - Real.log Real.pi)
        ≤ a * (Real.log |t| + (4 + Real.pi)) :=
      mul_le_mul_of_nonneg_left hbracket ha.le
    have hexp : Real.exp ((1 / 2 - (1 / 2 - a)) *
        ((1 / 2 : ℝ) * Real.log ((1 / 2 : ℝ) ^ 2 + (|t| / 2) ^ 2)
          + (1 / (|t| / 2) ^ 2 + Real.pi / (2 * (|t| / 2))) - Real.log Real.pi))
        ≤ Real.exp (a * (Real.log |t| + (4 + Real.pi))) := by
      refine Real.exp_le_exp.mpr ?_
      have hcoef : (1 / 2 - (1 / 2 - a)) = a := by ring
      rw [hcoef]
      exact hmul
    refine le_trans hexp ?_
    have hsplit : Real.exp (a * (Real.log |t| + (4 + Real.pi)))
        = Real.exp (Real.log |t| * a) * Real.exp (a * (4 + Real.pi)) := by
      rw [← Real.exp_add]
      ring_nf
    rw [hsplit, ← Real.rpow_def_of_pos htpos]
    have hrp : (0 : ℝ) ≤ |t| ^ a := Real.rpow_nonneg (abs_nonneg t) a
    calc |t| ^ a * Real.exp (a * (4 + Real.pi))
        ≤ |t| ^ a * max C (Real.exp (a * (4 + Real.pi))) := by
          exact mul_le_mul_of_nonneg_left (le_max_right _ _) hrp
      _ = max C (Real.exp (a * (4 + Real.pi))) * |t| ^ a := by ring

end RHTower
