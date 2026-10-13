import GaloisForLFunctions.RHTower.PaperWoldCompositeObservation
import GaloisForLFunctions.HTGeometry.PaperCoordinateCompression

/-! # Native finite observations of the composite exponent defect

The input prefix consists of the original coordinates through `M`. Strict
triangularity bounds its complete output support, so row damping supplies a
uniform norm bound without replacing the arithmetic operator by a model.
-/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped NNReal ENNReal

theorem paperWoldCompositeDampingWeight_antitone (r : ℝ≥0) :
    Antitone (paperWoldCompositeDampingWeight r) := by
  intro n j hnj
  apply Real.rpow_le_rpow_of_nonpos (by positivity)
    (by exact_mod_cast (show 2 * n + 3 ≤ 2 * j + 3 by omega))
    (neg_nonpos.mpr r.property)

theorem paperWoldCompositeDampingWeight_exp (r : ℝ≥0) (n : ℕ) :
    paperWoldCompositeDampingWeight r n =
      Real.exp (-((r : ℝ) * Real.log (2 * (n : ℝ) + 3))) := by
  rw [paperWoldCompositeDampingWeight, Real.rpow_def_of_pos (by positivity)]
  congr 1
  ring

theorem paperWoldCompositeDampingDefect_norm (r : ℝ≥0) (n : ℕ) :
    ‖(1 : ℂ) - (paperWoldCompositeDampingWeight r n : ℂ)‖ =
      1 - paperWoldCompositeDampingWeight r n := by
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (paperWoldCompositeDampingWeight_le_one r n))]

def paperWoldCompositePrefixDefect (t : {t : ℝ // t ≤ 1 / 2}) (M : ℕ) :
    PaperWoldHistory →L[ℂ] PaperWoldHistory :=
  (paperWoldCriticalCompositeOperator - paperWoldCompositeOperator t) ∘L
    paperCoordinateProjection (M + 1)

/-- Exponent distance times the logarithmic size of the original input prefix. -/
def paperWoldCompositeObservationClock (t : {t : ℝ // t ≤ 1 / 2}) (M : ℕ) : ℝ :=
  (paperWoldCompositeDampingTime t : ℝ) * Real.log ((M : ℝ) + 1)

theorem paperWoldCompositeObservationClock_nonneg (t : {t : ℝ // t ≤ 1 / 2}) (M : ℕ) :
    0 ≤ paperWoldCompositeObservationClock t M :=
  mul_nonneg (paperWoldCompositeDampingTime t).property
    (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) M]))

theorem paperWoldCompositePrefixDefect_factor (t : {t : ℝ // t ≤ 1 / 2}) (M : ℕ) :
    paperWoldCompositePrefixDefect t M =
      (1 - paperWoldCompositeDamping (paperWoldCompositeDampingTime t)) ∘L
        (paperWoldCriticalCompositeOperator ∘L paperCoordinateProjection (M + 1)) := by
  simp only [paperWoldCompositePrefixDefect, paperWoldCompositeOperator_factor,
    ContinuousLinearMap.sub_comp, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp,
    ContinuousLinearMap.comp_assoc]

theorem paperWoldCompositePrefixDefect_apply (t : {t : ℝ // t ≤ 1 / 2}) (M : ℕ)
    (f : PaperWoldHistory) (n : ℕ) :
    paperWoldCompositePrefixDefect t M f n =
      ((1 : ℂ) - paperWoldCompositeDampingWeight (paperWoldCompositeDampingTime t) n) *
        paperWoldCriticalCompositeOperator (paperCoordinateProjection (M + 1) f) n := by
  rw [paperWoldCompositePrefixDefect_factor]
  simp only [ContinuousLinearMap.comp_apply, sub_apply, lp.coeFn_sub, Pi.sub_apply,
    ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply, paperWoldCompositeDamping_apply]
  ring

private theorem projection_single (M j : ℕ) :
    paperCoordinateProjection (M + 1) (lp.single 2 j (1 : ℂ)) =
      if j ≤ M then lp.single 2 j (1 : ℂ) else 0 := by
  ext k
  by_cases hkj : k = j
  · subst k
    by_cases hj : j ≤ M <;> simp [paperCoordinateProjection_coordinate, hj]
  · by_cases hj : j ≤ M <;>
      simp [paperCoordinateProjection_coordinate, lp.single_apply, hkj, hj]

theorem paperWoldCompositePrefixDefect_single (t : {t : ℝ // t ≤ 1 / 2}) (M n j : ℕ) :
    paperWoldCompositePrefixDefect t M (lp.single 2 j (1 : ℂ)) n =
      if j ≤ M then
        ((1 : ℂ) - paperWoldCompositeDampingWeight (paperWoldCompositeDampingTime t) n) *
          paperWoldCompositeEntry (1 / 2) n j else 0 := by
  rw [paperWoldCompositePrefixDefect_apply, projection_single]
  split_ifs <;> simp [paperWoldCriticalCompositeOperator_single]

private theorem critical_prefix_zero (M n : ℕ) (hn : M ≤ n) (f : PaperWoldHistory) :
    paperWoldCriticalCompositeOperator (paperCoordinateProjection (M + 1) f) n = 0 := by
  rw [paperWoldCriticalCompositeOperator_apply]
  trans ∑' _j : ℕ, (0 : ℂ)
  · apply tsum_congr
    intro j
    rw [paperCoordinateProjection_coordinate]
    by_cases hj : j < M + 1
    · rw [if_pos hj, paperWoldCompositeEntry_critical_formula, if_neg (by omega : ¬ n < j), zero_mul]
    · rw [if_neg hj, mul_zero]
  · exact tsum_zero

theorem paperWoldCompositePrefixDefect_zero_prefix (t : {t : ℝ // t ≤ 1 / 2}) :
    paperWoldCompositePrefixDefect t 0 = 0 := by
  ext f n
  rw [paperWoldCompositePrefixDefect_apply, critical_prefix_zero 0 n (Nat.zero_le n), mul_zero]
  rfl

theorem paperWoldCompositePrefixDefect_norm_upper (t : {t : ℝ // t ≤ 1 / 2}) (M : ℕ) :
    ‖paperWoldCompositePrefixDefect t M‖ ≤
      5 * (1 - paperWoldCompositeDampingWeight (paperWoldCompositeDampingTime t) M) := by
  let r := paperWoldCompositeDampingTime t
  let c := 1 - paperWoldCompositeDampingWeight r M
  have hc : 0 ≤ c := sub_nonneg.mpr (paperWoldCompositeDampingWeight_le_one r M)
  let w : ℕ → ℂ := fun n => if n ≤ M then 1 - (paperWoldCompositeDampingWeight r n : ℂ) else 0
  have hw : ∀ n, ‖w n‖ ≤ c := by
    intro n
    dsimp [w]
    split_ifs with hn
    · rw [paperWoldCompositeDampingDefect_norm]
      exact sub_le_sub_left (paperWoldCompositeDampingWeight_antitone r hn) 1
    · simpa using hc
  let D := lpDiagonalCLM w hc hw
  let B := paperWoldCriticalCompositeOperator ∘L paperCoordinateProjection (M + 1)
  have heq : paperWoldCompositePrefixDefect t M = D ∘L B := by
    ext f n
    simp only [paperWoldCompositePrefixDefect_apply, ContinuousLinearMap.comp_apply,
      D, B, lpDiagonalCLM_apply, w, r]
    by_cases hn : n ≤ M
    · rw [if_pos hn]
    · rw [if_neg hn, critical_prefix_zero M n (by omega), mul_zero, mul_zero]
  have hB : ‖B‖ ≤ 5 := by
    calc
      ‖B‖ ≤ ‖paperWoldCriticalCompositeOperator‖ *
          ‖(paperCoordinateProjection (M + 1) : PaperWoldHistory →L[ℂ] PaperWoldHistory)‖ :=
        paperWoldCriticalCompositeOperator.opNorm_comp_le _
      _ ≤ 5 * 1 := mul_le_mul paperWoldCriticalCompositeOperator_norm_le
        (norm_paperCoordinateProjection_le _) (norm_nonneg _) (by norm_num)
      _ = 5 := mul_one _
  rw [heq]
  exact (D.opNorm_comp_le B).trans (by
    simpa only [mul_comm] using mul_le_mul (norm_lpDiagonalCLM_le w hc hw) hB (norm_nonneg B) hc)

theorem paperWoldCompositePrefixDefect_compact (t : {t : ℝ // t ≤ 1 / 2}) (M : ℕ) :
    IsCompactOperator (paperWoldCompositePrefixDefect t M) := by
  simpa only [paperWoldCompositePrefixDefect, ContinuousLinearMap.coe_comp] using
    (isCompactOperator_paperCoordinateProjection (E := ℂ) (M + 1)).clm_comp
      (paperWoldCriticalCompositeOperator - paperWoldCompositeOperator t)

theorem paperWoldCompositePrefixDefect_traceCost (t : {t : ℝ // t ≤ 1 / 2}) (M : ℕ) :
    compactOperatorTraceCost PaperWoldHistory (paperWoldCompositePrefixDefect t M) = 0 :=
  (compactOperatorTraceCost_eq_zero_iff _).mpr (paperWoldCompositePrefixDefect_compact t M)

end
end RHTower
