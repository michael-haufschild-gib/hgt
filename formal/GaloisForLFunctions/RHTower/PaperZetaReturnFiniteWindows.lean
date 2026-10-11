import GaloisForLFunctions.RHTower.PaperZetaReturnCoefficients

/-! # Finite-window positivity before asymptotic recurrence

Every admissible disc and positive tolerance has positive return mass on every
positive window. This local fact makes no asymptotic recurrence assertion.
-/

namespace RHTower
noncomputable section
open Complex Metric Set MeasureTheory

/-- An explicit admissible disc witnesses that the geometric domain is nonempty. -/
def paperZetaReturnReferenceDisc : PaperZetaReturnDisc where
  center := 3 / 4
  radius := 1 / 8
  radius_pos := by norm_num
  strip := by
    intro s hs
    have h := abs_le.mp ((abs_re_le_norm (s - (3 / 4 : ℂ))).trans
      (mem_closedBall_iff_norm.mp hs))
    norm_num at h
    constructor <;> linarith [h.1, h.2]

theorem paperZetaReturnTimes_zero (D : PaperZetaReturnDisc) (ε : {e : ℝ // 0 < e}) :
    (0 : ℝ) ∈ paperZetaReturnTimes D ε := by
  intro s hs
  simpa using ε.property

theorem paperZetaReturnTimes_window_pos (D : PaperZetaReturnDisc)
    (ε T : {t : ℝ // 0 < t}) :
    0 < volume (paperZetaReturnTimes D ε ∩ Icc 0 T.val) := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp (paperZetaReturnTimes_isOpen D ε) 0
    (paperZetaReturnTimes_zero D ε)
  let a := min r T.val / 2
  have ha : 0 < a := div_pos (lt_min hr T.property) (by norm_num)
  have har : a < r := by
    have := min_le_left r T.val
    dsimp [a]
    linarith
  have haT : a ≤ T.val := by
    have := min_le_right r T.val
    dsimp [a]
    linarith [T.property]
  have hinc : Ioc (0 : ℝ) a ⊆ paperZetaReturnTimes D ε ∩ Icc 0 T.val := by
    intro τ hτ
    refine ⟨hsub ?_, hτ.1.le, hτ.2.trans haT⟩
    simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hτ.1] using
      hτ.2.trans_lt har
  have hpos : 0 < volume (Ioc (0 : ℝ) a) := by
    simpa only [Real.volume_Ioc, sub_zero, ENNReal.ofReal_pos] using ha
  exact hpos.trans_le (measure_mono hinc)

theorem paperZetaReturnDensity_pos (D : PaperZetaReturnDisc)
    (ε T : {t : ℝ // 0 < t}) : 0 < paperZetaReturnDensity D ε T :=
  div_pos (ENNReal.toReal_pos (ne_of_gt (paperZetaReturnTimes_window_pos D ε T))
    (paperZetaReturnTimes_window_ne_top D ε T)) T.property

theorem paperZetaReturnCoeff_zero_norm_pos (D : PaperZetaReturnDisc)
    (ε T : {t : ℝ // 0 < t}) : 0 < ‖paperZetaReturnCoeff D ε T 0‖ := by
  rw [paperZetaReturnCoeff_zero_norm]
  exact paperZetaReturnDensity_pos D ε T

end
end RHTower
