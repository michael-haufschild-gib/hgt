import GaloisForLFunctions.RHTower.JointAncestryLogBudgetProducer
import GaloisForLFunctions.RHTower.PrimeLagLandauWeights

/-! # An unconditional summable budget for signed JAS sectors

The distance of each Xi zero from the edges of the critical strip controls the
level-one sector norm. Its reciprocal grows at most logarithmically in height,
so the native zero weights can pay this budget without a positivity assumption.
-/

namespace RHTower

noncomputable section

def jasZeroStripWidth (q : XiZeroCopy) : ℝ :=
  1 / 2 - |(q.1 : ℂ).re - 1 / 2|

theorem jasZeroStripWidth_pos (q : XiZeroCopy) : 0 < jasZeroStripWidth q := by
  have h0 := xiZeroCopy_re_pos q
  have h1 := xiZeroCopy_re_lt_one q
  have h : |(q.1 : ℂ).re - 1 / 2| < 1 / 2 := by
    rw [abs_lt]
    constructor <;> linarith
  unfold jasZeroStripWidth
  linarith

theorem jasZeroStripWidth_le_re (q : XiZeroCopy) :
    jasZeroStripWidth q ≤ (q.1 : ℂ).re := by
  unfold jasZeroStripWidth
  linarith [neg_le_abs ((q.1 : ℂ).re - 1 / 2)]

theorem jasZeroStripWidth_le_one_sub_re (q : XiZeroCopy) :
    jasZeroStripWidth q ≤ 1 - (q.1 : ℂ).re := by
  unfold jasZeroStripWidth
  linarith [le_abs_self ((q.1 : ℂ).re - 1 / 2)]

def jasSectorNormBudget (q : XiZeroCopy) : ℝ :=
  1 + (2 * jasZeroStripWidth q)⁻¹

theorem jasSectorNormBudget_pos (q : XiZeroCopy) : 0 < jasSectorNormBudget q := by
  have := jasZeroStripWidth_pos q
  unfold jasSectorNormBudget
  positivity

theorem exists_jasSectorNormBudget_le_log :
    ∃ C : ℝ, 0 < C ∧ ∀ q : XiZeroCopy,
      jasSectorNormBudget q ≤ C * (1 + Real.log (2 + |zeroOrdinate q|)) := by
  obtain ⟨η, hη, hlow⟩ := exists_low_zero_width
  let C : ℝ := 51 + (2 * η)⁻¹
  have hinv : 0 ≤ (2 * η)⁻¹ := by positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun q => ?_⟩
  have hw := jasZeroStripWidth_pos q
  have hlog : 0 ≤ Real.log (2 + |zeroOrdinate q|) :=
    Real.log_nonneg (by linarith [abs_nonneg (zeroOrdinate q)])
  by_cases hq : |(q.1 : ℂ).im| ≤ 4
  · have hηw : η ≤ jasZeroStripWidth q := by
      have := hlow q hq
      dsimp [jasZeroStripWidth]
      linarith
    have hi : (2 * jasZeroStripWidth q)⁻¹ ≤ (2 * η)⁻¹ := by
      rw [← one_div, ← one_div]
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    have hbudget : jasSectorNormBudget q ≤ C := by
      dsimp [jasSectorNormBudget, C]
      linarith
    exact hbudget.trans (by nlinarith)
  · have hfour : 4 ≤ |(q.1 : ℂ).im| := le_of_lt (lt_of_not_ge hq)
    have hL : 0 < Real.log |(q.1 : ℂ).im| := Real.log_pos (by linarith)
    have hwidth : 1 / 100 / Real.log |(q.1 : ℂ).im| ≤ jasZeroStripWidth q := by
      have := abs_re_sub_half_le_of_four_le q hfour
      dsimp [jasZeroStripWidth]
      linarith
    have hi : (2 * jasZeroStripWidth q)⁻¹ ≤ 50 * Real.log |(q.1 : ℂ).im| := by
      rw [← one_div, div_le_iff₀ (by positivity)]
      have := (div_le_iff₀ hL).1 hwidth
      nlinarith
    have hmono : Real.log |(q.1 : ℂ).im| ≤ Real.log (2 + |zeroOrdinate q|) := by
      apply Real.log_le_log (by linarith)
      dsimp [zeroOrdinate]
      linarith
    dsimp [jasSectorNormBudget, C]
    nlinarith [mul_nonneg hinv hlog]

theorem summable_lagWeight_mul_jasSectorNormBudget :
    Summable fun q : XiZeroCopy => ‖lagWeight q‖ * jasSectorNormBudget q := by
  obtain ⟨C, _hC, hbound⟩ := exists_jasSectorNormBudget_le_log
  apply Summable.of_nonneg_of_le
    (fun q => mul_nonneg (norm_nonneg _) (jasSectorNormBudget_pos q).le)
    (f := fun q => C * (‖lagWeight q‖ + ‖lagWeight q‖ * Real.log (2 + |zeroOrdinate q|)))
  · intro q
    calc ‖lagWeight q‖ * jasSectorNormBudget q
        ≤ ‖lagWeight q‖ * (C * (1 + Real.log (2 + |zeroOrdinate q|))) :=
          mul_le_mul_of_nonneg_left (hbound q) (norm_nonneg _)
      _ = _ := by ring
  · exact (summable_norm_lagWeight.add summable_lagWeight_mul_log).mul_left C

end

end RHTower
