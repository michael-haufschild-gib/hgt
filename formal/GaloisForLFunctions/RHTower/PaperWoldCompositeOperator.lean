import GaloisForLFunctions.RHTower.PaperHardyDominatedOperator
import GaloisForLFunctions.RHTower.PaperWoldCompactDomain

/-! # A bounded critical operator retaining the literal even-composite matrix

At the half power, the complete composite matrix is dominated by the native
Hardy tail. This constructs its action on all of the original sequence space.
-/

namespace RHTower
noncomputable section
open GaloisForLFunctions GaloisForLFunctions.HTGeometry

theorem paperWold_even_composite_increment_upper (n : ℕ) :
    -xiHeatCassiniWoldNatIncrement (2 * n + 2) ≤ 1 / (2 * (n : ℝ) + 3) := by
  rw [paperWold_even_composite_increment, neg_neg]
  have h := log_succ_sub_log_le (j := 2 * n + 3) (by omega)
  push_cast at h
  simpa only [show 2 * (n : ℝ) + 3 + 1 = 2 * n + 4 by ring] using h

theorem paperWoldCompositeEntry_critical_formula (n j : ℕ) :
    paperWoldCompositeEntry (1 / 2) n j = if n < j then
      (((2 * (n : ℝ) + 3) * (-xiHeatCassiniWoldNatIncrement (2 * n + 2)) *
        (-xiHeatCassiniWoldNatIncrement (2 * j + 2)) : ℝ) : ℂ) else 0 := by
  unfold paperWoldCompositeEntry paperWoldDirectedKernel
  by_cases h : n < j
  · rw [if_pos h, if_pos (by omega : 2 * n + 2 < 2 * j + 2)]
    rw [show (2 : ℝ) * (1 / 2) = 1 by ring, Real.rpow_one]
    push_cast
    ring
  · rw [if_neg h, if_neg (by omega : ¬ 2 * n + 2 < 2 * j + 2)]

/-- The exact complete critical composite kernel has a Hardy majorant. -/
theorem paperWoldCompositeEntry_critical_bound (n j : ℕ) :
    ‖paperWoldCompositeEntry (1 / 2) n j‖ ≤ DeletionPrimitiveHardy.tailKernel (3 / 4) n j := by
  rw [paperWoldCompositeEntry_norm_eq_re, paperWoldCompositeEntry_critical_formula]
  by_cases h : n < j
  · rw [if_pos h, Complex.ofReal_re]
    have hj0 : 0 ≤ -xiHeatCassiniWoldNatIncrement (2 * j + 2) :=
      neg_nonneg.mpr (paperWold_even_composite_increment_neg j).le
    have ha : (2 * (n : ℝ) + 3) * (-xiHeatCassiniWoldNatIncrement (2 * n + 2)) ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left (paperWold_even_composite_increment_upper n)
        (by positivity : 0 ≤ 2 * (n : ℝ) + 3)
      simpa only [mul_one_div_cancel (by positivity : 2 * (n : ℝ) + 3 ≠ 0)] using h
    calc
      _ ≤ 1 * (1 / (2 * (j : ℝ) + 3)) :=
        mul_le_mul ha (paperWold_even_composite_increment_upper j) hj0 zero_le_one
      _ ≤ 1 / ((j : ℝ) + 1) := by
        rw [one_mul]
        exact one_div_le_one_div_of_le (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) j])
      _ ≤ _ := PaperHardy.inverse_le_tail n j h.le
  · rw [if_neg h, Complex.zero_re]
    unfold DeletionPrimitiveHardy.tailKernel
    split_ifs <;> positivity

def paperWoldCriticalCompositeKernel : PaperHardy.Kernel where
  entry := paperWoldCompositeEntry (1 / 2)
  bound := paperWoldCompositeEntry_critical_bound

/-- All original even-composite entries, acting on every square-summable history. -/
def paperWoldCriticalCompositeOperator : PaperWoldHistory →L[ℂ] PaperWoldHistory :=
  paperWoldCriticalCompositeKernel.toOperator

theorem paperWoldCriticalCompositeOperator_apply (f : PaperWoldHistory) (n : ℕ) :
    paperWoldCriticalCompositeOperator f n = ∑' j, paperWoldCompositeEntry (1 / 2) n j * f j := rfl

theorem paperWoldCriticalCompositeOperator_single (n j : ℕ) :
    paperWoldCriticalCompositeOperator (lp.single 2 j (1 : ℂ)) n =
      paperWoldCompositeEntry (1 / 2) n j :=
  paperWoldCriticalCompositeKernel.toOperator_single n j

theorem paperWoldCriticalCompositeOperator_norm_le : ‖paperWoldCriticalCompositeOperator‖ ≤ 5 :=
  paperWoldCriticalCompositeKernel.norm_toOperator_le

theorem paperWoldCriticalCompositeOperator_matrix :
    HasLpMatrix paperWoldCriticalCompositeOperator (paperWoldCompositeEntry (1 / 2)) :=
  paperWoldCriticalCompositeOperator_single

end
end RHTower
