import GaloisForLFunctions.RHTower.PaperLagCayleyCompositeAsymptotic
import GaloisForLFunctions.RHTower.PaperLagReferenceObservation
import GaloisForLFunctions.HTGeometry.LpDiagonalSchattenEnergy
import GaloisForLFunctions.HTGeometry.PolynomialScaleSummability

/-! # The exact Schatten threshold of the full lag-source discrepancy

The complete source-minus-arithmetic Cayley operator is compact, has infinite
rank, and belongs to exactly the Schatten classes of order greater than one
half. Its positive trace norm contrasts with its zero compact-ideal cost.
-/

namespace RHTower.PaperLagCayley
noncomputable section
open GaloisForLFunctions GaloisForLFunctions.HTGeometry Filter
open scoped Topology

theorem summable_phase_compositeIndex_rpow_iff (p : ℝ) :
    Summable (fun k => ‖(phase (compositeIndex k) : ℂ) -
      arithmeticPhase (compositeIndex k)‖ ^ p) ↔ (1 / 2 : ℝ) < p := by
  have h := summable_rpow_iff_of_polynomial_limit
    (fun k => norm_nonneg ((phase (compositeIndex k) : ℂ) - arithmeticPhase (compositeIndex k)))
    (q := 2) (by norm_num : (0 : ℝ) < 1 / 216)
    (by simpa only [Real.rpow_two] using norm_phase_compositeIndex_rescaled_tendsto) p
  exact h.trans (by constructor <;> intro h <;> linarith)

theorem summable_phase_discrepancy_rpow_iff (p : ℝ) :
    Summable (fun n => ‖(phase n : ℂ) - arithmeticPhase n‖ ^ p) ↔ (1 / 2 : ℝ) < p := by
  constructor
  · intro h
    have hi : Function.Injective compositeIndex := by
      intro i j hij
      dsimp only [compositeIndex] at hij
      omega
    exact (summable_phase_compositeIndex_rpow_iff p).mp (h.comp_injective hi)
  · intro hp
    have hp0 : 0 < p := by linarith
    have hs : Summable (fun n : ℕ => 1 / (n + 1 : ℝ) ^ (2 * p)) := by
      have h := (summable_nat_add_iff
        (f := fun n : ℕ => 1 / (n : ℝ) ^ (2 * p)) 1).mpr
          (Real.summable_one_div_nat_rpow.mpr (by linarith : 1 < 2 * p))
      simpa only [Nat.cast_add, Nat.cast_one] using h
    apply (summable_nat_add_iff 9).mp
    refine Summable.of_nonneg_of_le (fun n => Real.rpow_nonneg (norm_nonneg _) p) (fun n => ?_) hs
    have hb : ‖(phase (n + 9) : ℂ) - arithmeticPhase (n + 9)‖ ≤ 1 / (n + 1 : ℝ) ^ 2 := by
      refine (phase_discrepancy_tail_le n).trans (one_div_le_one_div_of_le (by positivity) ?_)
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    calc
      _ ≤ (1 / (n + 1 : ℝ) ^ 2) ^ p := Real.rpow_le_rpow (norm_nonneg _) hb hp0.le
      _ = 1 / (n + 1 : ℝ) ^ (2 * p) := by
        rw [Real.div_rpow zero_le_one (sq_nonneg _) p, Real.one_rpow,
          ← Real.rpow_two, ← Real.rpow_mul (by positivity)]

theorem difference_eq_lpDiagonalCLM :
    sourceOperator - arithmeticOperator =
      lpDiagonalCLM (fun n => (phase n : ℂ) - arithmeticPhase n)
        (by norm_num : (0 : ℝ) ≤ 2) norm_phase_discrepancy_le_two := by
  ext x n
  simp only [sub_apply, lp.coeFn_sub, Pi.sub_apply, sourceOperator_apply,
    arithmeticOperator_apply, lpDiagonalCLM_apply]
  ring

private theorem difference_memSchattenClass_iff {p : ℝ} (hp : 0 < p) :
    MemSchattenClass p (sourceOperator - arithmeticOperator) ↔ (1 / 2 : ℝ) < p := by
  rw [difference_eq_lpDiagonalCLM, memSchattenClass_lpDiagonalCLM_iff _ _ _ hp,
    summable_phase_discrepancy_rpow_iff]

/-- The entire positive-order Schatten spectrum of the actual discrepancy. -/
theorem difference_schatten_spectrum :
    {p : ℝ | 0 < p ∧ MemSchattenClass p (sourceOperator - arithmeticOperator)} =
      Set.Ioi (1 / 2) := by
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_Ioi]
  constructor
  · rintro ⟨hp, h⟩
    exact (difference_memSchattenClass_iff hp).mp h
  · intro hp
    have hp0 : 0 < p := by linarith
    exact ⟨hp0, (difference_memSchattenClass_iff hp0).mpr hp⟩

theorem difference_memSchattenClass_one :
    MemSchattenClass 1 (sourceOperator - arithmeticOperator) :=
  (difference_memSchattenClass_iff zero_lt_one).mpr (by norm_num)

theorem difference_not_memSchattenClass_half :
    ¬ MemSchattenClass (1 / 2) (sourceOperator - arithmeticOperator) := by
  rw [difference_memSchattenClass_iff (by norm_num : (0 : ℝ) < 1 / 2)]
  exact lt_irrefl _

theorem difference_not_finite_rank (n : ℕ) :
    ¬ HasRankLE (sourceOperator - arithmeticOperator) n := by
  intro h
  exact difference_not_memSchattenClass_half
    (memSchattenClass_of_hasRankLE (by norm_num) h)

theorem difference_traceNorm_eq :
    traceNorm Space (sourceOperator - arithmeticOperator) =
      ∑' n, ‖(phase n : ℂ) - arithmeticPhase n‖ := by
  rw [difference_eq_lpDiagonalCLM, traceNorm_lpDiagonalCLM]

theorem difference_traceNorm_bounds :
    0 < traceNorm Space (sourceOperator - arithmeticOperator) ∧
      traceNorm Space (sourceOperator - arithmeticOperator) ≤ 4 := by
  have hne : sourceOperator - arithmeticOperator ≠ 0 := by
    intro h
    apply difference_not_finite_rank 0
    rw [h]
    exact hasRankLE_zero 0
  have hs : Summable (fun n => approxNumber (sourceOperator - arithmeticOperator) n) := by
    simpa only [MemSchattenClass, Real.rpow_one] using difference_memSchattenClass_one
  refine ⟨(norm_pos_iff.mpr hne).trans_le (norm_le_traceNorm hs), ?_⟩
  rw [difference_traceNorm_eq]
  exact phase_discrepancy_budget

theorem difference_zero_ideal_cost_positive_traceNorm :
    compactOperatorTraceCost Space (sourceOperator - arithmeticOperator) = 0 ∧
      0 < traceNorm Space (sourceOperator - arithmeticOperator) :=
  ⟨source_arithmetic_discrepancy_cost, difference_traceNorm_bounds.1⟩

end
end RHTower.PaperLagCayley
