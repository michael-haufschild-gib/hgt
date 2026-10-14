import GaloisForLFunctions.RHTower.PaperLagCayleyRelativeDeterminant

/-! # Finite-prefix approximation of the actual relative determinant -/

namespace RHTower.PaperLagCayley
noncomputable section
open GaloisForLFunctions GaloisForLFunctions.HTGeometry HilbertSchmidt
open _root_.Complex ContinuousLinearMap Filter
open scoped Topology

def relativePrefixDefect (N : ℕ) : Space →L[ℂ] Space :=
  differencePrefix N * arithmeticOperator.adjoint

private def prefixCoefficient (N n : ℕ) : ℂ := if n < N then relativePhase n - 1 else 0

private theorem prefixCoefficient_bound (N n : ℕ) : ‖prefixCoefficient N n‖ ≤ 2 := by
  by_cases hn : n < N
  · simpa only [prefixCoefficient, if_pos hn, norm_relativePhase_sub_one] using
      norm_phase_discrepancy_le_two n
  · simp [prefixCoefficient, hn]

private theorem prefixCoefficient_summable (N : ℕ) :
    Summable (fun n => ‖prefixCoefficient N n‖) := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    summable_phase_discrepancy
  by_cases hn : n < N
  · simp only [prefixCoefficient, if_pos hn, norm_relativePhase_sub_one, le_refl]
  · simp only [prefixCoefficient, if_neg hn, norm_zero, norm_nonneg]

private theorem relativePrefixDefect_diagonal (N : ℕ) :
    relativePrefixDefect N =
      lpDiagonalCLM (prefixCoefficient N) (by norm_num) (prefixCoefficient_bound N) := by
  ext x n
  change (if n < N then (phase n : ℂ) - arithmeticPhase n else 0) *
    (arithmeticOperator.adjoint x n) = prefixCoefficient N n * x n
  rw [arithmeticOperator_adjoint_apply]
  dsimp only [prefixCoefficient, relativePhase]
  by_cases hn : n < N
  · simp only [if_pos hn]
    field_simp [Circle.coe_ne_zero]
  · simp only [if_neg hn, zero_mul]

theorem relativePrefixDefect_traceClass (N : ℕ) :
    MemSchattenClass 1 (relativePrefixDefect N) := by
  rw [relativePrefixDefect_diagonal, memSchattenClass_lpDiagonalCLM_iff _ _ _ zero_lt_one]
  simpa only [Real.rpow_one] using prefixCoefficient_summable N

theorem fredholmDetOp_relativePrefixDefect (N : ℕ) :
    fredholmDetOp (lpBasis ℕ) (relativePrefixDefect N) =
      Complex.exp (((∑ n ∈ Finset.range N, relativeAngle n) : ℝ) * I) := by
  let a : ℕ → ℝ := fun n => if n < N then relativeAngle n else 0
  have ha : Summable (fun n => |a n|) := by
    refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun n => ?_)
      summable_abs_relativeAngle
    dsimp only [a]
    split_ifs <;> simp
  have ht : (∑' n, a n) = ∑ n ∈ Finset.range N, relativeAngle n := by
    have h := ha.of_abs.sum_add_tsum_nat_add N
    have hz : (∑' n, a (n + N)) = 0 := by
      have hz (n : ℕ) : a (n + N) = 0 := by
        simp only [a, if_neg (by omega : ¬ n + N < N)]
      simp only [hz, tsum_zero]
    rw [hz, add_zero] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [a, if_pos (Finset.mem_range.mp hn)]
  have hs : HasSum a (∑ n ∈ Finset.range N, relativeAngle n) := ht ▸ ha.of_abs.hasSum
  have hp := ((Complex.ofRealCLM.hasSum hs).mul_right I).cexp
  have hp' : HasProd (fun n => 1 + prefixCoefficient N n)
      (Complex.exp (((∑ n ∈ Finset.range N, relativeAngle n) : ℝ) * I)) := by
    refine hp.congr_fun fun n => ?_
    dsimp only [Function.comp_def, prefixCoefficient, a]
    split_ifs
    · simpa only [← add_sub_assoc, add_sub_cancel_left, Complex.ofRealCLM_apply] using
        relativePhase_eq_exp n
    · simp
  rw [relativePrefixDefect_diagonal]
  exact fredholmDetOp_lpDiagonalCLM_of_hasProd _ _ _ (prefixCoefficient_summable N) hp'

theorem fredholmDetOp_relative_factorization (N : ℕ) :
    fredholmDetOp (lpBasis ℕ) (relativeOperator - 1) =
      fredholmDetOp (lpBasis ℕ) (relativePrefixDefect N) *
        fredholmDetOp (lpBasis ℕ) (relativeDefect N) := by
  rw [fredholmDetOp_relativeOperator_sub_one, fredholmDetOp_relativePrefixDefect,
    fredholmDetOp_relativeDefect, ← Complex.exp_add]
  congr 1
  rw [← add_mul, ← Complex.ofReal_add]
  congr 2
  exact (summable_relativeAngle.sum_add_tsum_nat_add N).symm

theorem norm_fredholmDetOp_sub_prefix (N : ℕ) :
    ‖fredholmDetOp (lpBasis ℕ) (relativeOperator - 1) -
      fredholmDetOp (lpBasis ℕ) (relativePrefixDefect N)‖ =
        ‖fredholmDetOp (lpBasis ℕ) (relativeDefect N) - 1‖ := by
  rw [fredholmDetOp_relative_factorization N, ← mul_sub_one, norm_mul,
    fredholmDetOp_relativePrefixDefect, Complex.norm_exp_ofReal_mul_I, one_mul]

theorem norm_fredholmDetOp_sub_prefix_le (N : ℕ) :
    ‖fredholmDetOp (lpBasis ℕ) (relativeOperator - 1) -
      fredholmDetOp (lpBasis ℕ) (relativePrefixDefect (N + 9))‖ ≤
        1 / (3 * (N + 11 : ℝ)) := by
  rw [norm_fredholmDetOp_sub_prefix, fredholmDetOp_relativeDefect]
  exact norm_exp_relativeAngleTail_sub_one_le N

theorem fredholmDetOp_sub_prefix_ne_zero (N : ℕ) :
    fredholmDetOp (lpBasis ℕ) (relativeOperator - 1) -
      fredholmDetOp (lpBasis ℕ) (relativePrefixDefect (N + 9)) ≠ 0 := by
  intro he
  have hn := congrArg norm he
  rw [norm_zero, norm_fredholmDetOp_sub_prefix, norm_eq_zero] at hn
  exact exp_relativeAngleTail_ne_one N (by
    simpa only [fredholmDetOp_relativeDefect, sub_eq_zero] using hn)

end
end RHTower.PaperLagCayley
