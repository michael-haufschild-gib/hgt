import GaloisForLFunctions.RHTower.PaperLagCayleyRelativePhase
import GaloisForLFunctions.HTGeometry.LpDiagonalFredholmDeterminant

/-! # The actual relative Fredholm determinant of the lag source

The source/arithmetic unitary quotient has a trace-class defect. Removing any
finite coordinate prefix gives the exponential of the exact remaining signed
phase, using the corpus operator determinant and its standard Hilbert basis.
-/

namespace RHTower.PaperLagCayley
noncomputable section
open GaloisForLFunctions GaloisForLFunctions.HTGeometry HilbertSchmidt
open _root_.Complex ContinuousLinearMap

def relativeOperator : Space →L[ℂ] Space := sourceOperator * arithmeticOperator.adjoint

def relativeDefect (N : ℕ) : Space →L[ℂ] Space :=
  ((sourceOperator - arithmeticOperator) - differencePrefix N) * arithmeticOperator.adjoint

theorem arithmeticOperator_adjoint_apply (x : Space) (n : ℕ) :
    arithmeticOperator.adjoint x n = (arithmeticPhase n : ℂ)⁻¹ * x n := by
  have hc : ∀ n, ‖(starRingEnd ℂ) (arithmeticPhase n : ℂ)‖ ≤ 1 := by
    intro n
    simp only [Complex.norm_conj, Circle.norm_coe, le_refl]
  let B := lpDiagonalCLM (fun n => (starRingEnd ℂ) (arithmeticPhase n : ℂ))
    zero_le_one hc
  have he : arithmeticOperator = B.adjoint :=
    (ContinuousLinearMap.eq_adjoint_iff _ _).2
      (lpDiagonalCLM_inner _ _ _ zero_le_one hc)
  rw [he, ContinuousLinearMap.adjoint_adjoint]
  change (starRingEnd ℂ) (arithmeticPhase n : ℂ) * x n = _
  rw [← Circle.coe_inv_eq_conj, Circle.coe_inv]

theorem relativeDefect_zero : relativeDefect 0 = relativeOperator - 1 := by
  ext x n
  change (phase n : ℂ) * (arithmeticOperator.adjoint x n) -
      (arithmeticPhase n : ℂ) * (arithmeticOperator.adjoint x n) -
      (if n < 0 then (phase n : ℂ) - arithmeticPhase n else 0) *
        (arithmeticOperator.adjoint x n) =
    (phase n : ℂ) * (arithmeticOperator.adjoint x n) - x n
  rw [arithmeticOperator_adjoint_apply]
  simp only [Nat.not_lt_zero, if_false, zero_mul, sub_zero]
  field_simp [Circle.coe_ne_zero]

private def coefficient (N n : ℕ) : ℂ := if n < N then 0 else relativePhase n - 1

private theorem coefficient_bound (N n : ℕ) : ‖coefficient N n‖ ≤ 2 := by
  by_cases hn : n < N
  · simp [coefficient, hn]
  · simpa only [coefficient, if_neg hn, norm_relativePhase_sub_one] using
      norm_phase_discrepancy_le_two n

private theorem coefficient_summable (N : ℕ) : Summable (fun n => ‖coefficient N n‖) := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    summable_phase_discrepancy
  by_cases hn : n < N
  · simp only [coefficient, if_pos hn, norm_zero, norm_nonneg]
  · simp only [coefficient, if_neg hn, norm_relativePhase_sub_one, le_refl]

private theorem relativeDefect_diagonal (N : ℕ) :
    relativeDefect N = lpDiagonalCLM (coefficient N) (by norm_num) (coefficient_bound N) := by
  ext x n
  change (phase n : ℂ) * (arithmeticOperator.adjoint x n) -
      (arithmeticPhase n : ℂ) * (arithmeticOperator.adjoint x n) -
      (if n < N then (phase n : ℂ) - arithmeticPhase n else 0) *
        (arithmeticOperator.adjoint x n) = coefficient N n * x n
  rw [arithmeticOperator_adjoint_apply]
  dsimp only [coefficient, relativePhase]
  by_cases hn : n < N
  · simp only [if_pos hn, zero_mul]
    ring
  · simp only [if_neg hn, zero_mul, sub_zero]
    field_simp [Circle.coe_ne_zero]

theorem relativeDefect_traceClass (N : ℕ) : MemSchattenClass 1 (relativeDefect N) := by
  rw [relativeDefect_diagonal, memSchattenClass_lpDiagonalCLM_iff _ _ _ zero_lt_one]
  simpa only [Real.rpow_one] using coefficient_summable N

theorem relativeDefect_memSchattenClass_iff (N : ℕ) {p : ℝ} (hp : 0 < p) :
    MemSchattenClass p (relativeDefect N) ↔ (1 / 2 : ℝ) < p := by
  rw [relativeDefect_diagonal, memSchattenClass_lpDiagonalCLM_iff _ _ _ hp]
  have he : (fun n => ‖coefficient N (n + N)‖ ^ p) =
      (fun n => ‖(phase (n + N) : ℂ) - arithmeticPhase (n + N)‖ ^ p) := by
    funext n
    simp only [coefficient, if_neg (by omega : ¬ n + N < N), norm_relativePhase_sub_one]
  rw [← summable_nat_add_iff N (f := fun n => ‖coefficient N n‖ ^ p), he]
  exact (summable_nat_add_iff N
    (f := fun n => ‖(phase n : ℂ) - arithmeticPhase n‖ ^ p)).trans
      (summable_phase_discrepancy_rpow_iff p)

theorem relativeDefect_schatten_spectrum (N : ℕ) :
    {p : ℝ | 0 < p ∧ MemSchattenClass p (relativeDefect N)} = Set.Ioi (1 / 2) := by
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_Ioi]
  constructor
  · rintro ⟨hp, h⟩
    exact (relativeDefect_memSchattenClass_iff N hp).mp h
  · intro hp
    have hp0 : 0 < p := by linarith
    exact ⟨hp0, (relativeDefect_memSchattenClass_iff N hp0).mpr hp⟩

theorem relativeDefect_not_finite_rank (N k : ℕ) : ¬ HasRankLE (relativeDefect N) k := by
  intro h
  have hm := memSchattenClass_of_hasRankLE (p := 1 / 2) (by norm_num) h
  exact lt_irrefl (1 / 2 : ℝ)
    ((relativeDefect_memSchattenClass_iff N (by norm_num)).mp hm)

private theorem coefficient_hasProd (N : ℕ) :
    HasProd (fun n => 1 + coefficient N n)
      (Complex.exp ((relativeAngleTail N : ℂ) * I)) := by
  let a : ℕ → ℝ := fun n => if n < N then 0 else relativeAngle n
  have ha : Summable (fun n => |a n|) := by
    refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun n => ?_)
      summable_abs_relativeAngle
    dsimp only [a]
    split_ifs <;> simp
  have ht : (∑' n, a n) = relativeAngleTail N := by
    have h := ha.of_abs.sum_add_tsum_nat_add N
    have hz : (∑ n ∈ Finset.range N, a n) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      simp only [a, if_pos (Finset.mem_range.mp hn)]
    rw [hz, zero_add] at h
    rw [← h]
    apply tsum_congr
    intro n
    simp only [a, if_neg (by omega : ¬ n + N < N)]
  have hs : HasSum a (relativeAngleTail N) := ht ▸ ha.of_abs.hasSum
  have h := ((Complex.ofRealCLM.hasSum hs).mul_right I).cexp
  refine h.congr_fun fun n => ?_
  dsimp only [Function.comp_def, coefficient, a]
  split_ifs with hn
  · simp
  · simpa only [← add_sub_assoc, add_sub_cancel_left, Complex.ofRealCLM_apply] using
      relativePhase_eq_exp n

theorem fredholmDetOp_relativeDefect (N : ℕ) :
    fredholmDetOp (lpBasis ℕ) (relativeDefect N) =
      Complex.exp ((relativeAngleTail N : ℂ) * I) := by
  rw [relativeDefect_diagonal]
  exact fredholmDetOp_lpDiagonalCLM_of_hasProd _ _ _
    (coefficient_summable N) (coefficient_hasProd N)

theorem fredholmDetOp_relativeOperator_sub_one :
    fredholmDetOp (lpBasis ℕ) (relativeOperator - 1) =
      Complex.exp (((∑' n, relativeAngle n) : ℝ) * I) := by
  simpa only [relativeDefect_zero, relativeAngleTail, Nat.add_zero] using
    fredholmDetOp_relativeDefect 0

theorem norm_fredholmDetOp_relativeDefect (N : ℕ) :
    ‖fredholmDetOp (lpBasis ℕ) (relativeDefect N)‖ = 1 := by
  rw [fredholmDetOp_relativeDefect, Complex.norm_exp_ofReal_mul_I]

theorem fredholmDetOp_relativeDefect_ne_zero (N : ℕ) :
    fredholmDetOp (lpBasis ℕ) (relativeDefect N) ≠ 0 := by
  rw [fredholmDetOp_relativeDefect]
  exact Complex.exp_ne_zero _

theorem fredholmDetOp_relativeDefect_ne_one (N : ℕ) :
    fredholmDetOp (lpBasis ℕ) (relativeDefect (N + 9)) ≠ 1 := by
  rw [fredholmDetOp_relativeDefect]
  exact exp_relativeAngleTail_ne_one N

end
end RHTower.PaperLagCayley
