import GaloisForLFunctions.RHTower.PaperLagCayleySchattenThreshold

/-! # Quantitative trace-norm approximation of the full Cayley discrepancy

The literal finite prefixes converge in trace norm. The cubic curvature
estimate yields an explicit reciprocal trace-tail bound by telescoping.
-/

namespace RHTower.PaperLagCayley
noncomputable section
open GaloisForLFunctions GaloisForLFunctions.HTGeometry Filter
open scoped Topology

private def tailCoefficient (N n : ℕ) : ℂ :=
  if n < N then 0 else (phase n : ℂ) - arithmeticPhase n

private theorem norm_tailCoefficient_le (N n : ℕ) : ‖tailCoefficient N n‖ ≤ 2 := by
  unfold tailCoefficient
  split_ifs
  · simp
  · exact norm_phase_discrepancy_le_two n

private theorem summable_norm_tailCoefficient (N : ℕ) :
    Summable (fun n => ‖tailCoefficient N n‖) := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    summable_phase_discrepancy
  unfold tailCoefficient
  split_ifs
  · simp only [norm_zero, norm_nonneg]
  · exact le_rfl

private theorem difference_sub_prefix_eq_diagonal (N : ℕ) :
    (sourceOperator - arithmeticOperator) - differencePrefix N =
      lpDiagonalCLM (tailCoefficient N) (by norm_num : (0 : ℝ) ≤ 2)
        (norm_tailCoefficient_le N) := by
  ext x n
  simp only [sub_apply, lp.coeFn_sub, Pi.sub_apply, sourceOperator_apply,
    arithmeticOperator_apply, differencePrefix, diagonalOperator_apply, truncMultiplier,
    lpDiagonalCLM_apply, tailCoefficient]
  split_ifs <;> ring

private theorem difference_sub_prefix_memSchattenClass_iff (N : ℕ) {p : ℝ} (hp : 0 < p) :
    MemSchattenClass p ((sourceOperator - arithmeticOperator) - differencePrefix N) ↔
      (1 / 2 : ℝ) < p := by
  rw [difference_sub_prefix_eq_diagonal, memSchattenClass_lpDiagonalCLM_iff _ _ _ hp]
  have htail : (Summable fun n => ‖tailCoefficient N n‖ ^ p) ↔
      Summable (fun n => ‖(phase (n + N) : ℂ) - arithmeticPhase (n + N)‖ ^ p) := by
    have he (n : ℕ) : tailCoefficient N (n + N) =
        (phase (n + N) : ℂ) - arithmeticPhase (n + N) := by
      rw [tailCoefficient, if_neg (by omega : ¬ n + N < N)]
    rw [← summable_nat_add_iff N]
    simp only [he]
  exact htail.trans ((summable_nat_add_iff N).trans (summable_phase_discrepancy_rpow_iff p))

theorem difference_sub_prefix_schatten_spectrum (N : ℕ) :
    {p : ℝ | 0 < p ∧
      MemSchattenClass p ((sourceOperator - arithmeticOperator) - differencePrefix N)} =
      Set.Ioi (1 / 2) := by
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_Ioi]
  constructor
  · rintro ⟨hp, h⟩
    exact (difference_sub_prefix_memSchattenClass_iff N hp).mp h
  · intro hp
    have hp0 : 0 < p := by linarith
    exact ⟨hp0, (difference_sub_prefix_memSchattenClass_iff N hp0).mpr hp⟩

theorem difference_sub_prefix_not_finite_rank (N k : ℕ) :
    ¬ HasRankLE ((sourceOperator - arithmeticOperator) - differencePrefix N) k := by
  intro h
  have hm := memSchattenClass_of_hasRankLE (p := 1 / 2) (by norm_num) h
  exact lt_irrefl (1 / 2 : ℝ)
    ((difference_sub_prefix_memSchattenClass_iff N (by norm_num)).mp hm)

theorem difference_sub_prefix_memSchattenClass_one (N : ℕ) :
    MemSchattenClass 1 ((sourceOperator - arithmeticOperator) - differencePrefix N) := by
  rw [difference_sub_prefix_eq_diagonal, memSchattenClass_lpDiagonalCLM_iff _ _ _ zero_lt_one]
  simpa only [Real.rpow_one] using summable_norm_tailCoefficient N

theorem traceNorm_difference_sub_prefix (N : ℕ) :
    traceNorm Space ((sourceOperator - arithmeticOperator) - differencePrefix N) =
      ∑' n, ‖(phase (n + N) : ℂ) - arithmeticPhase (n + N)‖ := by
  rw [difference_sub_prefix_eq_diagonal, traceNorm_lpDiagonalCLM]
  have hz : ∑ n ∈ Finset.range N, ‖tailCoefficient N n‖ = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simp only [tailCoefficient, if_pos (Finset.mem_range.mp hn), norm_zero]
  have h := (summable_norm_tailCoefficient N).sum_add_tsum_nat_add N
  rw [hz, zero_add] at h
  rw [← h]
  apply tsum_congr
  intro n
  simp only [tailCoefficient, if_neg (by omega : ¬ n + N < N)]

theorem phase_discrepancy_tail_sum_le (N : ℕ) :
    (∑' n, ‖(phase (n + (N + 9)) : ℂ) - arithmeticPhase (n + (N + 9))‖) ≤
      1 / (3 * (N + 11 : ℝ)) := by
  let F : ℕ → ℝ := fun n => 1 / (3 * (n + N + 11 : ℝ))
  have hb (n : ℕ) :
      ‖(phase (n + (N + 9)) : ℂ) - arithmeticPhase (n + (N + 9))‖ ≤ F n - F (n + 1) := by
    have h := phase_discrepancy_tail_le (n + N)
    rw [Nat.add_assoc] at h
    refine h.trans_eq ?_
    dsimp only [F]
    push_cast
    rw [show (n : ℝ) + 1 + N + 11 = n + N + 12 by ring]
    have h11 : (n : ℝ) + N + 11 ≠ 0 := by positivity
    have h12 : (n : ℝ) + N + 12 ≠ 0 := by positivity
    field_simp
    ring
  apply Real.tsum_le_of_sum_range_le (fun _ => norm_nonneg _)
  intro M
  calc
    _ ≤ ∑ n ∈ Finset.range M, (F n - F (n + 1)) := Finset.sum_le_sum fun n _ => hb n
    _ = F 0 - F M := Finset.sum_range_sub' F M
    _ ≤ F 0 := sub_le_self _ (by dsimp only [F]; positivity)
    _ = _ := by simp only [F, Nat.cast_zero, zero_add]

theorem traceNorm_difference_sub_prefix_le (N : ℕ) :
    traceNorm Space ((sourceOperator - arithmeticOperator) - differencePrefix (N + 9)) ≤
      1 / (3 * (N + 11 : ℝ)) := by
  rw [traceNorm_difference_sub_prefix]
  exact phase_discrepancy_tail_sum_le N

theorem traceNorm_difference_sub_prefix_tendsto_zero :
    Tendsto (fun N => traceNorm Space ((sourceOperator - arithmeticOperator) - differencePrefix N))
      atTop (𝓝 0) := by
  simpa only [traceNorm_difference_sub_prefix] using
    tendsto_sum_nat_add (fun n => ‖(phase n : ℂ) - arithmeticPhase n‖)

end
end RHTower.PaperLagCayley
