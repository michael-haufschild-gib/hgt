import GaloisForLFunctions.RHTower.PaperLiNegativeSuppression

/-! # Finite Li observations and the completed obstruction

Every literal finite-degree cutoff is compact and has norm strictly below one.
The full operator can nevertheless retain a unit gap from every cutoff.
-/

namespace RHTower
noncomputable section
open Classical Filter Topology GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped BigOperators ENNReal

def paperLiNegativePrefixCoeff (b : PaperLiBudget) (N n : ℕ) : ℂ :=
  if n < N then (paperLiNegativeWeight b n : ℂ) else 0

theorem paperLiNegativePrefixCoeff_norm_le (b : PaperLiBudget) (N n : ℕ) :
    ‖paperLiNegativePrefixCoeff b N n‖ ≤ 1 := by
  unfold paperLiNegativePrefixCoeff
  split_ifs
  · exact paperLiNegativeWeight_norm_le b n
  · simp

def paperLiNegativePrefix (b : PaperLiBudget) (N : ℕ) : PaperLiHistory →L[ℂ] PaperLiHistory :=
  lpDiagonalCLM (paperLiNegativePrefixCoeff b N) zero_le_one
    (paperLiNegativePrefixCoeff_norm_le b N)

@[simp] theorem paperLiNegativePrefix_apply (b : PaperLiBudget) (N : ℕ)
    (x : PaperLiHistory) (n : ℕ) :
    paperLiNegativePrefix b N x n = if n < N then paperLiNegativeOperator b x n else 0 := by
  simp [paperLiNegativePrefix, paperLiNegativePrefixCoeff, ite_mul]

theorem paperLiNegativePrefix_compact (b : PaperLiBudget) (N : ℕ) :
    IsCompactOperator (paperLiNegativePrefix b N) := by
  apply isCompactOperator_lpDiagonalCLM
  apply (tendsto_const_nhds (x := (0 : ℝ))).congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  simp [paperLiNegativePrefixCoeff, not_lt_of_ge hn]

theorem paperLiNegativePrefix_traceCost (b : PaperLiBudget) (N : ℕ) :
    compactOperatorTraceCost PaperLiHistory (paperLiNegativePrefix b N) = 0 :=
  (compactOperatorTraceCost_eq_zero_iff _).mpr (paperLiNegativePrefix_compact b N)

theorem paperLiNegativePrefix_strong_tendsto (b : PaperLiBudget) (x : PaperLiHistory) :
    Tendsto (fun N => paperLiNegativePrefix b N x) atTop (𝓝 (paperLiNegativeOperator b x)) := by
  apply paperLpDiagonal_strong_tendsto (paperLiNegativePrefixCoeff b)
    (fun n => (paperLiNegativeWeight b n : ℂ)) 1 zero_le_one
    (paperLiNegativePrefixCoeff_norm_le b) (paperLiNegativeWeight_norm_le b)
  intro n
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop n] with N hN
  simp [paperLiNegativePrefixCoeff, hN]

theorem paperLiNegativePrefix_gap (b : PaperLiBudget) (N : ℕ) :
    (if RiemannHypothesis then 0 else 1) ≤
      ‖paperLiNegativeOperator b - paperLiNegativePrefix b N‖ := by
  classical
  exact paperLiNegativeOperator_compact_gap b
    ⟨paperLiNegativePrefix b N, paperLiNegativePrefix_compact b N⟩

theorem paperLiNegativePrefix_of_RH (h : RiemannHypothesis) (b : PaperLiBudget) (N : ℕ) :
    paperLiNegativePrefix b N = 0 := by
  ext x n
  simp [paperLiNegativeOperator_of_RH h]

theorem paperLiNegativePrefix_norm_tendsto_iff (b : PaperLiBudget) :
    Tendsto (paperLiNegativePrefix b) atTop (𝓝 (paperLiNegativeOperator b)) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    exact (paperLiNegativeOperator_compact_iff b).mp
      (isClosed_setOf_isCompactOperator.mem_of_tendsto h
        (Eventually.of_forall (paperLiNegativePrefix_compact b)))
  · intro h
    have hz : paperLiNegativePrefix b = fun _ => 0 := by
      funext N
      exact paperLiNegativePrefix_of_RH h b N
    rw [hz, paperLiNegativeOperator_of_RH h]
    exact tendsto_const_nhds

/-- A concrete finite bound using only the observed negative Li magnitudes. -/
def paperLiNegativePrefixCap (b : PaperLiBudget) (N : ℕ) : ℝ :=
  (∑ n ∈ Finset.range N, paperLiNegativeMass n) /
    ((∑ n ∈ Finset.range N, paperLiNegativeMass n) + b.val)

theorem paperLiNegativePrefixCap_nonneg (b : PaperLiBudget) (N : ℕ) :
    0 ≤ paperLiNegativePrefixCap b N := by
  have hs := Finset.sum_nonneg (fun n (_ : n ∈ Finset.range N) => paperLiNegativeMass_nonneg n)
  exact div_nonneg hs (add_pos_of_nonneg_of_pos hs b.property).le

theorem paperLiNegativePrefixCap_lt_one (b : PaperLiBudget) (N : ℕ) :
    paperLiNegativePrefixCap b N < 1 := by
  have hs := Finset.sum_nonneg (fun n (_ : n ∈ Finset.range N) => paperLiNegativeMass_nonneg n)
  rw [paperLiNegativePrefixCap, div_lt_one (add_pos_of_nonneg_of_pos hs b.property)]
  linarith [b.property]

theorem paperLiNegativePrefixCoeff_le_cap (b : PaperLiBudget) (N n : ℕ) :
    ‖paperLiNegativePrefixCoeff b N n‖ ≤ paperLiNegativePrefixCap b N := by
  by_cases hn : n < N
  · rw [paperLiNegativePrefixCoeff, if_pos hn, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (paperLiNegativeWeight_nonneg b n), paperLiNegativeWeight,
      paperLiNegativePrefixCap]
    have hs := Finset.sum_nonneg (fun k (_ : k ∈ Finset.range N) => paperLiNegativeMass_nonneg k)
    have hq := Finset.single_le_sum
      (fun k (_ : k ∈ Finset.range N) => paperLiNegativeMass_nonneg k) (Finset.mem_range.mpr hn)
    rw [div_le_div_iff₀ (add_pos_of_nonneg_of_pos (paperLiNegativeMass_nonneg n) b.property)
      (add_pos_of_nonneg_of_pos hs b.property)]
    nlinarith [b.property]
  · simpa only [paperLiNegativePrefixCoeff, if_neg hn, norm_zero] using
      paperLiNegativePrefixCap_nonneg b N

theorem paperLiNegativePrefix_norm_le_cap (b : PaperLiBudget) (N : ℕ) :
    ‖paperLiNegativePrefix b N‖ ≤ paperLiNegativePrefixCap b N := by
  have he : paperLiNegativePrefix b N = lpDiagonalCLM (paperLiNegativePrefixCoeff b N)
      (paperLiNegativePrefixCap_nonneg b N) (paperLiNegativePrefixCoeff_le_cap b N) := by
    ext x n
    rfl
  rw [he]
  exact norm_lpDiagonalCLM_le _ _ _

theorem paperLiNegativePrefix_norm_lt_one (b : PaperLiBudget) (N : ℕ) :
    ‖paperLiNegativePrefix b N‖ < 1 :=
  (paperLiNegativePrefix_norm_le_cap b N).trans_lt (paperLiNegativePrefixCap_lt_one b N)

/-- Every fixed finite observation can be suppressed in operator norm, without RH. -/
theorem paperLiNegativePrefixCap_budget_tendsto (N : ℕ) :
    Tendsto (fun m => paperLiNegativePrefixCap (paperLiIncreasingBudget m) N) atTop (𝓝 0) := by
  let S : ℝ := ∑ n ∈ Finset.range N, paperLiNegativeMass n
  have hs : 0 ≤ S := Finset.sum_nonneg (fun n _ => paperLiNegativeMass_nonneg n)
  have hd : Tendsto (fun m : ℕ => S + ((m : ℝ) + 1)) atTop atTop :=
    tendsto_atTop_mono (fun m => by linarith) (tendsto_natCast_atTop_atTop (R := ℝ))
  have h := (tendsto_inv_atTop_zero.comp hd).const_mul S
  simpa only [paperLiNegativePrefixCap, paperLiIncreasingBudget, Function.comp_def,
    div_eq_mul_inv, mul_zero, S] using h

theorem paperLiNegativePrefix_budget_norm_tendsto (N : ℕ) :
    Tendsto (fun m => paperLiNegativePrefix (paperLiIncreasingBudget m) N) atTop (𝓝 0) := by
  have h := squeeze_zero (fun m => norm_nonneg (paperLiNegativePrefix (paperLiIncreasingBudget m) N))
    (fun m => paperLiNegativePrefix_norm_le_cap (paperLiIncreasingBudget m) N)
    (paperLiNegativePrefixCap_budget_tendsto N)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [sub_zero] using h

end
end RHTower
