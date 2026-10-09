import GaloisForLFunctions.RHTower.WeilLogShiftUniformMomentReceiver

/-!
# Exact finite matrix norms for recovery moments

A panel of the first N centered moment coordinates depends only on the first
N−2 history coordinates. Its operator norm is exactly the sum of the absolute
column responses. A bounded arithmetic history with zero deviation removes the
affine baseline moment premise, leaving only finite-sign matrix bounds as an
exact receiver. The response matrix is shifted triangular with an explicit
positive diagonal. No interior convergence estimate is assumed or asserted.
-/

open Filter Topology Zeta23 Real
open scoped BigOperators BoundedContinuousFunction

noncomputable section

namespace RHTower

open WeilExcess

/-- A finite recovery prefix determines precisely the corresponding coefficient head. -/
theorem weilLogShiftRecoveryInverse_prefix (h g : ℕ → ℝ) (M : ℕ)
    (hh : ∀ k : ℕ, k < M → h k = g k) (n : ℕ) (hn : n < M + 2) :
    weilLogShiftRecoveryInverse h n = weilLogShiftRecoveryInverse g n := by
  by_cases hn2 : 2 ≤ n
  · apply (weilLogShiftRecoveryProbe_prefix_iff
      (weilLogShiftRecoveryInverse h) (weilLogShiftRecoveryInverse g) n).mp ?_ n hn2 le_rfl
    intro j hj hjn
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = k + 2 := ⟨j - 2, by omega⟩
    change weilLogShiftRecoveryHistory (weilLogShiftRecoveryInverse h) k =
      weilLogShiftRecoveryHistory (weilLogShiftRecoveryInverse g) k
    rw [weilLogShiftRecoveryHistory_inverse, weilLogShiftRecoveryHistory_inverse]
    exact hh k (by omega)
  · have hsmall : n = 0 ∨ n = 1 := by omega
    rcases hsmall with rfl | rfl
    · exact (weilLogShiftRecoveryInverse_head h).1.trans
        (weilLogShiftRecoveryInverse_head g).1.symm
    · exact (weilLogShiftRecoveryInverse_head h).2.trans
        (weilLogShiftRecoveryInverse_head g).2.symm

/-- Centered weighted coordinates inherit the sharp finite-prefix dependence. -/
theorem weilLogShiftRecoveryMomentCLM_prefix (y : ℝ) (M : ℕ) (h g : ℕ →ᵇ ℝ)
    (hh : ∀ k : ℕ, k < M → h k = g k) (n : ℕ) (hn : n < M + 2) :
    weilLogShiftRecoveryMomentCLM y n h = weilLogShiftRecoveryMomentCLM y n g := by
  simp only [weilLogShiftRecoveryMomentCLM_apply, weilLogShiftRecoveryMoment, weilDeviation,
    weilLogShiftRecoveryInverse_prefix h g M hh n hn]

/-- The bounded history which is one at k and zero elsewhere. -/
def weilLogShiftRecoveryUnitHistory (k : ℕ) : ℕ →ᵇ ℝ :=
  weilLogShiftBoundedHistoryBCF fun j =>
    ⟨if j = k then 1 else 0, by split_ifs <;> norm_num⟩

theorem weilLogShiftRecoveryUnitHistory_apply (k j : ℕ) :
    weilLogShiftRecoveryUnitHistory k j = if j = k then 1 else 0 := rfl

/-- Weighted centered inverse response to a single history coordinate. -/
def weilLogShiftRecoveryMomentResponse (y : ℝ) (n k : ℕ) : ℝ :=
  weilLogShiftRecoveryMomentCLM y n (weilLogShiftRecoveryUnitHistory k)

/-- The response matrix vanishes above its shifted diagonal. -/
theorem weilLogShiftRecoveryMomentResponse_eq_zero (y : ℝ) (n k : ℕ) (hn : n < k + 2) :
    weilLogShiftRecoveryMomentResponse y n k = 0 := by
  have hp := weilLogShiftRecoveryMomentCLM_prefix y k (weilLogShiftRecoveryUnitHistory k) 0
    (fun j hj => by
      change (if j = k then (1 : ℝ) else 0) = 0
      exact if_neg (by omega)) n hn
  simpa only [weilLogShiftRecoveryMomentResponse, map_zero] using hp

/-- The first visible response is the reciprocal triangular diagonal, weighted
by the chosen full paired kernel. -/
theorem weilLogShiftRecoveryMomentResponse_diagonal (y : ℝ) (k : ℕ) :
    weilLogShiftRecoveryMomentResponse y (k + 2) k =
      pairedLogKernel y (k + 2) /
        (sqrt (k + 2 : ℕ) * weilLogShiftRecoveryWeight (k + 2) (k + 2)) := by
  have hh (j : ℕ) (hj : j < k) : weilLogShiftRecoveryUnitHistory k j = (0 : ℝ) := by
    rw [weilLogShiftRecoveryUnitHistory_apply, if_neg (by omega)]
  have hd := weilLogShiftRecoveryProbe_first_difference
    (weilLogShiftRecoveryInverse (weilLogShiftRecoveryUnitHistory k))
    (weilLogShiftRecoveryInverse (fun _ => 0)) (k + 2) (by omega)
    (fun j _ hj => weilLogShiftRecoveryInverse_prefix _ _ k hh j hj)
  have hsample : weilLogShiftRecoveryProbe
      (weilLogShiftRecoveryInverse (weilLogShiftRecoveryUnitHistory k)) (k + 2) -
      weilLogShiftRecoveryProbe (weilLogShiftRecoveryInverse (fun _ => 0)) (k + 2) = 1 := by
    change weilLogShiftRecoveryHistory
      (weilLogShiftRecoveryInverse (weilLogShiftRecoveryUnitHistory k)) k -
      weilLogShiftRecoveryHistory (weilLogShiftRecoveryInverse (fun _ => 0)) k = 1
    rw [weilLogShiftRecoveryHistory_inverse, weilLogShiftRecoveryHistory_inverse]
    simp only [weilLogShiftRecoveryUnitHistory_apply, ite_true, sub_zero]
  rw [hsample] at hd
  have hw := weilLogShiftRecoveryWeight_diagonal_pos (k + 2) (by omega)
  have hr : 0 < sqrt (k + 2 : ℕ) := sqrt_pos.mpr (by positivity)
  have hdelta : weilLogShiftRecoveryInverse (weilLogShiftRecoveryUnitHistory k) (k + 2) -
      weilLogShiftRecoveryInverse (fun _ => 0) (k + 2) =
      1 / weilLogShiftRecoveryWeight (k + 2) (k + 2) := by
    field_simp [hw.ne']
    nlinarith only [hd]
  unfold weilLogShiftRecoveryMomentResponse
  rw [weilLogShiftRecoveryMomentCLM_apply]
  simp only [weilLogShiftRecoveryMoment, weilDeviation, if_pos (show 2 ≤ k + 2 by omega)]
  calc
    _ = ((weilLogShiftRecoveryInverse (weilLogShiftRecoveryUnitHistory k) (k + 2) -
        weilLogShiftRecoveryInverse (fun _ => 0) (k + 2)) / sqrt (k + 2 : ℕ)) *
        pairedLogKernel y (k + 2) := by ring
    _ = _ := by rw [hdelta]; field_simp [hw.ne', hr.ne']

theorem weilLogShiftRecoveryMomentResponse_diagonal_pos (y : ℝ) (k : ℕ) :
    0 < weilLogShiftRecoveryMomentResponse y (k + 2) k := by
  rw [weilLogShiftRecoveryMomentResponse_diagonal]
  exact div_pos (pairedLogKernel_pos y (k + 2))
    (mul_pos (sqrt_pos.mpr (by positivity))
      (weilLogShiftRecoveryWeight_diagonal_pos (k + 2) (by omega)))

private def historyTruncation (h : ℕ →ᵇ ℝ) (M : ℕ) : ℕ →ᵇ ℝ :=
  ∑ k ∈ Finset.range M, h k • weilLogShiftRecoveryUnitHistory k

private theorem historyTruncation_apply (h : ℕ →ᵇ ℝ) (M j : ℕ) (hj : j < M) :
    historyTruncation h M j = h j := by
  simp [historyTruncation, weilLogShiftRecoveryUnitHistory_apply, mul_ite, hj]

/-- A signed moment panel has an exact finite coordinate expansion. -/
theorem weilLogShiftRecoveryMomentPanel_eq_columns (y : ℝ) (N : ℕ) (sign : ℕ → Bool)
    (h : ℕ →ᵇ ℝ) :
    weilLogShiftRecoveryMomentPanel y N sign h =
      ∑ k ∈ Finset.range (N - 2), h k *
        weilLogShiftRecoveryMomentPanel y N sign (weilLogShiftRecoveryUnitHistory k) := by
  calc
    _ = weilLogShiftRecoveryMomentPanel y N sign (historyTruncation h (N - 2)) := by
      rw [weilLogShiftRecoveryMomentPanel_apply, weilLogShiftRecoveryMomentPanel_apply]
      apply Finset.sum_congr rfl
      intro n hn
      congr 1
      exact weilLogShiftRecoveryMomentCLM_prefix y (N - 2) h (historyTruncation h (N - 2))
        (fun k hk => (historyTruncation_apply h (N - 2) k hk).symm) n
        (by have := Finset.mem_range.mp hn; omega)
    _ = _ := by simp only [historyTruncation, map_sum, map_smul, smul_eq_mul]

/-- Every signed panel norm is exactly the finite sum of absolute column responses. -/
theorem norm_weilLogShiftRecoveryMomentPanel_eq_columns (y : ℝ) (N : ℕ) (sign : ℕ → Bool) :
    ‖weilLogShiftRecoveryMomentPanel y N sign‖ =
      ∑ k ∈ Finset.range (N - 2),
        ‖weilLogShiftRecoveryMomentPanel y N sign (weilLogShiftRecoveryUnitHistory k)‖ := by
  let T := weilLogShiftRecoveryMomentPanel y N sign
  let a : ℕ → ℝ := fun k => T (weilLogShiftRecoveryUnitHistory k)
  have hnonneg : 0 ≤ ∑ k ∈ Finset.range (N - 2), ‖a k‖ :=
    Finset.sum_nonneg fun k _ => norm_nonneg _
  apply le_antisymm
  · apply T.opNorm_le_bound hnonneg
    intro h
    rw [weilLogShiftRecoveryMomentPanel_eq_columns]
    calc
      _ ≤ ∑ k ∈ Finset.range (N - 2), ‖h k * a k‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range (N - 2), ‖a k‖ * ‖h‖ := by
        apply Finset.sum_le_sum
        intro k _
        rw [norm_mul, mul_comm]
        exact mul_le_mul_of_nonneg_left (h.norm_coe_le_norm k) (norm_nonneg _)
      _ = _ := (Finset.sum_mul _ _ _).symm
  · let v : WeilLogShiftBoundedHistory := fun k =>
      ⟨if 0 ≤ a k then 1 else -1, by split_ifs <;> norm_num⟩
    have hsign (k : ℕ) : weilLogShiftBoundedHistoryBCF v k * a k = ‖a k‖ := by
      change (if 0 ≤ a k then 1 else -1) * a k = ‖a k‖
      by_cases hk : 0 ≤ a k
      · simp only [if_pos hk, one_mul, Real.norm_eq_abs, abs_of_nonneg hk]
      · simp only [if_neg hk, neg_one_mul, Real.norm_eq_abs, abs_of_neg (lt_of_not_ge hk)]
    have hvalue : T (weilLogShiftBoundedHistoryBCF v) =
        ∑ k ∈ Finset.range (N - 2), ‖a k‖ := by
      rw [weilLogShiftRecoveryMomentPanel_eq_columns]
      exact Finset.sum_congr rfl fun k _ => hsign k
    calc
      _ = ‖T (weilLogShiftBoundedHistoryBCF v)‖ := by
        rw [hvalue, Real.norm_eq_abs, abs_of_nonneg hnonneg]
      _ ≤ ‖T‖ * ‖weilLogShiftBoundedHistoryBCF v‖ := T.le_opNorm _
      _ ≤ ‖T‖ := by
        exact (mul_le_mul_of_nonneg_left (norm_weilLogShiftBoundedHistoryBCF_le v)
          (norm_nonneg T)).trans_eq (mul_one _)

/-- A completely finite matrix expression, indexed only by a finite sign vector. -/
def weilLogShiftRecoveryMatrixBudget (y : ℝ) (N : ℕ) (sign : Fin N → Bool) : ℝ :=
  ∑ k : Fin (N - 2), |∑ n : Fin N,
    (if sign n then (1 : ℝ) else -1) * weilLogShiftRecoveryMomentResponse y n k|

/-- The infinite-dimensional operator norm equals its finite response-matrix budget. -/
theorem norm_weilLogShiftRecoveryMomentPanel_eq_matrix (y : ℝ) (N : ℕ) (sign : ℕ → Bool) :
    ‖weilLogShiftRecoveryMomentPanel y N sign‖ =
      weilLogShiftRecoveryMatrixBudget y N (fun n => sign n) := by
  let a : ℕ → ℕ → ℝ := fun n k =>
    (if sign n then (1 : ℝ) else -1) * weilLogShiftRecoveryMomentResponse y n k
  calc
    _ = ∑ k ∈ Finset.range (N - 2), |∑ n ∈ Finset.range N, a n k| := by
      rw [norm_weilLogShiftRecoveryMomentPanel_eq_columns]
      simp only [a, weilLogShiftRecoveryMomentPanel_apply,
        weilLogShiftRecoveryMomentResponse, Real.norm_eq_abs]
    _ = ∑ k : Fin (N - 2), |∑ n ∈ Finset.range N, a n k| :=
      (Fin.sum_univ_eq_sum_range (fun k => |∑ n ∈ Finset.range N, a n k|) (N - 2)).symm
    _ = _ := by
      unfold weilLogShiftRecoveryMatrixBudget
      apply Finset.sum_congr rfl
      intro k _
      congr 1
      exact (Fin.sum_univ_eq_sum_range (fun n => a n k) N).symm

/-- The arithmetic coefficient system has a bounded recovery history, because
its zero deviations make the fixed probe converge along cofinal cutoffs. -/
theorem exists_bound_weilLogShiftArithmeticHistory :
    ∃ C : ℝ, ∀ k : ℕ,
      ‖weilLogShiftRecoveryHistory (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) k‖ ≤ C := by
  have hdev (n : ℕ) :
      weilDeviation (fun j => (ArithmeticFunction.vonMangoldt j : ℝ)) n = 0 := by
    simp [weilDeviation]
  have hs : Summable (fun n =>
      weilDeviation (fun j => (ArithmeticFunction.vonMangoldt j : ℝ)) n *
        (riemannAutocorr (log (2 : ℕ) + log n) + riemannAutocorr (log (2 : ℕ) - log n))) := by
    simp only [hdev, zero_mul]
    exact summable_zero
  have ht := (tendsto_logShift_probe_of_summable_sample (m := 2) (by omega) hs).comp
    tendsto_weilLogShiftRecoveryCutoff
  obtain ⟨C, hC⟩ := ht.norm.bddAbove_range
  exact ⟨C, fun k => hC ⟨k + 2, rfl⟩⟩

/-- A bounded arithmetic anchor whose reconstructed deviations all vanish. -/
def weilLogShiftArithmeticHistoryBCF : ℕ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (weilLogShiftRecoveryHistory (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)))
    continuous_of_discreteTopology (Classical.choose exists_bound_weilLogShiftArithmeticHistory)
    (Classical.choose_spec exists_bound_weilLogShiftArithmeticHistory)

theorem weilLogShiftRecoveryMoment_arithmetic_zero (y : ℝ) (n : ℕ) :
    weilLogShiftRecoveryMoment y weilLogShiftArithmeticHistoryBCF n = 0 := by
  change weilDeviation (weilLogShiftRecoveryInverse
    (weilLogShiftRecoveryHistory (fun j => (ArithmeticFunction.vonMangoldt j : ℝ)))) n *
      pairedLogKernel y n = 0
  rw [weilDeviation_recoveryInverse_history]
  simp [weilDeviation]

/-- Subtracting the arithmetic history turns the full affine moment into a
centered linear response, with no residual baseline term. -/
theorem weilLogShiftRecoveryMomentCLM_sub_arithmetic (y : ℝ) (n : ℕ) (h : ℕ →ᵇ ℝ) :
    weilLogShiftRecoveryMomentCLM y n (h - weilLogShiftArithmeticHistoryBCF) =
      weilLogShiftRecoveryMoment y h n := by
  rw [map_sub, weilLogShiftRecoveryMomentCLM_apply, weilLogShiftRecoveryMomentCLM_apply,
    weilLogShiftRecoveryMoment_arithmetic_zero]
  ring

/-- The affine baseline summability premise is redundant: the bounded arithmetic
anchor makes uniform centered panel bounds sufficient on their own. -/
theorem weilLogShiftBoundedMomentSummable_iff_panel_bound (y : ℝ) :
    WeilLogShiftBoundedMomentSummable y ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ N sign, ‖weilLogShiftRecoveryMomentPanel y N sign‖ ≤ C := by
  constructor
  · exact weilLogShiftRecoveryMomentPanel_bounded
  · rintro ⟨C, _, hC⟩ h
    apply summable_norm_iff.mp
    apply summable_of_sum_range_le (fun n => norm_nonneg _)
    intro N
    have hcoe : (weilLogShiftBoundedHistoryBCF h : ℕ → ℝ) =
        weilLogShiftBoundedHistoryValues h := rfl
    simpa only [weilLogShiftRecoveryMomentCLM_sub_arithmetic, hcoe] using
      sum_norm_weilLogShiftRecoveryMomentCLM_le y hC
        (weilLogShiftBoundedHistoryBCF h - weilLogShiftArithmeticHistoryBCF) N

/-- Exact finite matrix receiver with the affine baseline premise discharged.
Only a uniform bound over finite matrices and finite sign vectors remains. -/
theorem weilLogShiftBoundedMomentSummable_iff_matrix_bound (y : ℝ) :
    WeilLogShiftBoundedMomentSummable y ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (sign : Fin N → Bool),
        weilLogShiftRecoveryMatrixBudget y N sign ≤ C := by
  rw [weilLogShiftBoundedMomentSummable_iff_panel_bound]
  constructor
  · rintro ⟨C, hC0, hC⟩
    refine ⟨C, hC0, fun N sign => ?_⟩
    let extended : ℕ → Bool := fun n => if hn : n < N then sign ⟨n, hn⟩ else false
    have heq : (fun n : Fin N => extended n) = sign := by
      funext n
      exact dif_pos n.isLt
    have h := hC N extended
    rw [norm_weilLogShiftRecoveryMomentPanel_eq_matrix, heq] at h
    exact h
  · rintro ⟨C, hC0, hC⟩
    refine ⟨C, hC0, fun N sign => ?_⟩
    rw [norm_weilLogShiftRecoveryMomentPanel_eq_matrix]
    exact hC N (fun n => sign n)

end RHTower
