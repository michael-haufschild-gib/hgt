import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenPaperDilation

/-!
# Product-scale boundary in Proposition 2.2

The source retains only boxes whose lower product scale lies in `(Y/2,4Y]`, then removes the
pointwise indicator.  This file records that operation exactly.  If every box has dilation at most
two, the discarded difference is supported on `(Y/4,8Y]`; its pointwise norm is bounded by the
unsigned aggregate of the original boxes, not by family cardinality times a maximum.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- Box indices whose lower product scale lies in the proposition's exact range. -/
def mtProductScaleIndices {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (M : ι → ℝ) (Y : ℝ) : Finset ι :=
  S.filter fun i => Y / 2 < M i ∧ M i ≤ 4 * Y

/-- Difference between restricting the complete box sum and retaining unrestricted good boxes. -/
def mtProductScaleBoundaryErrorAF {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (F : ι → ArithmeticFunction ℂ) (M : ι → ℝ) (Y : ℝ) :
    ArithmeticFunction ℂ :=
  mtRealIntervalAF (fun n => (∑ i ∈ S, F i) n) (Y / 2) (4 * Y) -
    ∑ i ∈ mtProductScaleIndices S M Y, F i

/-- Exact source decomposition into admissible boxes and product-scale boundary error. -/
theorem mtRealIntervalAF_sum_eq_sum_productScaleIndices_add_error
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (F : ι → ArithmeticFunction ℂ) (M : ι → ℝ) (Y : ℝ) :
    mtRealIntervalAF (fun n => (∑ i ∈ S, F i) n) (Y / 2) (4 * Y) =
      (∑ i ∈ mtProductScaleIndices S M Y, F i) +
        mtProductScaleBoundaryErrorAF S F M Y := by
  unfold mtProductScaleBoundaryErrorAF
  abel

/-- At a positive integer, the boundary error is the bad-box sum inside the target interval and
the negative good-box sum outside it. -/
theorem mtProductScaleBoundaryErrorAF_apply_of_pos
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (F : ι → ArithmeticFunction ℂ) (M : ι → ℝ) (Y : ℝ)
    {n : ℕ} (hn : 0 < n) :
    mtProductScaleBoundaryErrorAF S F M Y n =
      if Y / 2 < (n : ℝ) ∧ (n : ℝ) ≤ 4 * Y then
        ∑ i ∈ S.filter (fun i => ¬(Y / 2 < M i ∧ M i ≤ 4 * Y)), F i n
      else -∑ i ∈ mtProductScaleIndices S M Y, F i n := by
  unfold mtProductScaleBoundaryErrorAF
  change mtRealIntervalAF (fun n => (∑ i ∈ S, F i) n) (Y / 2) (4 * Y) n -
      (∑ i ∈ mtProductScaleIndices S M Y, F i) n = _
  rw [mtRealIntervalAF_apply_of_pos _ _ _ hn]
  simp only [arithmeticFunction_finset_sum_apply]
  by_cases hnY : Y / 2 < (n : ℝ) ∧ (n : ℝ) ≤ 4 * Y
  · simp only [if_pos hnY]
    unfold mtProductScaleIndices
    have hpartition := Finset.sum_filter_add_sum_filter_not
      (s := S) (f := fun i => F i n)
      (p := fun i => Y / 2 < M i ∧ M i ≤ 4 * Y)
    rw [← hpartition]
    ring
  · simp only [if_neg hnY]
    ring

/-- Product-scale filtering never pays the number of boxes pointwise. -/
theorem norm_mtProductScaleBoundaryErrorAF_apply_le
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (F : ι → ArithmeticFunction ℂ) (M : ι → ℝ) (Y : ℝ)
    (n : ℕ) :
    ‖mtProductScaleBoundaryErrorAF S F M Y n‖ ≤
      ∑ i ∈ S, ‖F i n‖ := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  rw [mtProductScaleBoundaryErrorAF_apply_of_pos S F M Y hn]
  split_ifs
  · exact (norm_sum_le _ _).trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _)
      (fun i hi hnot => norm_nonneg (F i n)))
  · rw [norm_neg]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _)
      (fun i hi hnot => norm_nonneg (F i n)))

/-- Dyadically supported boxes give the proposition's exact enlarged error support. -/
theorem mtProductScaleBoundaryErrorAF_support
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (F : ι → ArithmeticFunction ℂ) (M : ι → ℝ) (Y : ℝ)
    (hY : 0 < Y)
    (hsupport : ∀ i ∈ S, MTRealScaleSupported (F i) (M i) (2 * M i))
    {n : ℕ} (hn : mtProductScaleBoundaryErrorAF S F M Y n ≠ 0) :
    Y / 4 < (n : ℝ) ∧ (n : ℝ) ≤ 8 * Y := by
  have hnpos : 0 < n := by
    by_contra hn0
    have : n = 0 := Nat.eq_zero_of_not_pos hn0
    subst n
    simp at hn
  rw [mtProductScaleBoundaryErrorAF_apply_of_pos S F M Y hnpos] at hn
  by_cases hnY : Y / 2 < (n : ℝ) ∧ (n : ℝ) ≤ 4 * Y
  · rw [if_pos hnY] at hn
    have hexists : ∃ i ∈ S.filter
        (fun i => ¬(Y / 2 < M i ∧ M i ≤ 4 * Y)), F i n ≠ 0 := by
      by_contra hall
      apply hn
      apply Finset.sum_eq_zero
      intro i hi
      by_contra hFi
      exact hall ⟨i, hi, hFi⟩
    obtain ⟨i, hi, hFi⟩ := hexists
    have hiS := Finset.mem_filter.mp hi
    have hs := hsupport i hiS.1 hFi
    have hMiUpper : M i ≤ 4 * Y := hs.2.1.le.trans hnY.2
    have hMiLower : M i ≤ Y / 2 := by
      by_contra hnot
      exact hiS.2 ⟨lt_of_not_ge hnot, hMiUpper⟩
    refine ⟨(by linarith [hnY.1]), ?_⟩
    calc
      (n : ℝ) ≤ 2 * M i := hs.2.2
      _ ≤ 2 * (Y / 2) := mul_le_mul_of_nonneg_left hMiLower (by norm_num)
      _ ≤ 8 * Y := by linarith
  · rw [if_neg hnY] at hn
    have hsum : ∑ i ∈ mtProductScaleIndices S M Y, F i n ≠ 0 := by
      simpa using hn
    have hexists : ∃ i ∈ mtProductScaleIndices S M Y, F i n ≠ 0 := by
      by_contra hall
      apply hsum
      apply Finset.sum_eq_zero
      intro i hi
      by_contra hFi
      exact hall ⟨i, hi, hFi⟩
    obtain ⟨i, hi, hFi⟩ := hexists
    have hiData := Finset.mem_filter.mp hi
    have hs := hsupport i hiData.1 hFi
    have hnLower : Y / 2 < (n : ℝ) := hiData.2.1.trans hs.2.1
    have hnUpperTarget : 4 * Y < (n : ℝ) := by
      by_contra hnot
      exact hnY ⟨hnLower, le_of_not_gt hnot⟩
    refine ⟨(by linarith), ?_⟩
    calc
      (n : ℝ) ≤ 2 * M i := hs.2.2
      _ ≤ 2 * (4 * Y) := mul_le_mul_of_nonneg_left hiData.2.2 (by norm_num)
      _ = 8 * Y := by ring

/-- With an explicit common dilation, the product-scale error lies only in the two endpoint
collars.  This is the source's `c₂`-style boundary geometry. -/
theorem mtProductScaleBoundaryErrorAF_support_endpointCollars
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (F : ι → ArithmeticFunction ℂ) (M : ι → ℝ)
    (Y eta : ℝ) (heta : 0 ≤ eta)
    (hsupport : ∀ i ∈ S,
      MTRealScaleSupported (F i) (M i) ((1 + eta) * M i))
    {n : ℕ} (hn : mtProductScaleBoundaryErrorAF S F M Y n ≠ 0) :
    (Y / 2 < (n : ℝ) ∧ (n : ℝ) ≤ (1 + eta) * (Y / 2)) ∨
      (4 * Y < (n : ℝ) ∧ (n : ℝ) ≤ (1 + eta) * (4 * Y)) := by
  have hnpos : 0 < n := by
    by_contra hn0
    have : n = 0 := Nat.eq_zero_of_not_pos hn0
    subst n
    simp at hn
  rw [mtProductScaleBoundaryErrorAF_apply_of_pos S F M Y hnpos] at hn
  by_cases hnY : Y / 2 < (n : ℝ) ∧ (n : ℝ) ≤ 4 * Y
  · rw [if_pos hnY] at hn
    have hexists : ∃ i ∈ S.filter
        (fun i => ¬(Y / 2 < M i ∧ M i ≤ 4 * Y)), F i n ≠ 0 := by
      by_contra hall
      apply hn
      apply Finset.sum_eq_zero
      intro i hi
      by_contra hFi
      exact hall ⟨i, hi, hFi⟩
    obtain ⟨i, hi, hFi⟩ := hexists
    have hiData := Finset.mem_filter.mp hi
    have hs := hsupport i hiData.1 hFi
    have hMiUpper : M i ≤ 4 * Y := hs.2.1.le.trans hnY.2
    have hMiLower : M i ≤ Y / 2 := by
      by_contra hnot
      exact hiData.2 ⟨lt_of_not_ge hnot, hMiUpper⟩
    left
    refine ⟨hnY.1, ?_⟩
    calc
      (n : ℝ) ≤ (1 + eta) * M i := hs.2.2
      _ ≤ (1 + eta) * (Y / 2) :=
        mul_le_mul_of_nonneg_left hMiLower (by linarith)
  · rw [if_neg hnY] at hn
    have hsum : ∑ i ∈ mtProductScaleIndices S M Y, F i n ≠ 0 := by
      simpa using hn
    have hexists : ∃ i ∈ mtProductScaleIndices S M Y, F i n ≠ 0 := by
      by_contra hall
      apply hsum
      apply Finset.sum_eq_zero
      intro i hi
      by_contra hFi
      exact hall ⟨i, hi, hFi⟩
    obtain ⟨i, hi, hFi⟩ := hexists
    have hiData := Finset.mem_filter.mp hi
    have hs := hsupport i hiData.1 hFi
    have hnLower : Y / 2 < (n : ℝ) := hiData.2.1.trans hs.2.1
    have hnUpperTarget : 4 * Y < (n : ℝ) := by
      by_contra hnot
      exact hnY ⟨hnLower, le_of_not_gt hnot⟩
    right
    refine ⟨hnUpperTarget, ?_⟩
    calc
      (n : ℝ) ≤ (1 + eta) * M i := hs.2.2
      _ ≤ (1 + eta) * (4 * Y) :=
        mul_le_mul_of_nonneg_left hiData.2.2 (by linarith)

/-- Integer form of the two endpoint collars. -/
theorem mtProductScaleBoundaryErrorAF_mem_endpointCollars
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (F : ι → ArithmeticFunction ℂ) (M : ι → ℝ)
    (Y eta : ℝ) (hY : 0 < Y) (heta : 0 ≤ eta)
    (hsupport : ∀ i ∈ S,
      MTRealScaleSupported (F i) (M i) ((1 + eta) * M i))
    {n : ℕ} (hn : mtProductScaleBoundaryErrorAF S F M Y n ≠ 0) :
    n ∈ Finset.Ioc (Nat.floor (Y / 2))
        (Nat.floor ((1 + eta) * (Y / 2))) ∨
      n ∈ Finset.Ioc (Nat.floor (4 * Y))
        (Nat.floor ((1 + eta) * (4 * Y))) := by
  rcases mtProductScaleBoundaryErrorAF_support_endpointCollars
      S F M Y eta heta hsupport hn with hlower | hupper
  · left
    exact Finset.mem_Ioc.mpr ⟨
      (Nat.floor_lt (by positivity : 0 ≤ Y / 2)).mpr hlower.1,
      Nat.le_floor hlower.2⟩
  · right
    exact Finset.mem_Ioc.mpr ⟨
      (Nat.floor_lt (by positivity : 0 ≤ 4 * Y)).mpr hupper.1,
      Nat.le_floor hupper.2⟩

end

end RHTower.Sieve
