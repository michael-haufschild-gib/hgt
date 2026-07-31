import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Adaptive capacity saturation for countable Mercer features

A square-summable feature sequence has a diagonal tail tending to zero.  Therefore any family of
such sequences, weighted pointwise by finite nonnegative source costs, admits a finite rank at each
index whose residual diagonal is dominated by any prescribed positive summable budget.

This is the universal capacity law behind source-adaptive odd Jacobi cancellation.  It distinguishes
fixed-rank obstructions from genuine infinite-capacity obstructions without assuming a common rank,
a finite-dimensional ambient space, or a uniform convergence rate.
-/

noncomputable section

open Filter
open scoped BigOperators

namespace HTGeometry

variable {ι : Type*}

/-- Diagonal Mercer energy remaining after deleting the first `K` feature coordinates. -/
def adaptiveMercerDiagonalTail (a : ι → ℕ → ℝ) (K : ℕ) (i : ι) : ℝ :=
  ∑' n : ℕ, a i (n + K) ^ 2

theorem adaptiveMercerDiagonalTail_nonneg
    (a : ι → ℕ → ℝ) (K : ℕ) (i : ι) :
    0 ≤ adaptiveMercerDiagonalTail a K i := by
  unfold adaptiveMercerDiagonalTail
  exact tsum_nonneg fun _ => sq_nonneg _

/-- Every square-summable feature row is exhausted by increasing finite coordinate capacity. -/
theorem tendsto_adaptiveMercerDiagonalTail
    (a : ι → ℕ → ℝ) (i : ι)
    (_hsq : Summable fun n => a i n ^ 2) :
    Tendsto (fun K => adaptiveMercerDiagonalTail a K i) atTop (nhds 0) := by
  exact tendsto_sum_nat_add (fun n => a i n ^ 2)

/-- Coordinatewise residual after a label-dependent cutoff.  Coordinates are not reindexed:
different labels remain coupled through the same global feature coordinate. -/
def adaptiveMercerResidualFeature
    (a : ι → ℕ → ℝ) (capacity : ι → ℕ) (i : ι) (n : ℕ) : ℝ :=
  if n < capacity i then 0 else a i n

/-- Finite-coordinate Gram kernel of label-dependent Mercer residuals. -/
def adaptiveMercerFiniteResidualKernel
    (a : ι → ℕ → ℝ) (capacity : ι → ℕ) (N : ℕ) (i j : ι) : ℝ :=
  (Finset.range N).sum fun n =>
    adaptiveMercerResidualFeature a capacity i n *
      adaptiveMercerResidualFeature a capacity j n

/-- Infinite Gram kernel of label-dependent Mercer residuals. -/
def adaptiveMercerResidualKernel
    (a : ι → ℕ → ℝ) (capacity : ι → ℕ) (i j : ι) : ℝ :=
  ∑' n : ℕ,
    adaptiveMercerResidualFeature a capacity i n *
      adaptiveMercerResidualFeature a capacity j n

theorem summable_adaptiveMercerResidualFeature_sq
    (a : ι → ℕ → ℝ) (capacity : ι → ℕ) (i : ι)
    (hsq : Summable fun n => a i n ^ 2) :
    Summable fun n => adaptiveMercerResidualFeature a capacity i n ^ 2 := by
  exact Summable.of_nonneg_of_le
    (fun n => sq_nonneg (adaptiveMercerResidualFeature a capacity i n))
    (fun n => by
      unfold adaptiveMercerResidualFeature
      split_ifs
      · simpa using sq_nonneg (a i n)
      · exact le_rfl)
    hsq

/-- Cross-label residual products are absolutely summable from rowwise square summability. -/
theorem summable_adaptiveMercerResidualFeature_mul
    (a : ι → ℕ → ℝ) (capacity : ι → ℕ) (i j : ι)
    (hsqi : Summable fun n => a i n ^ 2)
    (hsqj : Summable fun n => a j n ^ 2) :
    Summable fun n =>
      adaptiveMercerResidualFeature a capacity i n *
        adaptiveMercerResidualFeature a capacity j n := by
  apply Summable.of_abs
  apply Summable.of_nonneg_of_le
    (f := fun n =>
      (adaptiveMercerResidualFeature a capacity i n ^ 2 +
        adaptiveMercerResidualFeature a capacity j n ^ 2) / 2)
    (fun n => abs_nonneg _)
  · intro n
    rw [abs_mul]
    have hsqdiff : 0 ≤
        (|adaptiveMercerResidualFeature a capacity i n| -
          |adaptiveMercerResidualFeature a capacity j n|) ^ 2 := sq_nonneg _
    have hi := sq_abs (adaptiveMercerResidualFeature a capacity i n)
    have hj := sq_abs (adaptiveMercerResidualFeature a capacity j n)
    nlinarith
  · exact ((summable_adaptiveMercerResidualFeature_sq a capacity i hsqi).add
      (summable_adaptiveMercerResidualFeature_sq a capacity j hsqj)).div_const 2

theorem tendsto_adaptiveMercerFiniteResidualKernel
    (a : ι → ℕ → ℝ) (capacity : ι → ℕ) (i j : ι)
    (hsqi : Summable fun n => a i n ^ 2)
    (hsqj : Summable fun n => a j n ^ 2) :
    Tendsto (fun N => adaptiveMercerFiniteResidualKernel a capacity N i j)
      atTop (nhds (adaptiveMercerResidualKernel a capacity i j)) := by
  exact (summable_adaptiveMercerResidualFeature_mul a capacity i j hsqi hsqj).hasSum
    |>.tendsto_sum_nat

/-- Diagonal of the coherent zero-padded residual kernel is exactly the shifted Mercer tail used
by adaptive capacity saturation. -/
theorem adaptiveMercerResidualKernel_self_eq_diagonalTail
    (a : ι → ℕ → ℝ) (capacity : ι → ℕ) (i : ι)
    (hsq : Summable fun n => a i n ^ 2) :
    adaptiveMercerResidualKernel a capacity i i =
      adaptiveMercerDiagonalTail a (capacity i) i := by
  have hr := summable_adaptiveMercerResidualFeature_sq a capacity i hsq
  have hsplit := hr.sum_add_tsum_nat_add (capacity i)
  rw [show (Finset.range (capacity i)).sum
      (fun n => adaptiveMercerResidualFeature a capacity i n ^ 2) = 0 by
    apply Finset.sum_eq_zero
    intro n hn
    simp only [adaptiveMercerResidualFeature,
      if_pos (Finset.mem_range.1 hn)]
    norm_num] at hsplit
  rw [zero_add] at hsplit
  rw [show (fun n =>
      adaptiveMercerResidualFeature a capacity i (n + capacity i) ^ 2) =
      fun n => a i (n + capacity i) ^ 2 by
    funext n
    simp only [adaptiveMercerResidualFeature,
      if_neg (Nat.not_lt_of_ge (Nat.le_add_left (capacity i) n))]] at hsplit
  unfold adaptiveMercerResidualKernel adaptiveMercerDiagonalTail
  rw [show (fun n => adaptiveMercerResidualFeature a capacity i n *
      adaptiveMercerResidualFeature a capacity i n) =
      fun n => adaptiveMercerResidualFeature a capacity i n ^ 2 by
    funext n
    rw [pow_two]]
  exact hsplit.symm

/-- Exact finite-packet energy identity for arbitrary label-dependent cutoffs. -/
theorem adaptiveMercerFiniteResidualKernel_quadraticForm_eq_sum_sq
    (a : ι → ℕ → ℝ) (capacity : ι → ℕ)
    (F : Finset ι) (N : ℕ) (z : ι → ℝ) :
    F.sum (fun i => F.sum (fun j =>
      z i * z j * adaptiveMercerFiniteResidualKernel a capacity N i j)) =
      (Finset.range N).sum (fun n =>
        (F.sum fun i =>
          z i * adaptiveMercerResidualFeature a capacity i n) ^ 2) := by
  let b : ι → ℕ → ℝ := fun i n =>
    z i * adaptiveMercerResidualFeature a capacity i n
  calc
    F.sum (fun i => F.sum (fun j =>
        z i * z j * adaptiveMercerFiniteResidualKernel a capacity N i j)) =
        F.sum (fun i => F.sum (fun j =>
          (Finset.range N).sum (fun n => b i n * b j n))) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      unfold adaptiveMercerFiniteResidualKernel b
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ = F.sum (fun i => (Finset.range N).sum (fun n =>
          F.sum (fun j => b i n * b j n))) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = (Finset.range N).sum (fun n =>
          F.sum (fun i => F.sum (fun j => b i n * b j n))) := by
      exact Finset.sum_comm
    _ = (Finset.range N).sum (fun n =>
        (F.sum fun i =>
          z i * adaptiveMercerResidualFeature a capacity i n) ^ 2) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [show F.sum (fun i => F.sum (fun j => b i n * b j n)) =
          (F.sum fun i => b i n) * (F.sum fun j => b j n) by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]]
      simp only [b]
      ring

theorem adaptiveMercerFiniteResidualKernel_psd
    (a : ι → ℕ → ℝ) (capacity : ι → ℕ)
    (F : Finset ι) (N : ℕ) (z : ι → ℝ) :
    0 ≤ F.sum (fun i => F.sum (fun j =>
      z i * z j * adaptiveMercerFiniteResidualKernel a capacity N i j)) := by
  rw [adaptiveMercerFiniteResidualKernel_quadraticForm_eq_sum_sq]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **Label-local cutoff coherence law.**  Arbitrary finite packets of label-dependent residuals
assemble into one positive semidefinite infinite kernel.  No common cutoff or uniform tail rate is
required. -/
theorem adaptiveMercerResidualKernel_psd
    (a : ι → ℕ → ℝ) (capacity : ι → ℕ)
    (hsq : ∀ i, Summable fun n => a i n ^ 2)
    (F : Finset ι) (z : ι → ℝ) :
    0 ≤ F.sum (fun i => F.sum (fun j =>
      z i * z j * adaptiveMercerResidualKernel a capacity i j)) := by
  have hlim : Tendsto
      (fun N => F.sum (fun i => F.sum (fun j =>
        z i * z j * adaptiveMercerFiniteResidualKernel a capacity N i j)))
      atTop
      (nhds (F.sum (fun i => F.sum (fun j =>
        z i * z j * adaptiveMercerResidualKernel a capacity i j)))) := by
    apply tendsto_finsetSum
    intro i hi
    apply tendsto_finsetSum
    intro j hj
    exact ((tendsto_adaptiveMercerFiniteResidualKernel
      a capacity i j (hsq i) (hsq j)).const_mul (z i * z j))
  exact ge_of_tendsto' hlim fun N =>
    adaptiveMercerFiniteResidualKernel_psd a capacity F N z

/-- **Adaptive Mercer capacity saturation law.**  For arbitrary index type, pointwise finite ranks
can push every weighted square-summable feature tail below any positive summable budget.  The
resulting residual diagonal is summable. -/
theorem exists_adaptiveMercerCapacity_of_summableBudget
    (a : ι → ℕ → ℝ) (weight budget : ι → ℝ)
    (hsq : ∀ i, Summable fun n => a i n ^ 2)
    (hweight : ∀ i, 0 ≤ weight i)
    (hbudgetPos : ∀ i, 0 < budget i)
    (hbudgetSummable : Summable budget) :
    ∃ capacity : ι → ℕ,
      (∀ i, weight i * adaptiveMercerDiagonalTail a (capacity i) i ≤ budget i) ∧
      Summable (fun i =>
        weight i * adaptiveMercerDiagonalTail a (capacity i) i) := by
  have hexists (i : ι) :
      ∃ K : ℕ, weight i * adaptiveMercerDiagonalTail a K i ≤ budget i := by
    have hlim := (tendsto_adaptiveMercerDiagonalTail a i (hsq i)).const_mul (weight i)
    have hevent : ∀ᶠ K in atTop,
        weight i * adaptiveMercerDiagonalTail a K i < budget i :=
      (tendsto_order.1 hlim).2 _ (by simpa using hbudgetPos i)
    obtain ⟨K, hK⟩ := hevent.exists
    exact ⟨K, hK.le⟩
  choose capacity hcapacity using hexists
  refine ⟨capacity, hcapacity, ?_⟩
  exact Summable.of_nonneg_of_le
    (fun i => mul_nonneg (hweight i)
      (adaptiveMercerDiagonalTail_nonneg a (capacity i) i))
    hcapacity hbudgetSummable

/-- Capacity saturation can always be chosen without sacrificing cross-label positivity. -/
theorem exists_adaptiveMercerPositiveKernelCapacity_of_summableBudget
    (a : ι → ℕ → ℝ) (weight budget : ι → ℝ)
    (hsq : ∀ i, Summable fun n => a i n ^ 2)
    (hweight : ∀ i, 0 ≤ weight i)
    (hbudgetPos : ∀ i, 0 < budget i)
    (hbudgetSummable : Summable budget) :
    ∃ capacity : ι → ℕ,
      (∀ i, weight i * adaptiveMercerDiagonalTail a (capacity i) i ≤ budget i) ∧
      Summable (fun i =>
        weight i * adaptiveMercerDiagonalTail a (capacity i) i) ∧
      ∀ (F : Finset ι) (z : ι → ℝ),
        0 ≤ F.sum (fun i => F.sum (fun j =>
          z i * z j * adaptiveMercerResidualKernel a capacity i j)) := by
  obtain ⟨capacity, hcapacity, hsummable⟩ :=
    exists_adaptiveMercerCapacity_of_summableBudget
      a weight budget hsq hweight hbudgetPos hbudgetSummable
  exact ⟨capacity, hcapacity, hsummable,
    adaptiveMercerResidualKernel_psd a capacity hsq⟩

end HTGeometry
