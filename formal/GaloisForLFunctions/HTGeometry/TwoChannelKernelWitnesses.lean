import GaloisForLFunctions.HTGeometry.TwoChannelRelativeCapacityNoGo

/-!
# Pairwise nonnegative two-channel kernels exist

The two-channel capacity laws assume that every pair of indices contributes a nonnegative
channel-linear current.  That is exactly two-by-two positive semidefiniteness of the kernel along
each pair: nonnegative diagonal and mixed entries dominated by the diagonal product.

Every Gram kernel of a real weight family satisfies it, with the current an exact square, so the
laws are not vacuous and hold on a class that separates the two channels genuinely.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Pairwise two-by-two positive semidefiniteness suffices.**  A nonnegative diagonal whose
mixed entries are dominated in square by the diagonal product makes every channel-linear current
nonnegative. -/
theorem pairwiseNonnegativeKernel_of_diagonal_nonneg_of_sq_le
    {ι : Type*} {kernel : ι → ι → ℝ}
    (hdiag : ∀ i, 0 ≤ kernel i i)
    (hmix : ∀ i j, kernel i j ^ (2 : ℕ) ≤ kernel i i * kernel j j) :
    PairwiseNonnegativeKernel kernel := by
  intro i j x y
  rw [twoChannelLinearCurrent]
  rcases eq_or_lt_of_le (hdiag i) with h | h
  · have hb : kernel i j ^ (2 : ℕ) ≤ 0 := by
      have := hmix i j
      rw [← h, zero_mul] at this
      exact this
    have hb0 : kernel i j = 0 := by nlinarith [sq_nonneg (kernel i j)]
    rw [← h, hb0]
    nlinarith [sq_nonneg y, hdiag j]
  · nlinarith [sq_nonneg (kernel i i * x + kernel i j * y), sq_nonneg y, hmix i j, h]

/-- **Every Gram kernel is pairwise nonnegative.**  Its channel-linear current is the square of the
weighted aggregate. -/
theorem pairwiseNonnegativeKernel_gram {ι : Type*} (v : ι → ℝ) :
    PairwiseNonnegativeKernel (fun i j => v i * v j) := by
  refine pairwiseNonnegativeKernel_of_diagonal_nonneg_of_sq_le (fun i => ?_) (fun i j => ?_)
  · exact mul_self_nonneg (v i)
  · nlinarith [sq_nonneg (v i), sq_nonneg (v j)]

/-- The current of a Gram kernel is an exact square. -/
theorem twoChannelLinearCurrent_gram {ι : Type*} (v : ι → ℝ) (i j : ι) (x y : ℝ) :
    twoChannelLinearCurrent (v i * v i) (v i * v j) (v j * v j) x y =
      (v i * x + v j * y) ^ (2 : ℕ) := by
  rw [twoChannelLinearCurrent]
  ring

/-- The zero kernel is pairwise nonnegative. -/
theorem pairwiseNonnegativeKernel_zero {ι : Type*} :
    PairwiseNonnegativeKernel (fun _ _ : ι => (0 : ℝ)) := by
  simpa using pairwiseNonnegativeKernel_gram (fun _ : ι => (0 : ℝ))

/-- The all-ones kernel is pairwise nonnegative, with current the squared total mass. -/
theorem pairwiseNonnegativeKernel_one {ι : Type*} :
    PairwiseNonnegativeKernel (fun _ _ : ι => (1 : ℝ)) := by
  simpa using pairwiseNonnegativeKernel_gram (fun _ : ι => (1 : ℝ))

end

end GaloisForLFunctions.HTGeometry
