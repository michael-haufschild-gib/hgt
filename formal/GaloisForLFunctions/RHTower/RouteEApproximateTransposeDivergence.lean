import Mathlib.Tactic

/-!
# Route E approximate-transpose divergence law

Mix two complete row kernels intended to move in opposite numerical directions.  Their column-load
defect is not controlled by the existence of both directions.  It is exactly one half of the
discrete divergence of the mismatch between the second kernel and the transpose of the first.
Consequently the mixed column-load Dirichlet energy is exactly one quarter of the mismatch-
divergence energy.  Exact transpose reversal is available with complete reverse rows only when the
original columns already have unit load.
-/

namespace RHTower

open scoped BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- Outgoing mass of a finite real kernel. -/
def routeERowMass (P : ι → ι → ℝ) (i : ι) : ℝ :=
  ∑ j, P i j

/-- Incoming mass of a finite real kernel. -/
def routeEColumnMass (P : ι → ι → ℝ) (i : ι) : ℝ :=
  ∑ j, P j i

/-- Equal mixture of two finite kernels. -/
def routeEKernelAverage (P Q : ι → ι → ℝ) (i j : ι) : ℝ :=
  (P i j + Q i j) / 2

/-- Failure of `Q` to be the transpose of `P`. -/
def routeETransposeMismatch (P Q : ι → ι → ℝ) (i j : ι) : ℝ :=
  Q i j - P j i

/-- Outgoing minus incoming marginal of the approximate-transpose mismatch. -/
def routeEMismatchDivergence (P Q : ι → ι → ℝ) (i : ι) : ℝ :=
  (∑ j, routeETransposeMismatch P Q i j) -
    ∑ j, routeETransposeMismatch P Q j i

/-- Row normalization of an unnormalized physical incidence. -/
def routeERowNormalizedKernel (U : ι → ι → ℝ) (i j : ι) : ℝ :=
  U i j / routeERowMass U i

/-- Exact split of normalized up/down transpose mismatch into raw-incidence and normalizer terms. -/
def routeERawBidirectionalMismatch (U V : ι → ι → ℝ) (i j : ι) : ℝ :=
  (V i j - U j i) / routeERowMass V i +
    U j i * (1 / routeERowMass V i - 1 / routeERowMass U j)

/-- Divergence of the raw-incidence plus normalizer mismatch. -/
def routeERawBidirectionalMismatchDivergence
    (U V : ι → ι → ℝ) (i : ι) : ℝ :=
  (∑ j, routeERawBidirectionalMismatch U V i j) -
    ∑ j, routeERawBidirectionalMismatch U V j i

/-- A nonempty raw row becomes a complete normalized row. -/
theorem routeE_rowMass_rowNormalizedKernel_eq_one
    (U : ι → ι → ℝ) (i : ι) (hU : routeERowMass U i ≠ 0) :
    routeERowMass (routeERowNormalizedKernel U) i = 1 := by
  change (∑ j, U i j / routeERowMass U i) = 1
  rw [← Finset.sum_div]
  exact div_self hU

/-- Normalized transpose mismatch separates exactly into geometry and row-normalization mismatch. -/
theorem routeE_normalizedTransposeMismatch_eq_rawBidirectionalMismatch
    (U V : ι → ι → ℝ) (i j : ι) :
    routeETransposeMismatch
        (routeERowNormalizedKernel U) (routeERowNormalizedKernel V) i j =
      routeERawBidirectionalMismatch U V i j := by
  unfold routeETransposeMismatch routeERowNormalizedKernel routeERawBidirectionalMismatch
  ring

/-- The normalized mismatch divergence is the divergence of the two explicit raw terms. -/
theorem routeE_normalizedMismatchDivergence_eq_rawBidirectionalMismatchDivergence
    (U V : ι → ι → ℝ) (i : ι) :
    routeEMismatchDivergence
        (routeERowNormalizedKernel U) (routeERowNormalizedKernel V) i =
      routeERawBidirectionalMismatchDivergence U V i := by
  unfold routeEMismatchDivergence routeERawBidirectionalMismatchDivergence
  simp_rw [routeE_normalizedTransposeMismatch_eq_rawBidirectionalMismatch]

/-- Column defect of the bidirectional mixture is exactly half the mismatch divergence. -/
theorem routeE_one_sub_averageColumnMass_eq_half_mismatchDivergence
    (P Q : ι → ι → ℝ)
    (hP : ∀ i, routeERowMass P i = 1)
    (hQ : ∀ i, routeERowMass Q i = 1)
    (i : ι) :
    1 - routeEColumnMass (routeEKernelAverage P Q) i =
      (1 / 2 : ℝ) * routeEMismatchDivergence P Q i := by
  unfold routeEColumnMass routeEKernelAverage routeEMismatchDivergence
    routeETransposeMismatch routeERowMass at *
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_div, Finset.sum_add_distrib, hP i, hQ i]
  ring

/-- A load gradient of the mixture is the oppositely oriented mismatch-divergence gradient. -/
theorem routeE_averageColumnMass_sub_eq_half_mismatchDivergence_sub
    (P Q : ι → ι → ℝ)
    (hP : ∀ i, routeERowMass P i = 1)
    (hQ : ∀ i, routeERowMass Q i = 1)
    (i j : ι) :
    routeEColumnMass (routeEKernelAverage P Q) i -
        routeEColumnMass (routeEKernelAverage P Q) j =
      (1 / 2 : ℝ) *
        (routeEMismatchDivergence P Q j - routeEMismatchDivergence P Q i) := by
  have hi := routeE_one_sub_averageColumnMass_eq_half_mismatchDivergence P Q hP hQ i
  have hj := routeE_one_sub_averageColumnMass_eq_half_mismatchDivergence P Q hP hQ j
  linarith

/-- Pointwise squared load gradients are one quarter of squared mismatch-divergence gradients. -/
theorem routeE_averageColumnMass_gradient_sq_eq_quarter_mismatchDivergence_gradient_sq
    (P Q : ι → ι → ℝ)
    (hP : ∀ i, routeERowMass P i = 1)
    (hQ : ∀ i, routeERowMass Q i = 1)
    (i j : ι) :
    (routeEColumnMass (routeEKernelAverage P Q) i -
        routeEColumnMass (routeEKernelAverage P Q) j) ^ 2 =
      (1 / 4 : ℝ) *
        (routeEMismatchDivergence P Q i - routeEMismatchDivergence P Q j) ^ 2 := by
  rw [routeE_averageColumnMass_sub_eq_half_mismatchDivergence_sub P Q hP hQ]
  ring

/-- Exact weighted energy interface, with no positivity assumption on the reporter weights. -/
theorem routeE_weightedAverageColumnGradientEnergy_eq_quarterMismatchDivergenceEnergy
    (P Q : ι → ι → ℝ)
    (hP : ∀ i, routeERowMass P i = 1)
    (hQ : ∀ i, routeERowMass Q i = 1)
    (edges : Finset (ι × ι)) (weight : ι × ι → ℝ) :
    (∑ p ∈ edges, weight p *
      (routeEColumnMass (routeEKernelAverage P Q) p.1 -
        routeEColumnMass (routeEKernelAverage P Q) p.2) ^ 2) =
      (1 / 4 : ℝ) * ∑ p ∈ edges, weight p *
        (routeEMismatchDivergence P Q p.1 -
          routeEMismatchDivergence P Q p.2) ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _hp
  rw [routeE_averageColumnMass_gradient_sq_eq_quarter_mismatchDivergence_gradient_sq
    P Q hP hQ]
  ring

/-- For row-normalized physical incidences, load-gradient energy is exactly the divergence energy
of raw shifted-incidence discrepancy plus local row-normalizer discrepancy. -/
theorem routeE_normalizedBidirectionalColumnGradientEnergy_eq_quarterRawMismatchDivergenceEnergy
    (U V : ι → ι → ℝ)
    (hU : ∀ i, routeERowMass U i ≠ 0)
    (hV : ∀ i, routeERowMass V i ≠ 0)
    (edges : Finset (ι × ι)) (weight : ι × ι → ℝ) :
    (∑ p ∈ edges, weight p *
      (routeEColumnMass
          (routeEKernelAverage
            (routeERowNormalizedKernel U) (routeERowNormalizedKernel V)) p.1 -
        routeEColumnMass
          (routeEKernelAverage
            (routeERowNormalizedKernel U) (routeERowNormalizedKernel V)) p.2) ^ 2) =
      (1 / 4 : ℝ) * ∑ p ∈ edges, weight p *
        (routeERawBidirectionalMismatchDivergence U V p.1 -
          routeERawBidirectionalMismatchDivergence U V p.2) ^ 2 := by
  rw [routeE_weightedAverageColumnGradientEnergy_eq_quarterMismatchDivergenceEnergy
    (routeERowNormalizedKernel U) (routeERowNormalizedKernel V)
    (fun i => routeE_rowMass_rowNormalizedKernel_eq_one U i (hU i))
    (fun i => routeE_rowMass_rowNormalizedKernel_eq_one V i (hV i))]
  apply congrArg ((1 / 4 : ℝ) * ·)
  apply Finset.sum_congr rfl
  intro p _hp
  rw [routeE_normalizedMismatchDivergence_eq_rawBidirectionalMismatchDivergence,
    routeE_normalizedMismatchDivergence_eq_rawBidirectionalMismatchDivergence]

/-- Pointwise absolute column defect is bounded by incoming plus outgoing mismatch mass. -/
theorem routeE_abs_one_sub_averageColumnMass_le_mismatchL1
    (P Q : ι → ι → ℝ)
    (hP : ∀ i, routeERowMass P i = 1)
    (hQ : ∀ i, routeERowMass Q i = 1)
    (i : ι) :
    |1 - routeEColumnMass (routeEKernelAverage P Q) i| ≤
      (1 / 2 : ℝ) *
        ((∑ j, |routeETransposeMismatch P Q i j|) +
          ∑ j, |routeETransposeMismatch P Q j i|) := by
  rw [routeE_one_sub_averageColumnMass_eq_half_mismatchDivergence P Q hP hQ,
    abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  unfold routeEMismatchDivergence
  calc
    |(∑ j, routeETransposeMismatch P Q i j) -
        ∑ j, routeETransposeMismatch P Q j i| ≤
        |∑ j, routeETransposeMismatch P Q i j| +
          |∑ j, routeETransposeMismatch P Q j i| := abs_sub _ _
    _ ≤ (∑ j, |routeETransposeMismatch P Q i j|) +
          ∑ j, |routeETransposeMismatch P Q j i| := by
      gcongr
      · exact Finset.abs_sum_le_sum_abs _ _
      · exact Finset.abs_sum_le_sum_abs _ _

/-- Total column defect is at most total approximate-transpose mismatch. -/
theorem routeE_sum_abs_one_sub_averageColumnMass_le_totalMismatchL1
    (P Q : ι → ι → ℝ)
    (hP : ∀ i, routeERowMass P i = 1)
    (hQ : ∀ i, routeERowMass Q i = 1) :
    (∑ i, |1 - routeEColumnMass (routeEKernelAverage P Q) i|) ≤
      ∑ i, ∑ j, |routeETransposeMismatch P Q i j| := by
  calc
    (∑ i, |1 - routeEColumnMass (routeEKernelAverage P Q) i|) ≤
        ∑ i, (1 / 2 : ℝ) *
          ((∑ j, |routeETransposeMismatch P Q i j|) +
            ∑ j, |routeETransposeMismatch P Q j i|) :=
      Finset.sum_le_sum fun i _hi =>
        routeE_abs_one_sub_averageColumnMass_le_mismatchL1 P Q hP hQ i
    _ = ∑ i, ∑ j, |routeETransposeMismatch P Q i j| := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      rw [Finset.sum_comm]
      ring

/-- Exact transpose reversal with complete reverse rows forces the original columns to be full. -/
theorem routeE_columnMass_eq_one_of_transpose_rowMass
    (P Q : ι → ι → ℝ)
    (hQ : ∀ i, routeERowMass Q i = 1)
    (htranspose : ∀ i j, Q i j = P j i)
    (i : ι) :
    routeEColumnMass P i = 1 := by
  calc
    routeEColumnMass P i = ∑ j, P j i := rfl
    _ = ∑ j, Q i j := by
      apply Finset.sum_congr rfl
      intro j _hj
      exact (htranspose i j).symm
    _ = routeERowMass Q i := rfl
    _ = 1 := hQ i

end

end RHTower
