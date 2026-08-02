import GaloisForLFunctions.RHTower.MobiusMultiplicativeRectangleCubature

/-!
# Exact block-defect compression for the Möbius Gibbs current

Replacing every atom by the left representative of a block of width `h` changes the exponentially
weighted sum by at most the sum of the pointwise Lipschitz costs.  The representative sum then
regroups exactly into one signed defect coefficient per block.

For atoms in a dyadic interval of length `O(U)`, Gibbs scale `x = O(U⁻¹)`, and block width
`h = U^(1/2-o(1))`, the resulting error is sub-square-root.  Consequently an almost-all theorem
about small individual block defects cannot be substituted for cancellation of the signed
block-defect current: the latter is the exact compressed source object.
-/

open scoped BigOperators

namespace RHTower

/-- Moving one exponential atom rightward by at most `h` costs at most its left-endpoint
first-order majorant. -/
theorem abs_exp_neg_mul_sub_blockRepresentative_le
    {x r n h : ℝ} (hx : 0 ≤ x) (hrn : r ≤ n) (hwidth : n - r ≤ h) :
    |Real.exp (-(x * n)) - Real.exp (-(x * r))| ≤
      x * h * Real.exp (-(x * r)) := by
  let d := n - r
  have hd0 : 0 ≤ d := sub_nonneg.mpr hrn
  have hdh : d ≤ h := hwidth
  have hxn : Real.exp (-(x * n)) ≤ Real.exp (-(x * r)) := by
    gcongr
  rw [abs_of_nonpos (sub_nonpos.mpr hxn)]
  have hfactor :
      Real.exp (-(x * r)) - Real.exp (-(x * n)) =
        Real.exp (-(x * r)) * (1 - Real.exp (-(x * d))) := by
    have hn : n = r + d := by simp [d]
    rw [hn, show -(x * (r + d)) = -(x * r) + -(x * d) by ring, Real.exp_add]
    ring
  rw [show -(Real.exp (-(x * n)) - Real.exp (-(x * r))) =
    Real.exp (-(x * r)) - Real.exp (-(x * n)) by ring, hfactor]
  have hone : 1 - Real.exp (-(x * d)) ≤ x * d := by
    linarith [Real.add_one_le_exp (-(x * d))]
  calc
    Real.exp (-(x * r)) * (1 - Real.exp (-(x * d)))
        ≤ Real.exp (-(x * r)) * (x * d) := by
          exact mul_le_mul_of_nonneg_left hone (Real.exp_pos _).le
    _ ≤ Real.exp (-(x * r)) * (x * h) := by
      gcongr
    _ = x * h * Real.exp (-(x * r)) := by ring

/-- Summed complex form of the block-replacement error, valid for arbitrary coefficients of norm
at most one. -/
theorem norm_sum_atom_sub_blockRepresentative_le
    {ι : Type*} (s : Finset ι) (a : ι → ℂ) (n r : ι → ℝ)
    {x h : ℝ} (hx : 0 ≤ x)
    (ha : ∀ i ∈ s, ‖a i‖ ≤ 1)
    (hrn : ∀ i ∈ s, r i ≤ n i)
    (hwidth : ∀ i ∈ s, n i - r i ≤ h) :
    ‖∑ i ∈ s, a i *
        ((Real.exp (-(x * n i)) : ℂ) - Real.exp (-(x * r i)))‖ ≤
      ∑ i ∈ s, x * h * Real.exp (-(x * r i)) := by
  calc
    ‖∑ i ∈ s, a i *
        ((Real.exp (-(x * n i)) : ℂ) - Real.exp (-(x * r i)))‖
        ≤ ∑ i ∈ s, ‖a i *
          ((Real.exp (-(x * n i)) : ℂ) - Real.exp (-(x * r i)))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ s, x * h * Real.exp (-(x * r i)) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul]
      have hnorm :
          ‖((Real.exp (-(x * n i)) : ℂ) - Real.exp (-(x * r i)))‖ =
            |Real.exp (-(x * n i)) - Real.exp (-(x * r i))| := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      rw [hnorm]
      calc
        ‖a i‖ * |Real.exp (-(x * n i)) - Real.exp (-(x * r i))|
            ≤ 1 * |Real.exp (-(x * n i)) - Real.exp (-(x * r i))| := by
              exact mul_le_mul_of_nonneg_right (ha i hi) (abs_nonneg _)
        _ ≤ x * h * Real.exp (-(x * r i)) := by
          simpa using abs_exp_neg_mul_sub_blockRepresentative_le
            hx (hrn i hi) (hwidth i hi)

/-- Exact finite regrouping: a representative-weighted atom sum is the current of its signed block
defects. -/
theorem sum_atom_eq_sum_blockDefect_mul_weight
    {ι β : Type*} [DecidableEq β]
    (s : Finset ι) (a : ι → ℂ) (block : ι → β) (weight : β → ℂ) :
    ∑ i ∈ s, a i * weight (block i) =
      ∑ j ∈ s.image block, (∑ i ∈ s with block i = j, a i) * weight j := by
  have hmap : ∀ i ∈ s, block i ∈ s.image block :=
    fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap
    (fun i => a i * weight (block i))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_filter] at hi
  rw [hi.2]

/-- Exact block-defect compression theorem: the original Gibbs sum differs from the signed
block-defect current by only the explicit block-replacement budget. -/
theorem norm_atom_sum_sub_blockDefectCurrent_le
    {ι β : Type*} [DecidableEq β]
    (s : Finset ι) (a : ι → ℂ) (n : ι → ℝ)
    (block : ι → β) (representative : β → ℝ)
    {x h : ℝ} (hx : 0 ≤ x)
    (ha : ∀ i ∈ s, ‖a i‖ ≤ 1)
    (hrn : ∀ i ∈ s, representative (block i) ≤ n i)
    (hwidth : ∀ i ∈ s, n i - representative (block i) ≤ h) :
    ‖(∑ i ∈ s, a i * (Real.exp (-(x * n i)) : ℂ)) -
        ∑ j ∈ s.image block,
          (∑ i ∈ s with block i = j, a i) *
            (Real.exp (-(x * representative j)) : ℂ)‖ ≤
      ∑ i ∈ s, x * h * Real.exp (-(x * representative (block i))) := by
  rw [← sum_atom_eq_sum_blockDefect_mul_weight s a block
    (fun j => (Real.exp (-(x * representative j)) : ℂ))]
  rw [← Finset.sum_sub_distrib]
  simpa [mul_sub] using norm_sum_atom_sub_blockRepresentative_le
    s a n (fun i => representative (block i)) hx ha hrn hwidth

end RHTower
