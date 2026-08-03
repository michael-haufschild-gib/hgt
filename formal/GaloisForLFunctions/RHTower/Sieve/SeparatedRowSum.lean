import GaloisForLFunctions.RHTower.Sieve.SeparatedPoints

/-!
# The row sum of reciprocal separations is harmonic

Summing the reciprocal separations of `SeparatedPoints.lean` over a whole Gram row reindexes to a
harmonic sum: the `i`-th term above (or below) a fixed index is separated by at least `(i+1)δ`, so

`∑_{s ≠ r, s < R} |λ_s - λ_r|^{-1} ≤ 2 δ^{-1} ∑_{i < R} (i+1)^{-1}`.

Both halves of the row are obtained from the same one-sided estimate, the lower half by reflecting
the range.

This is the quantitative form of the statement that bounding
`∑_{r≠s} x_r conj(x_s) (λ_r - λ_s)^{-1}` term by term cannot do better than `δ^{-1} log R`: the
harmonic sum on the right *is* the loss.  A sharp constant therefore has to come from cancellation
in that sum, not from the size of its terms.
-/

namespace RHTower.Sieve

open Finset

/-- Separated points are strictly increasing. -/
theorem lt_of_gap {lam : ℕ → ℝ} {δ : ℝ} (hδ : 0 < δ) (hgap : ∀ i, lam i + δ ≤ lam (i + 1))
    {r s : ℕ} (hrs : r < s) : lam r < lam s := by
  have hle := le_of_gap hgap r s (le_of_lt hrs)
  have hrsR : (1 : ℝ) ≤ (s : ℝ) - r := by
    have : (r : ℝ) + 1 ≤ (s : ℝ) := by exact_mod_cast hrs
    linarith
  nlinarith [hle, hrsR, hδ]

/-- **Harmonic row sum above a fixed index.** -/
theorem sum_inv_dist_le {lam : ℕ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ i, lam i + δ ≤ lam (i + 1)) (r R : ℕ) :
    ∑ s ∈ Finset.Ico (r + 1) R, 1 / (lam s - lam r)
      ≤ (1 / δ) * ∑ i ∈ Finset.range (R - (r + 1)), 1 / ((i : ℝ) + 1) := by
  rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hlt : r < r + 1 + i := by omega
  have hbase := inv_dist_le hδ hgap hlt
  have hcast : ((r + 1 + i : ℕ) : ℝ) - (r : ℝ) = (i : ℝ) + 1 := by
    push_cast
    ring
  rw [hcast] at hbase
  have hval : 1 / (((i : ℝ) + 1) * δ) = 1 / δ * (1 / ((i : ℝ) + 1)) := by
    field_simp
  rw [hval] at hbase
  exact hbase

/-- **Harmonic row sum below a fixed index.**  The lower half of the row is the reflection of the
upper half, so the same estimate applies after reindexing. -/
theorem sum_inv_dist_below_le {lam : ℕ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ i, lam i + δ ≤ lam (i + 1)) (r : ℕ) :
    ∑ s ∈ Finset.range r, 1 / (lam r - lam s)
      ≤ (1 / δ) * ∑ i ∈ Finset.range r, 1 / ((i : ℝ) + 1) := by
  rw [Finset.mul_sum, ← Finset.sum_range_reflect (fun s => 1 / (lam r - lam s)) r]
  refine Finset.sum_le_sum fun i hi => ?_
  have hir : i < r := Finset.mem_range.mp hi
  have hlt : r - 1 - i < r := by omega
  have hbase := inv_dist_le hδ hgap hlt
  have hnat : (r - 1 - i) + (i + 1) = r := by omega
  have hcast : (r : ℝ) - ((r - 1 - i : ℕ) : ℝ) = (i : ℝ) + 1 := by
    have := congrArg (fun n : ℕ => (n : ℝ)) hnat
    push_cast at this
    linarith
  rw [hcast] at hbase
  have hval : 1 / (((i : ℝ) + 1) * δ) = 1 / δ * (1 / ((i : ℝ) + 1)) := by
    field_simp
  rw [hval] at hbase
  exact hbase

/-- **The Gram row of a `δ`-separated family is bounded by a harmonic sum.** -/
theorem sum_inv_abs_dist_le {lam : ℕ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ i, lam i + δ ≤ lam (i + 1)) {r R : ℕ} (hr : r < R) :
    ∑ s ∈ (Finset.range R).erase r, 1 / |lam s - lam r|
      ≤ (2 / δ) * ∑ i ∈ Finset.range R, 1 / ((i : ℝ) + 1) := by
  have hsplit : (Finset.range R).erase r = Finset.range r ∪ Finset.Ico (r + 1) R := by
    ext s
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    omega
  have hdisj : Disjoint (Finset.range r) (Finset.Ico (r + 1) R) := by
    rw [Finset.disjoint_left]
    intro s hs hs'
    simp only [Finset.mem_range] at hs
    simp only [Finset.mem_Ico] at hs'
    omega
  rw [hsplit, Finset.sum_union hdisj]
  -- rewrite the two halves as signed differences
  have hlow : ∀ s ∈ Finset.range r, 1 / |lam s - lam r| = 1 / (lam r - lam s) := by
    intro s hs
    have hsr : s < r := Finset.mem_range.mp hs
    have := lt_of_gap hδ hgap hsr
    rw [abs_of_nonpos (by linarith)]
    ring_nf
  have hhigh : ∀ s ∈ Finset.Ico (r + 1) R, 1 / |lam s - lam r| = 1 / (lam s - lam r) := by
    intro s hs
    have hrs : r < s := by
      have := Finset.mem_Ico.mp hs
      omega
    have := lt_of_gap hδ hgap hrs
    rw [abs_of_nonneg (by linarith)]
  rw [Finset.sum_congr rfl hlow, Finset.sum_congr rfl hhigh]
  -- both halves are dominated by the full harmonic sum
  have hnonneg : ∀ i ∈ Finset.range R, i ∉ Finset.range r → (0 : ℝ) ≤ 1 / ((i : ℝ) + 1) := by
    intro i _ _
    positivity
  have hnonneg' : ∀ i ∈ Finset.range R, i ∉ Finset.range (R - (r + 1)) →
      (0 : ℝ) ≤ 1 / ((i : ℝ) + 1) := by
    intro i _ _
    positivity
  have hsub1 : Finset.range r ⊆ Finset.range R := by
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  have hsub2 : Finset.range (R - (r + 1)) ⊆ Finset.range R := by
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  have hH1 : ∑ i ∈ Finset.range r, 1 / ((i : ℝ) + 1)
      ≤ ∑ i ∈ Finset.range R, 1 / ((i : ℝ) + 1) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub1 hnonneg
  have hH2 : ∑ i ∈ Finset.range (R - (r + 1)), 1 / ((i : ℝ) + 1)
      ≤ ∑ i ∈ Finset.range R, 1 / ((i : ℝ) + 1) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub2 hnonneg'
  have hδinv : (0 : ℝ) ≤ 1 / δ := by positivity
  have hb1 := sum_inv_dist_below_le hδ hgap r
  have hb2 := sum_inv_dist_le hδ hgap r R
  have hfinal : (1 / δ) * ∑ i ∈ Finset.range R, 1 / ((i : ℝ) + 1)
      + (1 / δ) * ∑ i ∈ Finset.range R, 1 / ((i : ℝ) + 1)
      = (2 / δ) * ∑ i ∈ Finset.range R, 1 / ((i : ℝ) + 1) := by
    ring
  calc ∑ s ∈ Finset.range r, 1 / (lam r - lam s)
        + ∑ s ∈ Finset.Ico (r + 1) R, 1 / (lam s - lam r)
      ≤ (1 / δ) * ∑ i ∈ Finset.range r, 1 / ((i : ℝ) + 1)
        + (1 / δ) * ∑ i ∈ Finset.range (R - (r + 1)), 1 / ((i : ℝ) + 1) := by
        exact add_le_add hb1 hb2
    _ ≤ (1 / δ) * ∑ i ∈ Finset.range R, 1 / ((i : ℝ) + 1)
        + (1 / δ) * ∑ i ∈ Finset.range R, 1 / ((i : ℝ) + 1) := by
        exact add_le_add (mul_le_mul_of_nonneg_left hH1 hδinv)
          (mul_le_mul_of_nonneg_left hH2 hδinv)
    _ = (2 / δ) * ∑ i ∈ Finset.range R, 1 / ((i : ℝ) + 1) := hfinal

end RHTower.Sieve
