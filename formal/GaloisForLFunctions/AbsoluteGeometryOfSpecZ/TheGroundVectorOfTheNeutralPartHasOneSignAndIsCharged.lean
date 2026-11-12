import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.WeilsFormOnStepPacketsIsTheChargesAPotentialAndADirichletForm

/-!
# The ground vector of the neutral part has one sign and is charged

The neutral part `N` of the block matrix has negative entries off the diagonal: jets and
contacts attract. Hence:

* replacing `σ` by `|σ|` lowers the form of `N` strictly when `σ` has entries of both signs
  (`sum_neutralBlock_abs_lt`);
* a vector that minimises the form of `N` among the vectors of its length has entries of one
  sign (`neutral_minimizer_one_sign`);
* such a vector, if not zero, has both charges `c₀ = Σ σ_j` and `c₁ = Σ σ_j d(R + j)` different
  from zero and of one sign (`charges_mul_pos_of_neutral_minimizer`), so the product of the
  charges is positive on it and the block matrix is strictly above its neutral part there
  (`sum_neutralBlock_lt_sum_blockMatrix_of_minimizer`).

So the direction in which the neutral part is lowest is the direction in which the hyperbolic
plane of the charges is positive.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-- The degree of a block is positive. -/
theorem blockDegree_pos {a : ℕ} (ha : 1 ≤ a) : 0 < blockDegree a := by
  unfold blockDegree
  exact sub_pos.mpr
    (Real.log_lt_log (Nat.cast_pos.mpr ha) (Nat.cast_lt.mpr (Nat.lt_succ_self a)))

/-- Termwise, the modulus does not raise the neutral part. -/
theorem abs_mul_neutralBlock_le (Q R : ℕ) (σ : ℕ → ℝ) (j l : ℕ) :
    |σ j| * |σ l| * neutralBlock Q (R + j) (R + l) ≤
      σ j * σ l * neutralBlock Q (R + j) (R + l) := by
  by_cases hjl : j = l
  · subst hjl
    rw [abs_mul_abs_self]
  · have hneg := neutralBlock_neg (show R + j ≠ R + l by omega) Q
    have habs : σ j * σ l ≤ |σ j| * |σ l| := by
      rw [← abs_mul]
      exact le_abs_self _
    nlinarith

/-- **The modulus lowers the neutral part strictly on a vector with entries of both signs.** -/
theorem sum_neutralBlock_abs_lt (Q R J : ℕ) (σ : ℕ → ℝ) {j₀ l₀ : ℕ} (hj : j₀ < J) (hl : l₀ < J)
    (hpos : 0 < σ j₀) (hneg : σ l₀ < 0) :
    ∑ j ∈ range J, ∑ l ∈ range J, |σ j| * |σ l| * neutralBlock Q (R + j) (R + l) <
      ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * neutralBlock Q (R + j) (R + l) := by
  have hne : j₀ ≠ l₀ := by
    rintro rfl
    exact lt_asymm hpos hneg
  have hN := neutralBlock_neg (show R + j₀ ≠ R + l₀ by omega) Q
  refine Finset.sum_lt_sum
    (fun j _ => Finset.sum_le_sum fun l _ => abs_mul_neutralBlock_le Q R σ j l)
    ⟨j₀, Finset.mem_range.mpr hj,
      Finset.sum_lt_sum (fun l _ => abs_mul_neutralBlock_le Q R σ j₀ l)
        ⟨l₀, Finset.mem_range.mpr hl, ?_⟩⟩
  rw [abs_of_pos hpos, abs_of_neg hneg]
  have h := mul_pos (mul_pos hpos (neg_pos.mpr hneg)) (neg_pos.mpr hN)
  nlinarith [h]

/-- **A minimiser of the neutral part among the vectors of its length has entries of one
sign.** -/
theorem neutral_minimizer_one_sign {Q R J : ℕ} {σ : ℕ → ℝ}
    (hmin : ∀ τ : ℕ → ℝ, ∑ j ∈ range J, τ j ^ 2 = ∑ j ∈ range J, σ j ^ 2 →
      ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * neutralBlock Q (R + j) (R + l) ≤
        ∑ j ∈ range J, ∑ l ∈ range J, τ j * τ l * neutralBlock Q (R + j) (R + l)) :
    (∀ j, j < J → 0 ≤ σ j) ∨ (∀ j, j < J → σ j ≤ 0) := by
  by_contra h
  rw [not_or] at h
  obtain ⟨h1, h2⟩ := h
  push Not at h1 h2
  obtain ⟨l₀, hl, hneg⟩ := h1
  obtain ⟨j₀, hj, hpos⟩ := h2
  have hlt := sum_neutralBlock_abs_lt Q R J σ hj hl hpos hneg
  have hle := hmin (fun j => |σ j|) (Finset.sum_congr rfl fun j _ => sq_abs (σ j))
  exact absurd hle (not_le.mpr hlt)

/-- A vector with entries of one sign, not all zero, has two positive charges. -/
theorem charges_pos_of_nonneg {R J : ℕ} (hR : 1 ≤ R) {σ : ℕ → ℝ}
    (h0 : ∀ j, j < J → 0 ≤ σ j) {j₀ : ℕ} (hj : j₀ < J) (hpos : 0 < σ j₀) :
    0 < ∑ j ∈ range J, σ j ∧ 0 < ∑ j ∈ range J, σ j * blockDegree (R + j) := by
  constructor
  · exact Finset.sum_pos' (fun j hj' => h0 j (Finset.mem_range.mp hj'))
      ⟨j₀, Finset.mem_range.mpr hj, hpos⟩
  · exact Finset.sum_pos'
      (fun j hj' => mul_nonneg (h0 j (Finset.mem_range.mp hj'))
        (blockDegree_pos (a := R + j) (by omega)).le)
      ⟨j₀, Finset.mem_range.mpr hj, mul_pos hpos (blockDegree_pos (a := R + j₀) (by omega))⟩

/-- **A ground vector of the neutral part is charged**: both charges are different from zero
and have one sign. -/
theorem charges_mul_pos_of_neutral_minimizer {Q R J : ℕ} (hR : 1 ≤ R) {σ : ℕ → ℝ}
    (hmin : ∀ τ : ℕ → ℝ, ∑ j ∈ range J, τ j ^ 2 = ∑ j ∈ range J, σ j ^ 2 →
      ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * neutralBlock Q (R + j) (R + l) ≤
        ∑ j ∈ range J, ∑ l ∈ range J, τ j * τ l * neutralBlock Q (R + j) (R + l))
    {j₀ : ℕ} (hj : j₀ < J) (hne : σ j₀ ≠ 0) :
    0 < (∑ j ∈ range J, σ j) * (∑ j ∈ range J, σ j * blockDegree (R + j)) := by
  rcases neutral_minimizer_one_sign hmin with h | h
  · obtain ⟨h1, h2⟩ := charges_pos_of_nonneg hR h hj (lt_of_le_of_ne (h j₀ hj) hne.symm)
    exact mul_pos h1 h2
  · obtain ⟨h1, h2⟩ := charges_pos_of_nonneg (σ := fun j => -σ j) hR
      (fun j hj' => neg_nonneg.mpr (h j hj')) hj
      (neg_pos.mpr (lt_of_le_of_ne (h j₀ hj) hne))
    have h1' : ∑ j ∈ range J, σ j < 0 := by
      have : ∑ j ∈ range J, -σ j = -∑ j ∈ range J, σ j := Finset.sum_neg_distrib _
      rw [this] at h1
      exact neg_pos.mp h1
    have h2' : ∑ j ∈ range J, σ j * blockDegree (R + j) < 0 := by
      have : ∑ j ∈ range J, -σ j * blockDegree (R + j) =
          -∑ j ∈ range J, σ j * blockDegree (R + j) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun j _ => neg_mul _ _
      rw [this] at h2
      exact neg_pos.mp h2
    exact mul_pos_of_neg_of_neg h1' h2'

/-- **On a ground vector of the neutral part the block matrix is strictly above its neutral
part**: the product of the charges is positive there. -/
theorem sum_neutralBlock_lt_sum_blockMatrix_of_minimizer {Q R J : ℕ} (hR : 1 ≤ R) {σ : ℕ → ℝ}
    (hmin : ∀ τ : ℕ → ℝ, ∑ j ∈ range J, τ j ^ 2 = ∑ j ∈ range J, σ j ^ 2 →
      ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * neutralBlock Q (R + j) (R + l) ≤
        ∑ j ∈ range J, ∑ l ∈ range J, τ j * τ l * neutralBlock Q (R + j) (R + l))
    {j₀ : ℕ} (hj : j₀ < J) (hne : σ j₀ ≠ 0) :
    ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * neutralBlock Q (R + j) (R + l) <
      ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * blockMatrix Q (R + j) (R + l) := by
  have h := charges_mul_pos_of_neutral_minimizer hR hmin hj hne
  rw [sum_blockMatrix_eq_charges_add_neutral]
  linarith

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
