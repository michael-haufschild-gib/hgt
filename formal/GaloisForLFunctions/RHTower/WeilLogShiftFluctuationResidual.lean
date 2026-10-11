import GaloisForLFunctions.RHTower.WeilLogShiftActualVariance

/-! Centering the uniformly bounded index/correction discrepancy preserves its variance bound. -/

open scoped BigOperators

noncomputable section
namespace RHTower

def finiteWeilCanonicalFluctuationResidual (r k : ℕ) : ℝ :=
  ∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r k i *
    (((r + 1 : ℕ) : ℝ) *
      (finiteWeilCanonicalEdgeLogCorrection r k i - finiteWeilCanonicalLogTransportCorrection r k) -
      (((i : ℕ) : ℝ) - finiteWeilCanonicalEdgeIndexMean r k)) ^ 2

theorem finiteWeilCanonicalFluctuationResidual_nonneg (r k : ℕ) :
    0 ≤ finiteWeilCanonicalFluctuationResidual r k :=
  Finset.sum_nonneg fun i _ => mul_nonneg (finiteWeilCanonicalEdgeMass_pos r k i).le (sq_nonneg _)

theorem finiteWeilCanonicalEdgeLogCorrection_scaled_residual_mean (r k : ℕ) :
    (∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r k i *
      (((r + 1 : ℕ) : ℝ) * finiteWeilCanonicalEdgeLogCorrection r k i - (i : ℕ))) =
      ((r + 1 : ℕ) : ℝ) * finiteWeilCanonicalLogTransportCorrection r k -
        finiteWeilCanonicalEdgeIndexMean r k := by
  calc
    _ = ((r + 1 : ℕ) : ℝ) * (∑ i, finiteWeilCanonicalEdgeMass r k i *
        finiteWeilCanonicalEdgeLogCorrection r k i) -
        ∑ i, finiteWeilCanonicalEdgeMass r k i * ((i : ℕ) : ℝ) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by rw [finiteWeilCanonicalEdgeLogCorrection_mean]; rfl

theorem finiteWeilCanonicalFluctuationResidual_eq (r k : ℕ) :
    finiteWeilCanonicalFluctuationResidual r k =
      (∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r k i *
        (((r + 1 : ℕ) : ℝ) * finiteWeilCanonicalEdgeLogCorrection r k i - (i : ℕ)) ^ 2) -
      (((r + 1 : ℕ) : ℝ) * finiteWeilCanonicalLogTransportCorrection r k -
        finiteWeilCanonicalEdgeIndexMean r k) ^ 2 := by
  have h := finiteWeil_probability_centering (finiteWeilCanonicalEdgeMass r k)
    (fun i : Fin (r + 1) => ((r + 1 : ℕ) : ℝ) * finiteWeilCanonicalEdgeLogCorrection r k i - (i : ℕ))
    (finiteWeilCanonicalEdgeMass_sum r k) 0
  rw [finiteWeilCanonicalEdgeLogCorrection_scaled_residual_mean] at h
  calc
    _ = ∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r k i *
        ((((r + 1 : ℕ) : ℝ) * finiteWeilCanonicalEdgeLogCorrection r k i - (i : ℕ)) -
          (((r + 1 : ℕ) : ℝ) * finiteWeilCanonicalLogTransportCorrection r k -
            finiteWeilCanonicalEdgeIndexMean r k)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by simpa only [sub_zero] using h

theorem finiteWeilCanonicalFluctuationResidual_bound (r k : ℕ)
    (hwidth : ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ)) :
    finiteWeilCanonicalFluctuationResidual r k ≤ 1 := by
  have hraw : (∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r k i *
      (((r + 1 : ℕ) : ℝ) * finiteWeilCanonicalEdgeLogCorrection r k i - (i : ℕ)) ^ 2) ≤ 1 := by
    calc
      _ ≤ ∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r k i * 1 := by
        apply Finset.sum_le_sum
        intro i hi
        apply mul_le_mul_of_nonneg_left _ (finiteWeilCanonicalEdgeMass_pos r k i).le
        obtain ⟨hl, hu⟩ := abs_le.mp (finiteWeilCanonicalEdgeLogCorrection_scaled_index_bound r k i hwidth)
        have hp := mul_nonneg (sub_nonneg.mpr hu)
          (show 0 ≤ 1 + (((r + 1 : ℕ) : ℝ) * finiteWeilCanonicalEdgeLogCorrection r k i - (i : ℕ)) by
            linarith only [hl])
        nlinarith only [hp]
      _ = 1 := by simp only [mul_one, finiteWeilCanonicalEdgeMass_sum]
  rw [finiteWeilCanonicalFluctuationResidual_eq]
  linarith only [hraw, sq_nonneg (((r + 1 : ℕ) : ℝ) * finiteWeilCanonicalLogTransportCorrection r k -
    finiteWeilCanonicalEdgeIndexMean r k)]

theorem finiteWeilCanonicalFluctuationResidual_quadratic_bound (r t : ℕ) :
    finiteWeilCanonicalFluctuationResidual r (2 * (r + 1) ^ 2 + t) ≤ 1 := by
  apply finiteWeilCanonicalFluctuationResidual_bound
  push_cast
  nlinarith only [sq_nonneg ((r : ℝ) + 1), (Nat.cast_nonneg t : (0 : ℝ) ≤ t)]

end RHTower
