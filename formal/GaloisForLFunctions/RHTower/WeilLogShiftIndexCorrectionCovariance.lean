import GaloisForLFunctions.RHTower.WeilLogShiftFluctuationResidual

/-! The centered discrepancy determines the mixed covariance exactly. -/

open scoped BigOperators

noncomputable section
namespace RHTower

def finiteWeilCanonicalIndexCorrectionCovariance (r k : ℕ) : ℝ :=
  ∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r k i *
    (((i : ℕ) : ℝ) - finiteWeilCanonicalEdgeIndexMean r k) *
    (finiteWeilCanonicalEdgeLogCorrection r k i - finiteWeilCanonicalLogTransportCorrection r k)

theorem finiteWeilCanonicalIndexCorrectionCovariance_sq_le_variances (r k : ℕ) :
    finiteWeilCanonicalIndexCorrectionCovariance r k ^ 2 ≤
      finiteWeilCanonicalEdgeIndexVariance r k * finiteWeilCanonicalEdgeLogCorrectionVariance r k := by
  let m := finiteWeilCanonicalEdgeMass r k
  let x := fun i : Fin (r + 1) => ((i : ℕ) : ℝ) - finiteWeilCanonicalEdgeIndexMean r k
  let y := fun i : Fin (r + 1) =>
    finiteWeilCanonicalEdgeLogCorrection r k i - finiteWeilCanonicalLogTransportCorrection r k
  change (∑ i, m i * x i * y i) ^ 2 ≤ (∑ i, m i * x i ^ 2) * ∑ i, m i * y i ^ 2
  exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset (Fin (r + 1)))
    (r := fun i => m i * x i * y i) (f := fun i => m i * x i ^ 2) (g := fun i => m i * y i ^ 2)
    (fun i _ => mul_nonneg (finiteWeilCanonicalEdgeMass_pos r k i).le (sq_nonneg _))
    (fun i _ => mul_nonneg (finiteWeilCanonicalEdgeMass_pos r k i).le (sq_nonneg _))
    (fun i _ => le_of_eq (by ring))

theorem finiteWeilCanonicalFluctuationResidual_covariance_eq (r k : ℕ) :
    finiteWeilCanonicalFluctuationResidual r k =
      ((r + 1 : ℕ) : ℝ) ^ 2 * finiteWeilCanonicalEdgeLogCorrectionVariance r k +
      finiteWeilCanonicalEdgeIndexVariance r k -
      (2 * ((r + 1 : ℕ) : ℝ)) * finiteWeilCanonicalIndexCorrectionCovariance r k := by
  simp only [finiteWeilCanonicalFluctuationResidual, finiteWeilCanonicalEdgeLogCorrectionVariance,
    finiteWeilCanonicalEdgeIndexVariance, finiteWeilCanonicalIndexCorrectionCovariance,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem finiteWeilCanonicalFluctuationResidual_normalized_eq (r k : ℕ) :
    finiteWeilCanonicalFluctuationResidual r k / ((r + 1 : ℕ) : ℝ) =
      ((r + 1 : ℕ) : ℝ) * finiteWeilCanonicalEdgeLogCorrectionVariance r k +
      finiteWeilCanonicalEdgeIndexVariance r k / ((r + 1 : ℕ) : ℝ) -
      2 * finiteWeilCanonicalIndexCorrectionCovariance r k := by
  have hn : (((r + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  rw [finiteWeilCanonicalFluctuationResidual_covariance_eq]
  field_simp

end RHTower
