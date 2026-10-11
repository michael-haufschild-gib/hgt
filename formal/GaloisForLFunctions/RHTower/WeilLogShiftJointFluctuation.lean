import GaloisForLFunctions.RHTower.WeilLogShiftFluctuationCorrelation

/-! Every linear combination of normalized index and correction fluctuations has a rank-one limit. -/

open scoped BigOperators
open Filter Topology

noncomputable section
namespace RHTower

def finiteWeilCanonicalJointFluctuation (r k : ℕ) (a b : ℝ) : ℝ :=
  (∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r k i *
    (a * (((i : ℕ) : ℝ) - finiteWeilCanonicalEdgeIndexMean r k) +
      b * ((r + 1 : ℕ) : ℝ) *
        (finiteWeilCanonicalEdgeLogCorrection r k i - finiteWeilCanonicalLogTransportCorrection r k)) ^ 2) /
    ((r + 1 : ℕ) : ℝ)

theorem finiteWeilCanonicalJointFluctuation_nonneg (r k : ℕ) (a b : ℝ) :
    0 ≤ finiteWeilCanonicalJointFluctuation r k a b :=
  div_nonneg (Finset.sum_nonneg fun i _ =>
    mul_nonneg (finiteWeilCanonicalEdgeMass_pos r k i).le (sq_nonneg _)) (by positivity)

theorem finiteWeilCanonicalJointFluctuation_eq (r k : ℕ) (a b : ℝ) :
    finiteWeilCanonicalJointFluctuation r k a b =
      a ^ 2 * (finiteWeilCanonicalEdgeIndexVariance r k / ((r + 1 : ℕ) : ℝ)) +
      (2 * a * b) * finiteWeilCanonicalIndexCorrectionCovariance r k +
      b ^ 2 * (((r + 1 : ℕ) : ℝ) * finiteWeilCanonicalEdgeLogCorrectionVariance r k) := by
  have hn : (((r + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hexpand : (∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r k i *
      (a * (((i : ℕ) : ℝ) - finiteWeilCanonicalEdgeIndexMean r k) +
        b * ((r + 1 : ℕ) : ℝ) *
          (finiteWeilCanonicalEdgeLogCorrection r k i - finiteWeilCanonicalLogTransportCorrection r k)) ^ 2) =
      a ^ 2 * finiteWeilCanonicalEdgeIndexVariance r k +
      (2 * a * b * ((r + 1 : ℕ) : ℝ)) * finiteWeilCanonicalIndexCorrectionCovariance r k +
      (b ^ 2 * ((r + 1 : ℕ) : ℝ) ^ 2) * finiteWeilCanonicalEdgeLogCorrectionVariance r k := by
    simp only [finiteWeilCanonicalEdgeIndexVariance, finiteWeilCanonicalIndexCorrectionCovariance,
      finiteWeilCanonicalEdgeLogCorrectionVariance, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  unfold finiteWeilCanonicalJointFluctuation
  rw [hexpand]
  field_simp

theorem tendsto_finiteWeilCanonicalJointFluctuation_rank_one (t : ℕ → ℕ) (a b : ℝ) :
    Tendsto (fun r : ℕ => finiteWeilCanonicalJointFluctuation r (2 * (r + 1) ^ 2 + t r) a b)
      atTop (𝓝 ((a + b) ^ 2 / 4)) := by
  have h := (((tendsto_finiteWeilCanonicalEdgeIndexVariance_quarter t).const_mul (a ^ 2)).add
    ((tendsto_finiteWeilCanonicalIndexCorrectionCovariance_quarter t).const_mul (2 * a * b))).add
    ((tendsto_finiteWeilCanonicalEdgeLogCorrectionVariance_quarter t).const_mul (b ^ 2))
  convert h using 1
  · funext r
    exact finiteWeilCanonicalJointFluctuation_eq r _ a b
  · congr 1
    ring

end RHTower
