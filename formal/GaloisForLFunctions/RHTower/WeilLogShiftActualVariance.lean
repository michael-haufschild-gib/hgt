import GaloisForLFunctions.RHTower.WeilLogShiftEdgeCorrectionMoment

/-! Actual-mean variances and their exact fixed-center decompositions. -/

open scoped BigOperators

noncomputable section
namespace RHTower

theorem finiteWeil_probability_centering {ι : Type} [Fintype ι]
    (w f : ι → ℝ) (hm : ∑ i, w i = 1) (c : ℝ) :
    (∑ i, w i * (f i - ∑ j, w j * f j) ^ 2) =
      (∑ i, w i * (f i - c) ^ 2) - ((∑ i, w i * f i) - c) ^ 2 := by
  let μ := ∑ i, w i * f i
  have hexpand (z : ℝ) : (∑ i, w i * (f i - z) ^ 2) =
      (∑ i, w i * f i ^ 2) - 2 * z * μ + z ^ 2 := by
    calc
      _ = ∑ i, (w i * f i ^ 2 - (2 * z) * (w i * f i) + z ^ 2 * w i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hm, mul_one]
  change (∑ i, w i * (f i - μ) ^ 2) = (∑ i, w i * (f i - c) ^ 2) - (μ - c) ^ 2
  rw [hexpand, hexpand]
  ring

def finiteWeilCanonicalEdgeIndexVariance (r k : ℕ) : ℝ :=
  ∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r k i *
    (((i : ℕ) : ℝ) - finiteWeilCanonicalEdgeIndexMean r k) ^ 2

def finiteWeilCanonicalEdgeLogCorrectionVariance (r k : ℕ) : ℝ :=
  ∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r k i *
    (finiteWeilCanonicalEdgeLogCorrection r k i - finiteWeilCanonicalLogTransportCorrection r k) ^ 2

theorem finiteWeilCanonicalEdgeIndexVariance_nonneg (r k : ℕ) :
    0 ≤ finiteWeilCanonicalEdgeIndexVariance r k :=
  Finset.sum_nonneg fun i _ => mul_nonneg (finiteWeilCanonicalEdgeMass_pos r k i).le (sq_nonneg _)

theorem finiteWeilCanonicalEdgeLogCorrectionVariance_nonneg (r k : ℕ) :
    0 ≤ finiteWeilCanonicalEdgeLogCorrectionVariance r k :=
  Finset.sum_nonneg fun i _ => mul_nonneg (finiteWeilCanonicalEdgeMass_pos r k i).le (sq_nonneg _)

theorem finiteWeilCanonicalEdgeIndexVariance_eq (r k : ℕ) :
    finiteWeilCanonicalEdgeIndexVariance r k = finiteWeilCanonicalEdgeCenteredSecondMoment r k -
      (finiteWeilCanonicalEdgeIndexMean r k - (r : ℝ) / 2) ^ 2 := by
  exact finiteWeil_probability_centering (finiteWeilCanonicalEdgeMass r k)
    (fun i : Fin (r + 1) => ((i : ℕ) : ℝ)) (finiteWeilCanonicalEdgeMass_sum r k) ((r : ℝ) / 2)

theorem finiteWeilCanonicalEdgeLogCorrectionVariance_eq (r k : ℕ) :
    finiteWeilCanonicalEdgeLogCorrectionVariance r k = finiteWeilCanonicalEdgeLogCorrectionSecondMoment r k -
      (finiteWeilCanonicalLogTransportCorrection r k - 1 / 2) ^ 2 := by
  have h := finiteWeil_probability_centering (finiteWeilCanonicalEdgeMass r k)
    (finiteWeilCanonicalEdgeLogCorrection r k) (finiteWeilCanonicalEdgeMass_sum r k) (1 / 2)
  simpa only [finiteWeilCanonicalEdgeLogCorrectionVariance,
    finiteWeilCanonicalEdgeLogCorrectionSecondMoment, finiteWeilCanonicalEdgeLogCorrection_mean] using h

end RHTower
