import GaloisForLFunctions.RHTower.WeilLogShiftTransportDeficit

/-! A quantitative bridge from logarithmic transport to the normalized edge mean. -/

noncomputable section
namespace RHTower

def finiteWeilCanonicalLogTransportCorrection (r k : ℕ) : ℝ :=
  (((k + 2 : ℕ) : ℝ) / ((r + 1 : ℕ) : ℝ)) *
    (1 - ((k + 2 : ℕ) : ℝ) * finiteWeilCanonicalLogTransportCost r k)

theorem finiteWeilCanonicalLogTransportCorrection_mean_bound (r k : ℕ)
    (hwidth : ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ)) :
    |finiteWeilCanonicalLogTransportCorrection r k -
      finiteWeilCanonicalEdgeIndexMean r k / ((r + 1 : ℕ) : ℝ)| ≤ 1 / ((r + 1 : ℕ) : ℝ) := by
  let A : ℝ := ((k + 2 : ℕ) : ℝ)
  let n : ℝ := ((r + 1 : ℕ) : ℝ)
  let D : ℝ := 1 - A * finiteWeilCanonicalLogTransportCost r k
  have hA : 0 < A := by dsimp [A]; positivity
  have hn : 0 < n := by dsimp [n]; positivity
  have hr : (r : ℝ) + 1 = n := by simp [n]
  have hU : ((k + r + 3 : ℕ) : ℝ) = A + n := by dsimp [A, n]; push_cast; ring
  have hD : 0 ≤ D := by
    have hb := (le_div_iff₀ hA).mp (finiteWeilCanonicalLogTransportCost_bounds r k).2
    dsimp [D]
    nlinarith only [hb]
  have he := (finiteWeilCanonicalEdgeIndexMean_bounds r k).2
  obtain ⟨hl, hu⟩ := finiteWeilCanonicalLogTransportCost_deficit_bounds r k
  change finiteWeilCanonicalEdgeIndexMean r k ≤ ((k + r + 3 : ℕ) : ℝ) * D at hl
  change A * D ≤ finiteWeilCanonicalEdgeIndexMean r k + 1 at hu
  rw [hU] at hl
  have hsq : n * (n * D) ≤ n * 1 := by
    have hw := mul_le_mul_of_nonneg_right hwidth hD
    change n ^ 2 * D ≤ A * D at hw
    nlinarith only [hw, hu, he, hr]
  have hnD : n * D ≤ 1 := by
    by_contra! h
    have hp := mul_pos hn (sub_pos.mpr h)
    nlinarith only [hsq, hp]
  have herr : |A * D - finiteWeilCanonicalEdgeIndexMean r k| ≤ 1 := by
    apply abs_le.mpr
    constructor
    · nlinarith only [hl, hnD]
    · linarith only [hu]
  change |A / n * D - finiteWeilCanonicalEdgeIndexMean r k / n| ≤ 1 / n
  have hid : A / n * D - finiteWeilCanonicalEdgeIndexMean r k / n =
      (A * D - finiteWeilCanonicalEdgeIndexMean r k) / n := by ring
  rw [hid, abs_div, abs_of_nonneg hn.le]
  exact div_le_div_of_nonneg_right herr hn.le

theorem finiteWeilCanonicalLogTransportCorrection_quadratic_mean_bound (r t : ℕ) :
    |finiteWeilCanonicalLogTransportCorrection r (2 * (r + 1) ^ 2 + t) -
      finiteWeilCanonicalEdgeIndexMean r (2 * (r + 1) ^ 2 + t) / ((r + 1 : ℕ) : ℝ)| ≤
      1 / ((r + 1 : ℕ) : ℝ) := by
  apply finiteWeilCanonicalLogTransportCorrection_mean_bound
  push_cast
  have ht : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg _
  nlinarith only [ht, sq_nonneg ((r : ℝ) + 1)]

end RHTower
