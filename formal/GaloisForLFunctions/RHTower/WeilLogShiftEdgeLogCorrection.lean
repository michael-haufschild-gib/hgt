import GaloisForLFunctions.RHTower.WeilLogShiftTransportCorrection

/-! Local first corrections lie in the unit interval and track normalized edge indices. -/

open scoped BigOperators

noncomputable section
namespace RHTower

def finiteWeilCanonicalEdgeLogCorrection (r k : ℕ) (i : Fin (r + 1)) : ℝ :=
  (((k + 2 : ℕ) : ℝ) / ((r + 1 : ℕ) : ℝ)) *
    (1 - ((k + 2 : ℕ) : ℝ) *
      (finiteWeilClusterLogNodes r k i.succ - finiteWeilClusterLogNodes r k i.castSucc))

theorem finiteWeilCanonicalEdgeLogCorrection_mem_Icc (r k : ℕ) (i : Fin (r + 1)) :
    finiteWeilCanonicalEdgeLogCorrection r k i ∈ Set.Icc (0 : ℝ) 1 := by
  let A : ℝ := ((k + 2 : ℕ) : ℝ)
  let n : ℝ := ((r + 1 : ℕ) : ℝ)
  let g := finiteWeilClusterLogNodes r k i.succ - finiteWeilClusterLogNodes r k i.castSucc
  have hn : 0 < n := by dsimp [n]; positivity
  have hi : ((i : ℕ) : ℝ) + 1 ≤ n := by
    dsimp [n]
    exact_mod_cast (show (i : ℕ) + 1 ≤ r + 1 by have := i.isLt; omega)
  have hg : 0 < g := sub_pos.mpr (finiteWeilClusterLogNodes_strictMono r k
    (show i.castSucc < i.succ from by change i.val < i.val + 1; omega))
  have hl := (finiteWeilClusterLogNodes_adjacent_index_bounds r k i).1
  change (A + (i : ℕ)) * g ≤ 1 at hl
  have hD : 0 ≤ 1 - A * g := by
    have hm := mul_nonneg (Nat.cast_nonneg (i : ℕ)) hg.le
    nlinarith only [hl, hm]
  have hu := (finiteWeilClusterLogNodes_adjacent_deficit_bounds r k i).2
  change A * (1 - A * g) ≤ (i : ℕ) + 1 at hu
  have hid : finiteWeilCanonicalEdgeLogCorrection r k i = A * (1 - A * g) / n := by
    unfold finiteWeilCanonicalEdgeLogCorrection
    dsimp [A, n, g]
    ring
  rw [hid]
  constructor
  · exact div_nonneg (mul_nonneg (by dsimp [A]; positivity) hD) hn.le
  · apply (div_le_iff₀ hn).mpr
    linarith only [hu, hi]

theorem finiteWeilCanonicalEdgeLogCorrection_scaled_index_bound (r k : ℕ) (i : Fin (r + 1))
    (hwidth : ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ)) :
    |((r + 1 : ℕ) : ℝ) * finiteWeilCanonicalEdgeLogCorrection r k i - (i : ℕ)| ≤ 1 := by
  let A : ℝ := ((k + 2 : ℕ) : ℝ)
  let n : ℝ := ((r + 1 : ℕ) : ℝ)
  let D : ℝ := 1 - A *
    (finiteWeilClusterLogNodes r k i.succ - finiteWeilClusterLogNodes r k i.castSucc)
  have hA : 0 < A := by dsimp [A]; positivity
  have hn : 0 < n := by dsimp [n]; positivity
  have hi : ((i : ℕ) : ℝ) + 1 ≤ n := by
    dsimp [n]
    exact_mod_cast (show (i : ℕ) + 1 ≤ r + 1 by have := i.isLt; omega)
  have hscale : n * finiteWeilCanonicalEdgeLogCorrection r k i = A * D := by
    change n * (A / n * D) = A * D
    field_simp
  have hD : 0 ≤ D := by
    have hc := (finiteWeilCanonicalEdgeLogCorrection_mem_Icc r k i).1
    have hAD := mul_nonneg hn.le hc
    rw [hscale] at hAD
    by_contra! h
    have hp := mul_neg_of_pos_of_neg hA h
    linarith only [hAD, hp]
  obtain ⟨hl, hu⟩ := finiteWeilClusterLogNodes_adjacent_deficit_bounds r k i
  change ((i : ℕ) : ℝ) ≤ ((k + r + 3 : ℕ) : ℝ) * D at hl
  change A * D ≤ (i : ℕ) + 1 at hu
  have hU : ((k + r + 3 : ℕ) : ℝ) = A + n := by dsimp [A, n]; push_cast; ring
  rw [hU] at hl
  have hsq : n * (n * D) ≤ n := by
    have hw := mul_le_mul_of_nonneg_right hwidth hD
    change n ^ 2 * D ≤ A * D at hw
    nlinarith only [hw, hu, hi]
  have hnD : n * D ≤ 1 := by
    by_contra! h
    have hp := mul_pos hn (sub_pos.mpr h)
    nlinarith only [hsq, hp]
  change |n * finiteWeilCanonicalEdgeLogCorrection r k i - (i : ℕ)| ≤ 1
  rw [hscale]
  exact abs_le.mpr ⟨by nlinarith only [hl, hnD], by linarith only [hu]⟩

theorem finiteWeilCanonicalEdgeLogCorrection_index_bound (r k : ℕ) (i : Fin (r + 1))
    (hwidth : ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ)) :
    |finiteWeilCanonicalEdgeLogCorrection r k i - ((i : ℕ) : ℝ) / ((r + 1 : ℕ) : ℝ)| ≤
      1 / ((r + 1 : ℕ) : ℝ) := by
  have hn : (0 : ℝ) < ((r + 1 : ℕ) : ℝ) := by positivity
  have hid : finiteWeilCanonicalEdgeLogCorrection r k i - ((i : ℕ) : ℝ) / ((r + 1 : ℕ) : ℝ) =
      (((r + 1 : ℕ) : ℝ) * finiteWeilCanonicalEdgeLogCorrection r k i - (i : ℕ)) /
        ((r + 1 : ℕ) : ℝ) := by field_simp
  rw [hid, abs_div, abs_of_nonneg hn.le]
  exact div_le_div_of_nonneg_right
    (finiteWeilCanonicalEdgeLogCorrection_scaled_index_bound r k i hwidth) hn.le

theorem finiteWeilCanonicalEdgeLogCorrection_mean (r k : ℕ) :
    (∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r k i * finiteWeilCanonicalEdgeLogCorrection r k i) =
      finiteWeilCanonicalLogTransportCorrection r k :=
  finiteWeilCanonicalLogTransportCost_deficit_average r k _

end RHTower
