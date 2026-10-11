import GaloisForLFunctions.RHTower.WeilLogShiftEdgeVarianceScale
import GaloisForLFunctions.RHTower.WeilLogShiftEdgeCorrectionMoment

/-! The transport correction and the edge index share the same fluctuation scale. -/

open scoped BigOperators

namespace RHTower

theorem finiteWeilCanonicalEdge_centered_first_moment_bound (r k : ℕ)
    (hwidth : 2 * ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ)) :
    (∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r k i * |((i : ℕ) : ℝ) - (r : ℝ) / 2|) ≤
      4 * Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) := by
  let n : ℝ := ((r + 1 : ℕ) : ℝ)
  let S := Real.sqrt ((n + 1) / 2)
  let x := fun i : Fin (r + 1) => ((i : ℕ) : ℝ) - (r : ℝ) / 2
  have hn1 : 1 ≤ n := by dsimp [n]; exact_mod_cast (show 1 ≤ r + 1 by omega)
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hS2 : S ^ 2 = (n + 1) / 2 := Real.sq_sqrt (by positivity)
  have hSn : S ≤ n := by nlinarith only [hS0, hS2, hn1, sq_nonneg (n - 1)]
  have hr : (r : ℝ) + 1 = n := by simp only [n, Nat.cast_add, Nat.cast_one]
  have hH := (abs_le.mp (finiteWeilCanonicalEdgeCenteredSecondMoment_sharp_bound r k hwidth)).2
  change finiteWeilCanonicalEdgeCenteredSecondMoment r k - (r : ℝ) / 4 ≤ 4 * S at hH
  have hHsq : finiteWeilCanonicalEdgeCenteredSecondMoment r k ≤ (4 * S) ^ 2 := by
    nlinarith only [hH, hSn, hS2, hr, hn1]
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset (Fin (r + 1)))
    (r := fun i => finiteWeilCanonicalEdgeMass r k i * |x i|)
    (f := finiteWeilCanonicalEdgeMass r k) (g := fun i => finiteWeilCanonicalEdgeMass r k i * x i ^ 2)
    (fun i _ => (finiteWeilCanonicalEdgeMass_pos r k i).le)
    (fun i _ => mul_nonneg (finiteWeilCanonicalEdgeMass_pos r k i).le (sq_nonneg _))
    (fun i _ => le_of_eq (by rw [mul_pow, sq_abs]; ring))
  rw [finiteWeilCanonicalEdgeMass_sum, one_mul] at hcs
  change (∑ i, finiteWeilCanonicalEdgeMass r k i * |x i|) ^ 2 ≤
    finiteWeilCanonicalEdgeCenteredSecondMoment r k at hcs
  change (∑ i, finiteWeilCanonicalEdgeMass r k i * |x i|) ≤ 4 * S
  nlinarith only [hcs, hHsq, hS0]

theorem finiteWeilCanonicalEdgeLogCorrectionSecondMoment_raw_comparison (r k : ℕ)
    (hwidth : 2 * ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ)) :
    |((r + 1 : ℕ) : ℝ) ^ 2 * finiteWeilCanonicalEdgeLogCorrectionSecondMoment r k -
      finiteWeilCanonicalEdgeCenteredSecondMoment r k| ≤
        16 * Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) := by
  let n : ℝ := ((r + 1 : ℕ) : ℝ)
  let S := Real.sqrt ((n + 1) / 2)
  let x := fun i : Fin (r + 1) => ((i : ℕ) : ℝ) - (r : ℝ) / 2
  have hn1 : 1 ≤ n := by dsimp [n]; exact_mod_cast (show 1 ≤ r + 1 by omega)
  have hS : 1 ≤ S := by
    have hs0 := Real.sqrt_nonneg ((n + 1) / 2)
    have hs2 := Real.sq_sqrt (show 0 ≤ (n + 1) / 2 by positivity)
    change 1 ≤ Real.sqrt ((n + 1) / 2)
    nlinarith only [hs0, hs2, hn1]
  have hw : ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ) := by
    nlinarith only [hwidth, sq_nonneg (((r + 1 : ℕ) : ℝ))]
  have halg (a z : ℝ) (hz : |z| ≤ 3 / 2) : |(a + z) ^ 2 - a ^ 2| ≤ 3 * |a| + 4 := by
    obtain ⟨hz0, hz1⟩ := abs_le.mp hz
    have hp := mul_nonneg (show 0 ≤ z + 3 / 2 by linarith only [hz0])
      (show 0 ≤ 3 / 2 - z by linarith only [hz1])
    have hmul := mul_le_mul_of_nonneg_left hz (show 0 ≤ 2 * |a| by positivity)
    rw [show (a + z) ^ 2 - a ^ 2 = 2 * a * z + z ^ 2 by ring]
    calc
      _ ≤ |2 * a * z| + |z ^ 2| := abs_add_le _ _
      _ = 2 * |a| * |z| + z ^ 2 := by
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg (sq_nonneg z)]
      _ ≤ _ := by nlinarith only [hmul, hp]
  have hpoint (i : Fin (r + 1)) :
      |(n * (finiteWeilCanonicalEdgeLogCorrection r k i - 1 / 2)) ^ 2 - x i ^ 2| ≤ 3 * |x i| + 4 := by
    have hi := finiteWeilCanonicalEdgeLogCorrection_scaled_index_bound r k i hw
    have hz : |n * finiteWeilCanonicalEdgeLogCorrection r k i - (i : ℕ) - 1 / 2| ≤ 3 / 2 := by
      obtain ⟨hl, hu⟩ := abs_le.mp hi
      exact abs_le.mpr ⟨by linarith only [hl], by linarith only [hu]⟩
    have h := halg (x i) (n * finiteWeilCanonicalEdgeLogCorrection r k i - (i : ℕ) - 1 / 2) hz
    have hid : x i + (n * finiteWeilCanonicalEdgeLogCorrection r k i - (i : ℕ) - 1 / 2) =
        n * (finiteWeilCanonicalEdgeLogCorrection r k i - 1 / 2) := by
      dsimp [x, n]
      push_cast
      ring
    rwa [hid] at h
  have hid : n ^ 2 * finiteWeilCanonicalEdgeLogCorrectionSecondMoment r k -
      finiteWeilCanonicalEdgeCenteredSecondMoment r k =
      ∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r k i *
        ((n * (finiteWeilCanonicalEdgeLogCorrection r k i - 1 / 2)) ^ 2 - x i ^ 2) := by
    unfold finiteWeilCanonicalEdgeLogCorrectionSecondMoment finiteWeilCanonicalEdgeCenteredSecondMoment
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [x]
    ring
  change |n ^ 2 * finiteWeilCanonicalEdgeLogCorrectionSecondMoment r k -
    finiteWeilCanonicalEdgeCenteredSecondMoment r k| ≤ 16 * S
  rw [hid]
  calc
    _ ≤ ∑ i : Fin (r + 1), |finiteWeilCanonicalEdgeMass r k i *
        ((n * (finiteWeilCanonicalEdgeLogCorrection r k i - 1 / 2)) ^ 2 - x i ^ 2)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r k i *
        |(n * (finiteWeilCanonicalEdgeLogCorrection r k i - 1 / 2)) ^ 2 - x i ^ 2| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul, abs_of_pos (finiteWeilCanonicalEdgeMass_pos r k i)]
    _ ≤ ∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r k i * (3 * |x i| + 4) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hpoint i) (finiteWeilCanonicalEdgeMass_pos r k i).le
    _ = 3 * (∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r k i * |x i|) + 4 := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
      rw [finiteWeilCanonicalEdgeMass_sum, one_mul, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ _ := by
      have hb := finiteWeilCanonicalEdge_centered_first_moment_bound r k hwidth
      change (∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r k i * |x i|) ≤ 4 * S at hb
      linarith only [hb, hS]

theorem finiteWeilCanonicalEdgeLogCorrectionSecondMoment_scaled_comparison (r k : ℕ)
    (hwidth : 2 * ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ)) :
    |((r + 1 : ℕ) : ℝ) * finiteWeilCanonicalEdgeLogCorrectionSecondMoment r k -
      finiteWeilCanonicalEdgeCenteredSecondMoment r k / ((r + 1 : ℕ) : ℝ)| ≤
        16 * (Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) / ((r + 1 : ℕ) : ℝ)) := by
  have hn : (0 : ℝ) < ((r + 1 : ℕ) : ℝ) := by positivity
  have hid : ((r + 1 : ℕ) : ℝ) * finiteWeilCanonicalEdgeLogCorrectionSecondMoment r k -
      finiteWeilCanonicalEdgeCenteredSecondMoment r k / ((r + 1 : ℕ) : ℝ) =
      (((r + 1 : ℕ) : ℝ) ^ 2 * finiteWeilCanonicalEdgeLogCorrectionSecondMoment r k -
        finiteWeilCanonicalEdgeCenteredSecondMoment r k) / ((r + 1 : ℕ) : ℝ) := by field_simp
  rw [hid, abs_div, abs_of_pos hn]
  calc
    _ ≤ (16 * Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2)) / ((r + 1 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right (finiteWeilCanonicalEdgeLogCorrectionSecondMoment_raw_comparison r k hwidth) hn.le
    _ = _ := by ring

end RHTower
