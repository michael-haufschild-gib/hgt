import GaloisForLFunctions.RHTower.WeilLogShiftEdgeLogCorrection
import GaloisForLFunctions.RHTower.WeilLogShiftEdgeConcentration

/-! Edge-index concentration forces mean-square concentration of the local log correction. -/

open scoped BigOperators

noncomputable section
namespace RHTower

def finiteWeilCanonicalEdgeLogCorrectionSecondMoment (r k : ℕ) : ℝ :=
  ∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r k i *
    (finiteWeilCanonicalEdgeLogCorrection r k i - 1 / 2) ^ 2

theorem finiteWeilCanonicalEdgeLogCorrectionSecondMoment_nonneg (r k : ℕ) :
    0 ≤ finiteWeilCanonicalEdgeLogCorrectionSecondMoment r k :=
  Finset.sum_nonneg fun i _ => mul_nonneg (finiteWeilCanonicalEdgeMass_pos r k i).le (by positivity)

theorem finiteWeilCanonicalEdgeLogCorrectionSecondMoment_edge_bound (r k : ℕ)
    (hwidth : ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ)) :
    finiteWeilCanonicalEdgeLogCorrectionSecondMoment r k ≤
      (4 * finiteWeilCanonicalEdgeCenteredSecondMoment r k + 4) / ((r + 1 : ℕ) : ℝ) ^ 2 := by
  let n : ℝ := ((r + 1 : ℕ) : ℝ)
  have hn : 0 < n := by dsimp [n]; positivity
  have halg (x z : ℝ) (hz : |z| ≤ 1) : (z + x - 1 / 2) ^ 2 ≤ 4 * x ^ 2 + 4 := by
    obtain ⟨hz0, hz1⟩ := abs_le.mp hz
    have hp := mul_nonneg (show 0 ≤ z + 1 by linarith only [hz0])
      (show 0 ≤ 1 - z by linarith only [hz1])
    nlinarith only [hp, sq_nonneg (z - (x - 1 / 2)), sq_nonneg (x + 1 / 2)]
  have hpoint (i : Fin (r + 1)) :
      (finiteWeilCanonicalEdgeLogCorrection r k i - 1 / 2) ^ 2 ≤
        (4 * (((i : ℕ) : ℝ) - (r : ℝ) / 2) ^ 2 + 4) / n ^ 2 := by
    have hs := halg (((i : ℕ) : ℝ) - (r : ℝ) / 2)
      (n * finiteWeilCanonicalEdgeLogCorrection r k i - (i : ℕ))
      (finiteWeilCanonicalEdgeLogCorrection_scaled_index_bound r k i hwidth)
    have hid : n * finiteWeilCanonicalEdgeLogCorrection r k i - (i : ℕ) +
        (((i : ℕ) : ℝ) - (r : ℝ) / 2) - 1 / 2 =
        n * (finiteWeilCanonicalEdgeLogCorrection r k i - 1 / 2) := by
      dsimp [n]
      push_cast
      ring
    rw [hid] at hs
    apply (le_div_iff₀ (sq_pos_of_pos hn)).mpr
    nlinarith only [hs]
  calc
    _ ≤ ∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r k i *
        ((4 * (((i : ℕ) : ℝ) - (r : ℝ) / 2) ^ 2 + 4) / n ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hpoint i) (finiteWeilCanonicalEdgeMass_pos r k i).le
    _ = (∑ i : Fin (r + 1), (4 * (finiteWeilCanonicalEdgeMass r k i *
        (((i : ℕ) : ℝ) - (r : ℝ) / 2) ^ 2) + 4 * finiteWeilCanonicalEdgeMass r k i)) / n ^ 2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, finiteWeilCanonicalEdgeMass_sum, mul_one]
      rfl

theorem finiteWeilCanonicalEdgeLogCorrectionSecondMoment_quadratic_bound (r t : ℕ) :
    finiteWeilCanonicalEdgeLogCorrectionSecondMoment r (2 * (r + 1) ^ 2 + t) ≤
      8 * (Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) / ((r + 1 : ℕ) : ℝ)) := by
  let n : ℝ := ((r + 1 : ℕ) : ℝ)
  let S : ℝ := Real.sqrt ((n + 1) / 2)
  have hn : 0 < n := by dsimp [n]; positivity
  have hn1 : 1 ≤ n := by dsimp [n]; exact_mod_cast (show 1 ≤ r + 1 by omega)
  have hS : 1 ≤ S := by
    have hs0 := Real.sqrt_nonneg ((n + 1) / 2)
    have hs2 := Real.sq_sqrt (show 0 ≤ (n + 1) / 2 by positivity)
    change 1 ≤ Real.sqrt ((n + 1) / 2)
    nlinarith only [hs0, hs2, hn1]
  have hsmall : 1 / n ^ 2 ≤ S / n := by
    apply (div_le_iff₀ (sq_pos_of_pos hn)).mpr
    have hid : S / n * n ^ 2 = S * n := by field_simp
    rw [hid]
    have hp := mul_nonneg (sub_nonneg.mpr hS) hn.le
    nlinarith only [hp, hn1]
  have hwidth : ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((2 * (r + 1) ^ 2 + t + 2 : ℕ) : ℝ) := by
    push_cast
    have ht : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg _
    nlinarith only [ht, sq_nonneg ((r : ℝ) + 1)]
  have hH := finiteWeilCanonicalEdgeCenteredSecondMoment_quadratic_bound r t
  change finiteWeilCanonicalEdgeCenteredSecondMoment r (2 * (r + 1) ^ 2 + t) / n ^ 2 ≤ S / n at hH
  calc
    _ ≤ (4 * finiteWeilCanonicalEdgeCenteredSecondMoment r (2 * (r + 1) ^ 2 + t) + 4) / n ^ 2 :=
      finiteWeilCanonicalEdgeLogCorrectionSecondMoment_edge_bound r _ hwidth
    _ = 4 * (finiteWeilCanonicalEdgeCenteredSecondMoment r (2 * (r + 1) ^ 2 + t) / n ^ 2) +
        4 * (1 / n ^ 2) := by ring
    _ ≤ _ := by change _ ≤ 8 * (S / n); linarith only [hH, hsmall]

end RHTower
