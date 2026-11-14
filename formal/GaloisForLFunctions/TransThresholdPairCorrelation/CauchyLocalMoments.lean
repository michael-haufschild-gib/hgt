import GaloisForLFunctions.HTGeometry.IntegerSeriesBounds
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Uniform moments of discrete Cauchy correlations

The Cauchy kernel has a finite total mass on the integer lattice. Weighted
Jensen and symmetry transfer every local correlation moment to the next
occupancy moment, with a constant independent of the finite window.
-/

open scoped BigOperators
open Finset

namespace GaloisForLFunctions.TransThresholdPairCorrelation
noncomputable section

/-- Cauchy interaction between lattice cells. -/
def cellCauchy (j k : ℤ) : ℝ := 1 / (1 + ((j : ℝ) - k) ^ 2)

theorem cellCauchy_nonneg (j k : ℤ) : 0 ≤ cellCauchy j k := by
  unfold cellCauchy
  positivity

theorem cellCauchy_symm (j k : ℤ) : cellCauchy j k = cellCauchy k j := by
  simp only [cellCauchy, sq_sub_comm]

theorem summable_cellCauchy : Summable (fun j : ℤ => cellCauchy j 0) := by
  refine Summable.of_nonneg_of_le (fun j => cellCauchy_nonneg j 0) (fun j => ?_)
    (summable_one_div_one_add_abs_sq.mul_left 2)
  simp only [cellCauchy, Int.cast_zero, sub_zero]
  have hden : 0 < 1 + (j : ℝ) ^ 2 := by positivity
  have habs : 0 < (1 + |(j : ℝ)|) ^ 2 := by positivity
  rw [mul_div_assoc, div_le_div_iff₀ hden habs]
  nlinarith only [sq_nonneg (|(j : ℝ)| - 1), sq_abs (j : ℝ)]

/-- Total lattice mass; it pays every finite row uniformly. -/
def cellCauchyMass : ℝ := ∑' j : ℤ, cellCauchy j 0

theorem cellCauchyMass_nonneg : 0 ≤ cellCauchyMass :=
  tsum_nonneg fun j => cellCauchy_nonneg j 0

/-- Finite row sums are bounded independently of the window and the row. -/
theorem sum_cellCauchy_le (s : Finset ℤ) (j : ℤ) :
    (∑ k ∈ s, cellCauchy j k) ≤ cellCauchyMass := by
  have he : (∑ k ∈ s, cellCauchy j k) = ∑ m ∈ s.image (fun k => j - k), cellCauchy m 0 := by
    rw [sum_image]
    · apply sum_congr rfl
      intro k _
      simp only [cellCauchy, Int.cast_sub, Int.cast_zero, sub_zero]
    · intro a _ b _ h
      omega
  rw [he]
  exact summable_cellCauchy.sum_le_tsum _ (fun i _ => cellCauchy_nonneg i 0)

/-- Local occupancy averaged with the Cauchy kernel. -/
def cellCauchyDensity (s : Finset ℤ) (n : ℤ → ℝ≥0) (j : ℤ) : ℝ :=
  ∑ k ∈ s, cellCauchy j k * (n k : ℝ)

private theorem weighted_power {ι : Type*} (s : Finset ι) (w a : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (ha : ∀ i ∈ s, 0 ≤ a i) (q : ℕ) :
    (∑ i ∈ s, w i * a i) ^ (q + 1) ≤
      (∑ i ∈ s, w i) ^ q * ∑ i ∈ s, w i * a i ^ (q + 1) := by
  let W := ∑ i ∈ s, w i
  have hW : 0 ≤ W := sum_nonneg hw
  by_cases hz : W = 0
  · have hwz (i) (hi : i ∈ s) : w i = 0 := by
      have hh := single_le_sum hw hi
      change w i ≤ W at hh
      exact le_antisymm (hz ▸ hh) (hw i hi)
    simp only [hwz, mul_zero, zero_mul, sum_const_zero, zero_pow (Nat.succ_ne_zero q)]
    positivity
  · have hp : 0 < W := lt_of_le_of_ne hW (Ne.symm hz)
    have hn : ∑ i ∈ s, w i / W = 1 := by rw [← sum_div]; exact div_self hz
    have h := Real.pow_arith_mean_le_arith_mean_pow s (fun i => w i / W) a
      (fun i hi => div_nonneg (hw i hi) hW) hn ha (q + 1)
    have he : (∑ i ∈ s, w i / W * a i) = (∑ i ∈ s, w i * a i) / W := by
      rw [sum_div]
      exact sum_congr rfl fun _ _ => by ring
    have he' : (∑ i ∈ s, w i / W * a i ^ (q + 1)) =
        (∑ i ∈ s, w i * a i ^ (q + 1)) / W := by
      rw [sum_div]
      exact sum_congr rfl fun _ _ => by ring
    rw [he, he', div_pow, div_le_div_iff₀ (pow_pos hp _) hp] at h
    rw [pow_succ] at h
    have hh : (∑ i ∈ s, w i * a i) ^ (q + 1) * W ≤
        (W ^ q * ∑ i ∈ s, w i * a i ^ (q + 1)) * W := by nlinarith only [h]
    exact (mul_le_mul_iff_left₀ hp).mp hh

private theorem mixed_power (a b : ℝ≥0) (q : ℕ) :
    (a : ℝ) * (b : ℝ) ^ (q + 1) ≤ (a : ℝ) ^ (q + 2) + (b : ℝ) ^ (q + 2) := by
  rcases le_total (a : ℝ) (b : ℝ) with h | h
  · have hh := mul_le_mul_of_nonneg_right h (pow_nonneg b.coe_nonneg (q + 1))
    have he : (b : ℝ) * (b : ℝ) ^ (q + 1) = (b : ℝ) ^ (q + 2) := by rw [pow_succ]; ring
    rw [he] at hh
    exact hh.trans (le_add_of_nonneg_left (pow_nonneg a.coe_nonneg _))
  · have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ b.coe_nonneg h (q + 1)) a.coe_nonneg
    have he : (a : ℝ) * (a : ℝ) ^ (q + 1) = (a : ℝ) ^ (q + 2) := by rw [pow_succ]; ring
    rw [he] at hh
    exact hh.trans (le_add_of_nonneg_right (pow_nonneg b.coe_nonneg _))

/-- Every local moment is paid by the next occupancy moment, uniformly in the window. -/
theorem cellCauchy_moment_le (s : Finset ℤ) (n : ℤ → ℝ≥0) (q : ℕ) :
    (∑ j ∈ s, (n j : ℝ) * cellCauchyDensity s n j ^ (q + 1)) ≤
      2 * cellCauchyMass ^ (q + 1) * ∑ j ∈ s, (n j : ℝ) ^ (q + 2) := by
  have hrow (j : ℤ) : cellCauchyDensity s n j ^ (q + 1) ≤
      cellCauchyMass ^ q * ∑ k ∈ s, cellCauchy j k * (n k : ℝ) ^ (q + 1) := by
    exact (weighted_power s (cellCauchy j) (fun k => (n k : ℝ))
      (fun k _ => cellCauchy_nonneg j k) (fun k _ => (n k).coe_nonneg) q).trans
      (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (sum_nonneg fun k _ => cellCauchy_nonneg j k)
          (sum_cellCauchy_le s j) q)
        (sum_nonneg fun k _ => mul_nonneg (cellCauchy_nonneg j k) (pow_nonneg (n k).coe_nonneg _)))
  have hpair : (∑ j ∈ s, ∑ k ∈ s, cellCauchy j k * ((n j : ℝ) * (n k : ℝ) ^ (q + 1))) ≤
      2 * cellCauchyMass * ∑ j ∈ s, (n j : ℝ) ^ (q + 2) := by
    calc
      _ ≤ ∑ j ∈ s, ∑ k ∈ s, cellCauchy j k *
          ((n j : ℝ) ^ (q + 2) + (n k : ℝ) ^ (q + 2)) :=
        sum_le_sum fun j _ => sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_left (mixed_power (n j) (n k) q) (cellCauchy_nonneg j k)
      _ = 2 * ∑ j ∈ s, (n j : ℝ) ^ (q + 2) * ∑ k ∈ s, cellCauchy j k := by
        simp only [mul_add, sum_add_distrib]
        rw [sum_comm (f := fun j k => cellCauchy j k * (n k : ℝ) ^ (q + 2))]
        simp_rw [cellCauchy_symm, mul_comm (cellCauchy _ _), ← mul_sum]
        ring
      _ ≤ 2 * ∑ j ∈ s, (n j : ℝ) ^ (q + 2) * cellCauchyMass := by
        gcongr with j hj
        exact sum_cellCauchy_le s j
      _ = _ := by rw [← sum_mul]; ring
  calc
    _ ≤ ∑ j ∈ s, (n j : ℝ) * (cellCauchyMass ^ q *
        ∑ k ∈ s, cellCauchy j k * (n k : ℝ) ^ (q + 1)) :=
      sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hrow j) (n j).coe_nonneg
    _ = cellCauchyMass ^ q * ∑ j ∈ s, ∑ k ∈ s,
        cellCauchy j k * ((n j : ℝ) * (n k : ℝ) ^ (q + 1)) := by
      simp only [mul_sum]
      apply sum_congr rfl
      intro j _
      exact sum_congr rfl fun k _ => by ring
    _ ≤ cellCauchyMass ^ q * (2 * cellCauchyMass * ∑ j ∈ s, (n j : ℝ) ^ (q + 2)) :=
      mul_le_mul_of_nonneg_left hpair (pow_nonneg cellCauchyMass_nonneg _)
    _ = _ := by rw [pow_succ]; ring

end
end GaloisForLFunctions.TransThresholdPairCorrelation

#print axioms GaloisForLFunctions.TransThresholdPairCorrelation.cellCauchy_moment_le
