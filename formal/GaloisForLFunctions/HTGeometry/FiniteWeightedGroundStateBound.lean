import GaloisForLFunctions.HTGeometry.WeightedSchurTest

/-!
# Weighted Schur bounds with the row potential retained

The weighted arithmetic-geometric inequality bounds a symmetric nonnegative
kernel by its exact row potential. Keeping the row-dependent diagonal permits
subsequent control by a Dirichlet form instead of a scalar row maximum.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.HTGeometry

/-- Weighted Schur's inequality before replacing the row potential by a scalar. -/
theorem finite_weighted_schur_row_potential {ι : Type*} (S : Finset ι)
    (x w : ι → ℝ) (K : ι → ι → ℝ)
    (hw : ∀ i ∈ S, 0 < w i)
    (hK : ∀ i ∈ S, ∀ j ∈ S, 0 ≤ K i j)
    (hsym : ∀ i ∈ S, ∀ j ∈ S, K i j = K j i) :
    (∑ i ∈ S, ∑ j ∈ S, x i * x j * K i j) ≤
      ∑ i ∈ S, x i ^ 2 / w i * (∑ j ∈ S, K i j * w j) := by
  have hpair : ∀ i ∈ S, ∀ j ∈ S, x i * x j * K i j ≤
      (x i ^ 2 / w i * (K i j * w j) +
        x j ^ 2 / w j * (K j i * w i)) / 2 := by
    intro i hi j hj
    have hwi := hw i hi
    have hwj := hw j hj
    have heq : x i ^ 2 / w i * w j + x j ^ 2 / w j * w i - 2 * (x i * x j) =
        (x i * w j - x j * w i) ^ 2 / (w i * w j) := by
      field_simp [hwi.ne', hwj.ne']
      ring
    have hnonneg : 0 ≤ (x i * w j - x j * w i) ^ 2 / (w i * w j) := by positivity
    have hbase : 2 * (x i * x j) ≤ x i ^ 2 / w i * w j + x j ^ 2 / w j * w i := by
      linarith only [heq, hnonneg]
    have h := mul_le_mul_of_nonneg_right hbase (hK i hi j hj)
    rw [hsym j hj i hi]
    nlinarith only [h]
  have hswap :
      (∑ i ∈ S, ∑ j ∈ S, x j ^ 2 / w j * (K j i * w i)) =
        ∑ i ∈ S, ∑ j ∈ S, x i ^ 2 / w i * (K i j * w j) := sum_comm
  calc
    (∑ i ∈ S, ∑ j ∈ S, x i * x j * K i j) ≤
        ∑ i ∈ S, ∑ j ∈ S,
          (x i ^ 2 / w i * (K i j * w j) +
            x j ^ 2 / w j * (K j i * w i)) / 2 :=
      sum_le_sum fun i hi => sum_le_sum fun j hj => hpair i hi j hj
    _ = ∑ i ∈ S, x i ^ 2 / w i * (∑ j ∈ S, K i j * w j) := by
      simp only [← sum_div, sum_add_distrib, hswap, mul_sum]
      ring

end GaloisForLFunctions.HTGeometry

