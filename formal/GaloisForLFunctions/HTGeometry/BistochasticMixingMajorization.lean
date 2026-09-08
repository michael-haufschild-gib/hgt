import GaloisForLFunctions.HTGeometry.TopSumMajorization
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Majorization and exact information loss under bistochastic mixing

The finite mixing argument in Sapienza, arXiv:2608.22463v1, Appendix A, applies
whenever a transition matrix is doubly stochastic. Here it acts on the corpus's
`topSum` statistic. The squared-norm loss is exactly a sum of conditional
variances, giving a support-wise equality classification as well as monotonicity.
-/

open scoped BigOperators NNReal
open Matrix
namespace GaloisForLFunctions.HTGeometry
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A bistochastic image is a convex combination of relabelings of its input. -/
theorem bistochasticMixing_permutation_decomposition
    (M : doublyStochastic ℝ ι) (x : ι → ℝ) :
    ∃ w : Equiv.Perm ι → ℝ, (∀ e, 0 ≤ w e) ∧ ∑ e, w e = 1 ∧
      (M.val *ᵥ x) = ∑ e, w e • (x ∘ e) := by
  obtain ⟨w, hw, hsum, hM⟩ := exists_eq_sum_perm_of_mem_doublyStochastic M.property
  refine ⟨w, hw, hsum, ?_⟩
  rw [← hM, Matrix.sum_mulVec]
  simp only [Matrix.smul_mulVec, Matrix.permMatrix_mulVec]

/-- Every sum of the largest `k` entries decreases under bistochastic mixing. -/
theorem bistochasticMixing_topSum_le {n : ℕ}
    (M : doublyStochastic ℝ (Fin n)) (x : Fin n → ℝ) (k : Fin (n + 1)) :
    topSum k.val (M.val *ᵥ x) ≤ topSum k.val x := by
  classical
  have hk : k.val ≤ n := Nat.le_of_lt_succ k.isLt
  obtain ⟨t, ht, htop⟩ := exists_sum_eq_topSum (M.val *ᵥ x) hk
  obtain ⟨w, hw, hsum, hM⟩ := bistochasticMixing_permutation_decomposition M x
  rw [← htop, hM]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  calc
    (∑ e : Equiv.Perm (Fin n), ∑ i ∈ t, w e * x (e i)) =
        ∑ e, w e * ∑ i ∈ t, x (e i) := by simp_rw [Finset.mul_sum]
    _ ≤ ∑ e, w e * topSum k.val x := by
      apply Finset.sum_le_sum
      intro e _
      apply mul_le_mul_of_nonneg_left _ (hw e)
      have himage : ∑ i ∈ t, x (e i) = ∑ j ∈ t.image e, x j :=
        (Finset.sum_image fun _ _ _ _ h => e.injective h).symm
      rw [himage]
      exact sum_le_topSum hk (by rw [Finset.card_image_of_injective _ e.injective, ht])
    _ = topSum k.val x := by rw [← Finset.sum_mul, hsum, one_mul]

/-- Shannon's entropy density increases for every nonnegative finite mass vector. -/
theorem bistochasticMixing_negMulLog_sum_le
    (M : doublyStochastic ℝ ι) (x : ι → ℝ≥0) :
    (∑ i, Real.negMulLog (x i)) ≤
      ∑ i, Real.negMulLog ((M.val *ᵥ fun j => (x j : ℝ)) i) := by
  have hrow (i : ι) := Real.concaveOn_negMulLog.le_map_sum
    (t := Finset.univ) (w := fun j => M.val i j) (p := fun j => (x j : ℝ))
    (fun j _ => M.property.1 i j) (sum_row_of_mem_doublyStochastic M.property i)
    (fun j _ => (x j).property)
  calc
    (∑ j, Real.negMulLog (x j)) = ∑ i, ∑ j, M.val i j * Real.negMulLog (x j) := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, sum_col_of_mem_doublyStochastic M.property, one_mul]
    _ ≤ _ := Finset.sum_le_sum fun i _ => by
      simpa only [smul_eq_mul, Matrix.mulVec, dotProduct] using hrow i

/-- Each row's centered second moment is its exact Jensen deficit. -/
theorem bistochasticMixing_row_variance
    (M : doublyStochastic ℝ ι) (x : ι → ℝ) (i : ι) :
    (∑ j, M.val i j * (x j - (M.val *ᵥ x) i) ^ 2) =
      (∑ j, M.val i j * x j ^ 2) - (M.val *ᵥ x) i ^ 2 := by
  have hexpand (j : ι) :
      M.val i j * (x j - (M.val *ᵥ x) i) ^ 2 =
        M.val i j * x j ^ 2 - 2 * (M.val *ᵥ x) i * (M.val i j * x j) +
          M.val i j * (M.val *ᵥ x) i ^ 2 := by ring
  simp_rw [hexpand, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul]
  rw [sum_row_of_mem_doublyStochastic M.property]
  change _ - 2 * (M.val *ᵥ x) i * (M.val *ᵥ x) i + 1 * _ = _
  ring

/-- Total squared-norm loss is the sum of conditional variances. -/
theorem bistochasticMixing_variance_identity
    (M : doublyStochastic ℝ ι) (x : ι → ℝ) :
    (∑ i, x i ^ 2) - (∑ i, (M.val *ᵥ x) i ^ 2) =
      ∑ i, ∑ j, M.val i j * (x j - (M.val *ᵥ x) i) ^ 2 := by
  simp_rw [bistochasticMixing_row_variance, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, sum_col_of_mem_doublyStochastic M.property, one_mul]

/-- Mixing cannot increase the squared Euclidean norm. -/
theorem bistochasticMixing_sum_sq_le
    (M : doublyStochastic ℝ ι) (x : ι → ℝ) :
    (∑ i, (M.val *ᵥ x) i ^ 2) ≤ ∑ i, x i ^ 2 := by
  apply sub_nonneg.mp
  rw [bistochasticMixing_variance_identity]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (M.property.1 i j) (sq_nonneg _)

/-- No norm is lost exactly when every occupied row sees a single input value. -/
theorem bistochasticMixing_sum_sq_eq_iff
    (M : doublyStochastic ℝ ι) (x : ι → ℝ) :
    (∑ i, (M.val *ᵥ x) i ^ 2) = (∑ i, x i ^ 2) ↔
      ∀ i j, M.val i j = 0 ∨ x j = (M.val *ᵥ x) i := by
  conv_lhs => rw [eq_comm]
  rw [← sub_eq_zero, bistochasticMixing_variance_identity]
  simp only [Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (M.property.1 i j) (sq_nonneg _)), Finset.mem_univ, forall_const]
  apply forall_congr'
  intro i
  rw [Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => mul_nonneg (M.property.1 i j) (sq_nonneg _))]
  simp only [Finset.mem_univ, forall_const, mul_eq_zero, sq_eq_zero_iff, sub_eq_zero]

/-- Total variation between two mass vectors contracts under the same mixing. -/
theorem bistochasticMixing_abs_sub_sum_le
    (M : doublyStochastic ℝ ι) (x y : ι → ℝ) :
    (∑ i, |(M.val *ᵥ x) i - (M.val *ᵥ y) i|) ≤ ∑ i, |x i - y i| := by
  calc
    _ = ∑ i, |∑ j, M.val i j * (x j - y j)| := by
      simp_rw [mul_sub, Finset.sum_sub_distrib]; rfl
    _ ≤ ∑ i, ∑ j, |M.val i j * (x j - y j)| := by
      exact Finset.sum_le_sum fun i _ => by
        simpa only [Real.norm_eq_abs] using norm_sum_le Finset.univ
          (fun j => M.val i j * (x j - y j))
    _ = ∑ j, |x j - y j| := by
      simp_rw [abs_mul, abs_of_nonneg (M.property.1 _ _)]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, sum_col_of_mem_doublyStochastic M.property, one_mul]

end
end GaloisForLFunctions.HTGeometry
