import GaloisForLFunctions.RHTower.WeilLogShiftJointTransportGeometry

/-! Every centered residual is uniformly bounded, independently of the finite atom. -/

open scoped BigOperators

noncomputable section
namespace RHTower

theorem finiteWeilCanonicalEdgeLogCorrection_scaled_index_quadratic_bound
    (r t : ℕ) (i : Fin (r + 1)) :
    |((r + 1 : ℕ) : ℝ) * finiteWeilCanonicalEdgeLogCorrection r (2 * (r + 1) ^ 2 + t) i -
      ((i : ℕ) : ℝ)| ≤ 1 := by
  apply finiteWeilCanonicalEdgeLogCorrection_scaled_index_bound
  push_cast
  nlinarith only [sq_nonneg ((r : ℝ) + 1), (Nat.cast_nonneg t : (0 : ℝ) ≤ t)]

theorem finiteWeilCanonicalScaledResidualMean_quadratic_bound (r t : ℕ) :
    |((r + 1 : ℕ) : ℝ) * finiteWeilCanonicalLogTransportCorrection r (2 * (r + 1) ^ 2 + t) -
      finiteWeilCanonicalEdgeIndexMean r (2 * (r + 1) ^ 2 + t)| ≤ 1 := by
  rw [← finiteWeilCanonicalEdgeLogCorrection_scaled_residual_mean]
  calc
    _ ≤ ∑ i : Fin (r + 1), |finiteWeilCanonicalEdgeMass r (2 * (r + 1) ^ 2 + t) i *
        (((r + 1 : ℕ) : ℝ) * finiteWeilCanonicalEdgeLogCorrection r (2 * (r + 1) ^ 2 + t) i -
          ((i : ℕ) : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r (2 * (r + 1) ^ 2 + t) i *
        |((r + 1 : ℕ) : ℝ) * finiteWeilCanonicalEdgeLogCorrection r (2 * (r + 1) ^ 2 + t) i -
          ((i : ℕ) : ℝ)| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_mul, abs_of_pos (finiteWeilCanonicalEdgeMass_pos r _ i)]
    _ ≤ ∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r (2 * (r + 1) ^ 2 + t) i * 1 :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
        (finiteWeilCanonicalEdgeLogCorrection_scaled_index_quadratic_bound r t i)
        (finiteWeilCanonicalEdgeMass_pos r _ i).le
    _ = 1 := by simp only [mul_one, finiteWeilCanonicalEdgeMass_sum]

theorem finiteWeilCanonicalFluctuationResidualValue_quadratic_bound
    (r t : ℕ) (i : Fin (r + 1)) :
    |finiteWeilCanonicalFluctuationResidualValue r (2 * (r + 1) ^ 2 + t) i| ≤ 2 := by
  let k := 2 * (r + 1) ^ 2 + t
  let u := ((r + 1 : ℕ) : ℝ) * finiteWeilCanonicalEdgeLogCorrection r k i - ((i : ℕ) : ℝ)
  let m := ((r + 1 : ℕ) : ℝ) * finiteWeilCanonicalLogTransportCorrection r k -
    finiteWeilCanonicalEdgeIndexMean r k
  have hu : |u| ≤ 1 := finiteWeilCanonicalEdgeLogCorrection_scaled_index_quadratic_bound r t i
  have hm : |m| ≤ 1 := finiteWeilCanonicalScaledResidualMean_quadratic_bound r t
  have he : finiteWeilCanonicalFluctuationResidualValue r k i = u + -m := by
    dsimp [finiteWeilCanonicalFluctuationResidualValue, u, m]
    ring
  change |finiteWeilCanonicalFluctuationResidualValue r k i| ≤ 2
  rw [he]
  have h := abs_add_le u (-m)
  rw [abs_neg] at h
  linarith only [hu, hm, h]

theorem finiteWeilCanonicalFluctuationPoint_diagonal_quadratic_bound
    (r t : ℕ) (i : Fin (r + 1)) :
    dist (finiteWeilCanonicalFluctuationPoint r (2 * (r + 1) ^ 2 + t) i)
      (finiteWeilDiagonalPoint (finiteWeilCanonicalFluctuationPoint r (2 * (r + 1) ^ 2 + t) i 0)) ≤
      2 / Real.sqrt ((r + 1 : ℕ) : ℝ) := by
  rw [finiteWeilCanonicalFluctuationPoint_diagonal_dist]
  exact div_le_div_of_nonneg_right (finiteWeilCanonicalFluctuationResidualValue_quadratic_bound r t i)
    (Real.sqrt_nonneg _)

end RHTower
