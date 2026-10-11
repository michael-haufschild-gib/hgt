import GaloisForLFunctions.RHTower.WeilLogShiftDiagonalGaussian

/-! The diagonal is Lipschitz, and atom displacement is exactly normalized residual. -/

open MeasureTheory Filter Topology
open scoped BigOperators

noncomputable section
namespace RHTower

theorem finiteWeilCanonicalFluctuationPoint_fst_injective (r k : ℕ) :
    Function.Injective (fun i => finiteWeilCanonicalFluctuationPoint r k i 0) := by
  intro i j h
  have hs : Real.sqrt ((r + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt (by positivity)
  change ((((i : ℕ) : ℝ) - finiteWeilCanonicalEdgeIndexMean r k) / _) =
    ((((j : ℕ) : ℝ) - finiteWeilCanonicalEdgeIndexMean r k) / _) at h
  have hc := (div_left_inj' hs).mp h
  have he : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := by linarith only [hc]
  apply Fin.ext
  exact_mod_cast he

theorem finiteWeilDiagonalPoint_lipschitz : LipschitzWith 2 finiteWeilDiagonalPoint := by
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro x y
  calc
    _ = Real.sqrt (2 * |x - y| ^ 2) := by
      simp only [EuclideanSpace.dist_eq, Fin.sum_univ_two, finiteWeilDiagonalPoint,
        Matrix.cons_val_zero, Matrix.cons_val_one, Real.dist_eq]
      congr 1
      ring
    _ ≤ Real.sqrt ((2 * |x - y|) ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith only [sq_nonneg |x - y|])
    _ = _ := by rw [Real.sqrt_sq (by positivity), Real.dist_eq]; norm_num

theorem finiteWeilCanonicalFluctuationPoint_diagonal_dist (r k : ℕ) (i : Fin (r + 1)) :
    dist (finiteWeilCanonicalFluctuationPoint r k i)
      (finiteWeilDiagonalPoint (finiteWeilCanonicalFluctuationPoint r k i 0)) =
      |finiteWeilCanonicalFluctuationResidualValue r k i| / Real.sqrt ((r + 1 : ℕ) : ℝ) := by
  have hs : 0 < Real.sqrt ((r + 1 : ℕ) : ℝ) := by positivity
  let X := (((i : ℕ) : ℝ) - finiteWeilCanonicalEdgeIndexMean r k)
  let Y := ((r + 1 : ℕ) : ℝ) *
    (finiteWeilCanonicalEdgeLogCorrection r k i - finiteWeilCanonicalLogTransportCorrection r k)
  let s := Real.sqrt ((r + 1 : ℕ) : ℝ)
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  change Real.sqrt (dist (X / s) (X / s) ^ 2 + dist (Y / s) (X / s) ^ 2) = _
  rw [dist_self, show (0 : ℝ) ^ 2 = 0 by norm_num, zero_add, Real.sqrt_sq_eq_abs,
    abs_of_nonneg dist_nonneg, Real.dist_eq, ← sub_div, abs_div, abs_of_pos hs]
  rfl

def finiteWeilCanonicalJointDiagonalGap (r k : ℕ) : ℝ :=
  ∑ i, finiteWeilCanonicalEdgeMass r k i *
    dist (finiteWeilCanonicalFluctuationPoint r k i)
      (finiteWeilDiagonalPoint (finiteWeilCanonicalFluctuationPoint r k i 0))

theorem finiteWeilCanonicalJointDiagonalGap_nonneg (r k : ℕ) :
    0 ≤ finiteWeilCanonicalJointDiagonalGap r k :=
  Finset.sum_nonneg fun i _ => mul_nonneg (finiteWeilCanonicalEdgeMass_pos r k i).le dist_nonneg

theorem finiteWeilCanonicalJointDiagonalGap_quadratic_bound (r t : ℕ) :
    finiteWeilCanonicalJointDiagonalGap r (2 * (r + 1) ^ 2 + t) ≤
      (Real.sqrt ((r + 1 : ℕ) : ℝ))⁻¹ := by
  unfold finiteWeilCanonicalJointDiagonalGap
  simp_rw [finiteWeilCanonicalFluctuationPoint_diagonal_dist, ← mul_div_assoc]
  rw [← Finset.sum_div]
  have hw : ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((2 * (r + 1) ^ 2 + t + 2 : ℕ) : ℝ) := by
    push_cast
    nlinarith only [sq_nonneg ((r : ℝ) + 1), (Nat.cast_nonneg t : (0 : ℝ) ≤ t)]
  simpa only [one_div] using div_le_div_of_nonneg_right
    (finiteWeilCanonicalFluctuationResidual_first_moment_bound r _ hw) (Real.sqrt_nonneg _)

theorem tendsto_finiteWeilCanonicalJointDiagonalGap_zero (t : ℕ → ℕ) :
    Tendsto (fun r => finiteWeilCanonicalJointDiagonalGap r (2 * (r + 1) ^ 2 + t r))
      atTop (𝓝 0) :=
  squeeze_zero (fun r => finiteWeilCanonicalJointDiagonalGap_nonneg r _)
    (fun r => finiteWeilCanonicalJointDiagonalGap_quadratic_bound r (t r))
    tendsto_finiteWeil_inverse_sqrt_succ

end RHTower
