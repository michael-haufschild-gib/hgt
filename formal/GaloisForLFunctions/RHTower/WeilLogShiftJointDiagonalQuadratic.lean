import GaloisForLFunctions.RHTower.WeilLogShiftJointGaussianCost

/-! Exact diagonal quadratic geometry identifies the transverse residual contribution. -/

open MeasureTheory
open scoped BigOperators

noncomputable section
namespace RHTower

theorem finiteWeilDiagonalPoint_dist_sq (x y : ℝ) :
    dist (finiteWeilDiagonalPoint x) (finiteWeilDiagonalPoint y) ^ 2 = 2 * |x - y| ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
  change dist x y ^ 2 + dist x y ^ 2 = _
  rw [Real.dist_eq]
  ring

theorem finiteWeilCanonicalJointLiftDisplacement_sq_fst_integrable (r k : ℕ) :
    Integrable (fun z : ℝ × ℝ => finiteWeilCanonicalJointLiftDisplacement r k z.1 ^ 2)
      (finiteWeilCanonicalGaussianCoupling r k 1 0 : Measure (ℝ × ℝ)) := by
  have h : Integrable (fun x => finiteWeilCanonicalJointLiftDisplacement r k x ^ 2)
      ((finiteWeilCanonicalGaussianCoupling r k 1 0 : Measure (ℝ × ℝ)).map Prod.fst) := by
    rw [(finiteWeilCanonicalGaussianCoupling_isCoupling r k 1 0).1]
    exact finiteWeilCanonicalProjectedProbabilityLaw_integrable r k 1 0 _
  exact (integrable_map_measure
    ((finiteWeilCanonicalJointLiftDisplacement_measurable r k).pow_const (2 : ℕ)).aestronglyMeasurable
    measurable_fst.aemeasurable).mp h

theorem finiteWeilCanonicalJointLiftDisplacement_sq_fst_integral (r k : ℕ) :
    (∫ z, finiteWeilCanonicalJointLiftDisplacement r k z.1 ^ 2
      ∂(finiteWeilCanonicalGaussianCoupling r k 1 0 : Measure (ℝ × ℝ))) =
      finiteWeilCanonicalFluctuationResidual r k / ((r + 1 : ℕ) : ℝ) := by
  rw [← integral_map measurable_fst.aemeasurable
    ((finiteWeilCanonicalJointLiftDisplacement_measurable r k).pow_const (2 : ℕ)).aestronglyMeasurable,
    (finiteWeilCanonicalGaussianCoupling_isCoupling r k 1 0).1,
    finiteWeilCanonicalProjectedProbabilityLaw, finiteWeilCanonicalObservableLaw_integral_real]
  simp only [one_mul, zero_mul, add_zero]
  change (∑ i, finiteWeilCanonicalEdgeMass r k i *
    finiteWeilCanonicalJointLiftDisplacement r k (finiteWeilCanonicalFluctuationPoint r k i 0) ^ 2) = _
  simp_rw [finiteWeilCanonicalJointLiftDisplacement, finiteWeilCanonicalJointLift_at_atom,
    finiteWeilCanonicalFluctuationPoint_diagonal_dist, div_pow, sq_abs,
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ ((r + 1 : ℕ) : ℝ)), ← mul_div_assoc]
  rw [← Finset.sum_div]
  rfl

theorem finiteWeilCanonicalJointGaussianTransportMap_dist_sq_bound (r k : ℕ) (z : ℝ × ℝ) :
    dist (finiteWeilCanonicalJointLift r k z.1) (finiteWeilDiagonalPoint z.2) ^ 2 ≤
      2 * finiteWeilCanonicalJointLiftDisplacement r k z.1 ^ 2 + 4 * |z.1 - z.2| ^ 2 := by
  have ht := mul_self_le_mul_self dist_nonneg
    (dist_triangle (finiteWeilCanonicalJointLift r k z.1)
      (finiteWeilDiagonalPoint z.1) (finiteWeilDiagonalPoint z.2))
  have hs := sq_nonneg (dist (finiteWeilCanonicalJointLift r k z.1) (finiteWeilDiagonalPoint z.1) -
    dist (finiteWeilDiagonalPoint z.1) (finiteWeilDiagonalPoint z.2))
  have hd := finiteWeilDiagonalPoint_dist_sq z.1 z.2
  unfold finiteWeilCanonicalJointLiftDisplacement
  nlinarith only [ht, hs, hd]

end RHTower
