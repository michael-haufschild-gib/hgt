import GaloisForLFunctions.RHTower.WeilLogShiftPowerCovarianceDeterminant

/-! # Explicit support factor in the finite power-covariance determinant -/

namespace RHTower

open MeasureTheory
open GaloisForLFunctions.HTGeometry
open scoped BigOperators

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- Squared first-coordinate gaps depend only on the finite index difference. -/
theorem finiteWeilCanonicalFluctuationPoint_fst_sub_sq
    (r k : ℕ) (i j : Fin (r + 1)) :
    (finiteWeilCanonicalFluctuationPoint r k j 0 -
      finiteWeilCanonicalFluctuationPoint r k i 0) ^ 2 =
      ((((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) ^ 2) / ((r + 1 : ℕ) : ℝ) := by
  change ((((j : ℕ) : ℝ) - finiteWeilCanonicalEdgeIndexMean r k) /
    Real.sqrt ((r + 1 : ℕ) : ℝ) -
    (((i : ℕ) : ℝ) - finiteWeilCanonicalEdgeIndexMean r k) /
    Real.sqrt ((r + 1 : ℕ) : ℝ)) ^ 2 = _
  rw [← sub_div, div_pow, Real.sq_sqrt (by positivity)]
  congr 2
  ring

/-- Depth and tilt enter the maximal covariance determinant only through atom weights. -/
theorem finiteWeilCanonicalJointQuadraticTilt_powerCovarianceMatrix_det_product
    (r k : ℕ) (a b d : ℝ) :
    (powerCovarianceMatrix (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E)
      (fun z : E => z 0) r).det =
    (∏ i : Fin (r + 1), ∏ j ∈ Finset.Ioi i,
      ((((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) ^ 2) / ((r + 1 : ℕ) : ℝ)) *
      ∏ i, finiteWeilCanonicalJointQuadraticTiltWeight r k a b d i := by
  rw [finiteWeilCanonicalJointQuadraticTilt_powerCovarianceMatrix_det_eq,
    Matrix.det_vandermonde]
  simp_rw [← Finset.prod_pow, finiteWeilCanonicalFluctuationPoint_fst_sub_sq]

end RHTower
