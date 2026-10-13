import GaloisForLFunctions.RHTower.WeilLogShiftPowerCovarianceKernel
import GaloisForLFunctions.RHTower.WeilLogShiftFinitePowerCovariance
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Exact rank and nullity of every finite Weil power covariance, at every depth and real tilt. -/

open MeasureTheory GaloisForLFunctions.HTGeometry
local notation "E" => EuclideanSpace ℝ (Fin 2)

namespace RHTower

theorem finiteWeilCanonicalJointQuadraticTilt_powerCovarianceMatrix_rank
    (r k : ℕ) (a b d : ℝ) (n : ℕ) :
    (powerCovarianceMatrix (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E)
      (fun z => z 0) n).rank = min n r := by
  let C := powerCovarianceMatrix
    (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E) (fun z => z 0) n
  let D := finitePowerDifferenceMatrix r n (fun i => finiteWeilCanonicalFluctuationPoint r k i 0)
  have hker : LinearMap.ker C.mulVecLin = LinearMap.ker D.mulVecLin :=
    finiteWeilCanonicalJointQuadraticTilt_powerCovarianceMatrix_ker_eq_difference r k a b d n
  have hc : C.rank + Module.finrank ℝ (LinearMap.ker C.mulVecLin) = n := by
    simpa [Matrix.rank] using C.mulVecLin.finrank_range_add_finrank_ker
  have hd : D.rank + Module.finrank ℝ (LinearMap.ker D.mulVecLin) = n := by
    simpa [Matrix.rank] using D.mulVecLin.finrank_range_add_finrank_ker
  have hsame : C.rank = D.rank := by
    rw [hker] at hc
    omega
  have hr : C.rank ≤ r := hsame.trans_le D.rank_le_height
  have hn : C.rank ≤ n := C.rank_le_width
  let m := min n r
  have hmn : m ≤ n := Nat.min_le_left n r
  have hmr : m ≤ r := Nat.min_le_right n r
  have hsmall : C.submatrix (Fin.castLE hmn) (Fin.castLE hmn) =
      powerCovarianceMatrix (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E)
        (fun z => z 0) m := rfl
  have hsmall_rank : (powerCovarianceMatrix
      (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E) (fun z => z 0) m).rank = m := by
    simpa using Matrix.rank_of_isUnit _
      (finiteWeilCanonicalJointQuadraticTilt_powerCovarianceMatrix_posDef_of_le r k a b d m hmr).isUnit
  have hlower := C.rank_submatrix_le (Fin.castLE hmn) (Fin.castLE hmn)
  rw [hsmall, hsmall_rank] at hlower
  change C.rank = min n r
  dsimp only [m] at hlower
  omega

theorem finiteWeilCanonicalJointQuadraticTilt_powerCovarianceMatrix_nullity
    (r k : ℕ) (a b d : ℝ) (n : ℕ) :
    Module.finrank ℝ (LinearMap.ker (powerCovarianceMatrix
      (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E)
      (fun z => z 0) n).mulVecLin) = n - r := by
  let C := powerCovarianceMatrix
    (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E) (fun z => z 0) n
  have h : C.rank + Module.finrank ℝ (LinearMap.ker C.mulVecLin) = n := by
    simpa [Matrix.rank] using C.mulVecLin.finrank_range_add_finrank_ker
  have hrank : C.rank = min n r :=
    finiteWeilCanonicalJointQuadraticTilt_powerCovarianceMatrix_rank r k a b d n
  rw [hrank] at h
  change Module.finrank ℝ (LinearMap.ker C.mulVecLin) = n - r
  omega

end RHTower
